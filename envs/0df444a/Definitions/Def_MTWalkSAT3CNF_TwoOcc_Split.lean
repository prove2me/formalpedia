-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Split
-- name    : MTWalkSAT3CNF_TwoOcc_Split
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:07.469024+00:00
-- url     : https://prove2.me/theorems/8ad74bba-d27c-4f86-889f-9da14095adfd
-- title:
--   Same-sign splitting $F\mapsto F^\sharp$ and the induced initial assignment
-- statement:
--   Let $S$ be the set of variables of $F$ with two same-sign occurrences. For each $x\in S$ introduce fresh variables $x^{(1)},x^{(2)}$ and replace the two literal occurrences of $x$ by
--
--   $$(x,x)\mapsto(x^{(1)},x^{(2)}),\qquad (\neg x,\neg x)\mapsto(\neg x^{(1)},\neg x^{(2)}),$$
--
--   the first occurrence (in the order of clause index, then position) becoming $x^{(1)}$. All other literals are unchanged; the result $F^\sharp$ has the same $m$ clause indices and the same signs. Given $X_0\in\{0,1\}^V$, the initial assignment $Y_0$ of $F^\sharp$ is
--
--   $$Y_0(x^{(1)})=Y_0(x^{(2)})=X_0(x)\ (x\in S),\qquad Y_0(z)=X_0(z)\ (z\in V\setminus S).$$
--
--   **Formalization Note** The variables of $F^\sharp$ are $\{z\in V: z\notin S\}\sqcup(S\times\{0,1\})$, and a map `orig` sends each new variable to the variable of $V$ it comes from; $Y_0=X_0\circ\mathrm{orig}$. The clauses of $F^\sharp$ still have three distinct variables.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Proposition 3.3, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Formula

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Same-sign splitting `F ↦ F♯`

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), Proposition 3.3 (p. 12).

Let `S` be the set of variables with two same-sign occurrences. Each `x ∈ S` is replaced by two
fresh variables `x^(1)`, `x^(2)`: the first occurrence of `x` (in the order of `(i, p)`, clause
index first) becomes `x^(1)` and the second becomes `x^(2)`, keeping its sign. All other
literals are unchanged.

Conventions.
* The variables of `F♯` are `SplitVar F = {z // z ∉ S} ⊕ (S × Fin 2)`; `inr (x, 0)` is `x^(1)`,
  `inr (x, 1)` is `x^(2)`, and `orig` maps every new variable back to the variable of `V` it
  comes from.
* `F♯` has the same clause indices `Fin m` and the same signs at every position.
* `Y_0 = splitInit F X_0`: `Y_0(x^(1)) = Y_0(x^(2)) = X_0(x)` for `x ∈ S`, `Y_0(z) = X_0(z)`
  otherwise.
-/

namespace MTWalkSAT3CNF.TwoOcc

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The variables of `F♯`: the variables without two same-sign occurrences, and two fresh copies
of each variable with two same-sign occurrences. -/
abbrev SplitVar (F : Formula V m) : Type _ :=
  {x : V // ¬ SameSign F x} ⊕ ({x : V // SameSign F x} × Fin 2)

/-- The variable of `V` a variable of `F♯` comes from. -/
def SplitVar.orig {F : Formula V m} : SplitVar F → V
  | Sum.inl z => z.1
  | Sum.inr (x, _) => x.1

/-- `0` for the first occurrence of the variable at `(i, p)` (no occurrence of the same variable
at an earlier position in the order `3·j + q`), `1` otherwise. -/
def occRank (F : Formula V m) (i : Fin m) (p : Fin 3) : Fin 2 :=
  if ∃ (j : Fin m) (q : Fin 3), j.val * 3 + q.val < i.val * 3 + p.val ∧ (F j).var q = (F i).var p
  then 1 else 0

/-- The variable of `F♯` at position `p` of clause `i`. -/
def splitVarAt (F : Formula V m) (i : Fin m) (p : Fin 3) : SplitVar F :=
  if hx : SameSign F ((F i).var p) then Sum.inr (⟨(F i).var p, hx⟩, occRank F i p)
  else Sum.inl ⟨(F i).var p, hx⟩

lemma orig_splitVarAt (F : Formula V m) (i : Fin m) (p : Fin 3) :
    (splitVarAt F i p).orig = (F i).var p := by
  unfold splitVarAt
  split_ifs <;> rfl

/-- The split formula `F♯`. -/
def splitFormula (F : Formula V m) : Formula (SplitVar F) m := fun i =>
  { var := splitVarAt F i
    sign := (F i).sign
    var_inj := fun p q h => (F i).var_inj (by
      rw [← orig_splitVarAt F i p, ← orig_splitVarAt F i q, h]) }

/-- The initial assignment `Y_0` of `F♯` induced by `X_0`. -/
def splitInit (F : Formula V m) (X₀ : V → Bool) : SplitVar F → Bool := fun z => X₀ z.orig

end MTWalkSAT3CNF.TwoOcc


