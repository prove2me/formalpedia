-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Formula
-- name    : MTWalkSAT3CNF_TwoOcc_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:50.48508+00:00
-- url     : https://prove2.me/theorems/16e0f747-841f-438a-9742-ca674c1e76c2
-- title:
--   Indexed 3-CNF formulas, occurrence counts $\Delta(x,F)$ and $\mathrm{Bad}_F(\sigma)$
-- statement:
--   Let $V$ be a finite set of Boolean variables. A **3-clause** consists of three literal occurrences, at positions $p\in\{0,1,2\}$, on three pairwise distinct variables; the occurrence at position $p$ is the variable $\mathrm{var}(C,p)$ with a sign (positive literal $x$ or negative literal $\neg x$). A **3-CNF formula** with $m$ clauses is an indexed family $F=(C_1,\dots,C_m)$: repeated clauses are separate indices, and $m=0$ is allowed. Variables of $V$ need not occur in $F$.
--
--   For an assignment $\sigma\in\{0,1\}^V$ the occurrence at position $p$ of $C$ is true when $\sigma(\mathrm{var}(C,p))$ equals its sign. Write $s(C)$ for the number of true occurrences of $C$, and
--
--   $$\mathrm{Bad}_F(\sigma)=\{i : \text{all three occurrences of } C_i \text{ are false under } \sigma\}.$$
--
--   For a variable $x$, $\Delta(x,F)$ is the number of pairs $(i,p)$ with $\mathrm{var}(C_i,p)=x$ (positive and negative occurrences together), and $\Delta(F)\le 2$ means $\Delta(x,F)\le 2$ for every $x$. The number of variables occurring in $F$ is $n=\#\{x:\Delta(x,F)\ge 1\}$. The definition also fixes the flip of one variable, the **opposite-sign case** (two distinct occurrences of one variable always have opposite signs) and the predicate "$x$ has two same-sign occurrences".
--
--   These are the objects all statements of the mission are about.
--
--   **Formalization Note** Positions are `Fin 3`, clause indices `Fin m`, signs `Bool` (`true` = positive literal); `var_inj` enforces three distinct variables per clause. $\Delta(F)\le2$ is stated pointwise, which avoids a maximum over a possibly empty type.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §1.1, p. 5; §2.1, p. 9; §3.2, pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Mathlib

set_option autoImplicit false

/-!
# Indexed 3-CNF formulas, occurrence counts and unsatisfied clauses

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), §1.1 (p. 5) and §2.1 (p. 9).

Conventions (standing assumptions of the paper).
* A clause is an ordered triple of literal occurrences, at positions `Fin 3`, on three
  pairwise distinct variables (`var_inj`). A literal occurrence is a variable with a sign:
  `sign p = true` is the positive literal `x`, `sign p = false` the negative literal `¬x`.
* A formula with `m` clauses is an indexed family `Fin m → Clause V`: repeated clauses are
  separate indices, and `m = 0` is allowed. The variable type `V` may contain variables that do
  not occur in the formula.
* An assignment is `σ : V → Bool`; the occurrence at position `p` of `C` is true under `σ`
  exactly when `σ (C.var p) = C.sign p`.
-/

namespace MTWalkSAT3CNF.TwoOcc

/-- A 3-clause: three literal occurrences (positions `0, 1, 2`) on pairwise distinct variables.
`sign p = true` means the occurrence at position `p` is the positive literal. -/
structure Clause (V : Type*) where
  /-- the variable underlying the occurrence at each position -/
  var : Fin 3 → V
  /-- the sign of the occurrence at each position (`true` = positive literal) -/
  sign : Fin 3 → Bool
  /-- the three variables of a clause are distinct -/
  var_inj : Function.Injective var

/-- An indexed 3-CNF formula `F = (C_1, …, C_m)` over the variables `V`. -/
abbrev Formula (V : Type*) (m : ℕ) := Fin m → Clause V

variable {V : Type*} {m : ℕ}

/-- The literal occurrence at position `p` of clause `C` is true under `σ`. -/
def LitTrue (σ : V → Bool) (C : Clause V) (p : Fin 3) : Prop :=
  σ (C.var p) = C.sign p

instance (σ : V → Bool) (C : Clause V) (p : Fin 3) : Decidable (LitTrue σ C p) :=
  inferInstanceAs (Decidable (σ (C.var p) = C.sign p))

/-- `s(C)`: the number of true literal occurrences of `C` under `σ`. -/
def numTrue (σ : V → Bool) (C : Clause V) : ℕ :=
  (Finset.univ.filter (fun p : Fin 3 => LitTrue σ C p)).card

/-- `Bad_F(σ)`: the indices of the clauses falsified by `σ` (all three occurrences false). -/
def bad (F : Formula V m) (σ : V → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∀ p : Fin 3, ¬ LitTrue σ (F i) p)

/-- `Δ(x, F)`: the number of literal occurrences (positive and negative together) of the
variable `x` in `F`, i.e. the number of pairs `(i, p)` with `var(C_i, p) = x`. -/
def occCount [DecidableEq V] (F : Formula V m) (x : V) : ℕ :=
  (Finset.univ.filter (fun ip : Fin m × Fin 3 => (F ip.1).var ip.2 = x)).card

/-- `Δ(F) ≤ 2`, stated pointwise: every variable occurs at most twice. This is equivalent to
`max_x Δ(x, F) ≤ 2` and needs no maximum over a possibly empty variable type. -/
def MaxOccLeTwo [DecidableEq V] (F : Formula V m) : Prop :=
  ∀ x : V, occCount F x ≤ 2

/-- `n`: the number of variables occurring in `F`. -/
def numOccVars [Fintype V] [DecidableEq V] (F : Formula V m) : ℕ :=
  (Finset.univ.filter (fun x : V => 0 < occCount F x)).card

/-- Flip the value of the variable `x`. -/
def flip [DecidableEq V] (σ : V → Bool) (x : V) : V → Bool :=
  Function.update σ x (!σ x)

/-- Every variable occurring twice has one positive and one negative occurrence: two distinct
occurrences of the same variable have opposite signs (§3.2, p. 13, first case of the proof of
Theorem 3.4). -/
def OppositeSign (F : Formula V m) : Prop :=
  ∀ (i j : Fin m) (p q : Fin 3), (i, p) ≠ (j, q) → (F i).var p = (F j).var q →
    (F i).sign p ≠ (F j).sign q

/-- The variable `x` has two distinct occurrences with the same sign (Proposition 3.3, p. 12). -/
def SameSign (F : Formula V m) (x : V) : Prop :=
  ∃ (i j : Fin m) (p q : Fin 3), (i, p) ≠ (j, q) ∧ (F i).var p = x ∧ (F j).var q = x ∧
    (F i).sign p = (F j).sign q

instance [DecidableEq V] (F : Formula V m) (x : V) : Decidable (SameSign F x) := by
  unfold SameSign; infer_instance

end MTWalkSAT3CNF.TwoOcc


