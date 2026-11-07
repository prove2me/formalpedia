-- Prove2me | Definitions.Def_CoDecompFO_Codes
-- name    : CoDecompFO_Codes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:42.677416+00:00
-- url     : https://prove2.me/theorems/35596dbd-6cc7-4541-8515-42f57a4285f2
-- title:
--   Codes of formulas and co-decompositions, and $|\varphi|$
-- statement:
--   The code of a formula is a prefix code in natural numbers: $0$ for $\bot$, then $1,t_1,t_2$ for $t_1=t_2$, then $2,i,t_1,\dots,t_a$ for $R_i(t_1,\dots,t_a)$, then $3$ followed by the codes of $f$ and $g$ for $f\to g$, and $4$ followed by the code of $f$ for $\forall f$. A variable is written as its de Bruijn level. The length $|\varphi|$ is the length of this code.
--
--   The code of a finite structure lists its number of points and a bit table for each relation. The code of a co-decomposition lists $b$, the number of edges, the edges, the codes of the bags and of the adhesions, and the maps as value lists. The input of the main theorem is the length of the code of $\varphi$, that code, and the code of $\mathcal T$; the limit is not part of it.
--
--   **Formalization Note** The paper fixes no code. For a fixed signature, a bit table has length bounded by a function of the width, so a list of tuples would change only the function $f$. Bit tables are ordered through `finFunctionFinEquiv`, and the membership bits are classical. Variable levels are bounded by the binder depth, so entries and length are bounded together.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 1.16, p.4; ¶3.1, p.8 (codes not fixed by the paper)

import Mathlib
import Definitions.Def_CoDecompFO_CoDecomp

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

variable {σ : Sig}

/-- The code of a term: a term of a relational language is a variable, and `Sentence`'s bound variables
are de Bruijn levels below the binder depth. -/
def encTerm {n : ℕ} : σ.lang.Term (Empty ⊕ Fin n) → ℕ
  | .var (.inl e) => e.elim
  | .var (.inr k) => k.val
  | .func f _ => nomatch (show Empty from f)

/-- The prefix code of a formula: `0` for `⊥`, `1 t₁ t₂` for `t₁ = t₂`, `2 i t₁ … t_a` for
`R_i(t₁, …, t_a)`, `3 f g` for `f → g`, `4 f` for `∀ f`. Mathlib's other connectives are abbreviations
for these. -/
def encF : {n : ℕ} → σ.lang.BoundedFormula Empty n → List ℕ
  | _, .falsum => [0]
  | _, .equal t₁ t₂ => [1, encTerm t₁, encTerm t₂]
  | _, .rel R ts => 2 :: R.1.val :: List.ofFn (fun j => encTerm (ts j))
  | _, .imp f g => 3 :: (encF f ++ encF g)
  | _, .all f => 4 :: encF f

/-- The length `|φ|` of a formula (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…,
Theorem 1.16, p.4), as the length of its code.

**Formalization Note** The paper does not define `|φ|`. Bound variables are levels below the binder
depth, so entries and length are bounded together and no long name can hide in a short formula. -/
def sentLen {n : ℕ} (φ : σ.lang.BoundedFormula Empty n) : ℕ := (encF φ).length

open Classical in
/-- The code of a finite structure: `n`, then for each symbol `i` in turn the bit table of its relation
over `(Fin n)^{ar(i)}`, in the order of `finFunctionFinEquiv`. -/
noncomputable def encBag (B : Bag σ) : List ℕ :=
  B.n :: (List.finRange σ.r).flatMap (fun i =>
    List.ofFn (fun k : Fin (B.n ^ σ.ar i) =>
      if B.rel i (finFunctionFinEquiv.symm k) then 1 else 0))

/-- The code of a tree co-decomposition: `b`, `m`, the edge list, the bags, the adhesions, and the maps
as value lists. The limit is not part of the code (¶3.1, p.8: "when we are given a tree co-decomposition
T, we are not also given its limit").

**Formalization Note** The paper fixes no code (`paper.md` decision 9). For a fixed `σ` a bit table has
length bounded by a function of the width, so a tuple-list input differs only in `f`. -/
noncomputable def encCoDecomp (T : CoDecomp σ) : List ℕ :=
  T.b :: T.m ::
    ((List.finRange T.m).flatMap (fun e => [(T.ends e).1.val, (T.ends e).2.val]) ++
      (List.finRange T.b).flatMap (fun t => encBag (T.bag t)) ++
      (List.finRange T.m).flatMap (fun e => encBag (T.adh e)) ++
      (List.finRange T.m).flatMap (fun e =>
        List.ofFn (fun x => (T.gl e x).val) ++ List.ofFn (fun x => (T.gr e x).val)))

/-- The input to the algorithm of Theorem 1.16: the length of `φ`'s code, that code, and the code of
`T`. -/
noncomputable def input (φ : σ.lang.Sentence) (T : CoDecomp σ) : List ℕ :=
  (encF φ).length :: (encF φ ++ encCoDecomp T)

end CoDecompFO


