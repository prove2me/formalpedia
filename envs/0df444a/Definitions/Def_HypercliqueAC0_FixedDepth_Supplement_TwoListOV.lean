-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_TwoListOV
-- name    : HypercliqueAC0_FixedDepth_Supplement_TwoListOV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:40.840019+00:00
-- url     : https://prove2.me/theorems/0e9b4f47-ec82-4f5a-81ac-886a1f8b17fa
-- title:
--   Two-list Orthogonal Vectors with lists of lengths $n_1,n_2$, and its subfunctions on one vector
-- statement:
--   Fix natural numbers $n_1,n_2,d$. An instance consists of a first list $a_1,\dots,a_{n_1}$ and a second list $b_1,\dots,b_{n_2}$ of vectors in $\{0,1\}^d$, one Boolean variable per coordinate of each vector. Two-list Orthogonal Vectors is
--
--   $$2\text{-}\mathsf{OV}_{n_1,n_2,d}(a,b)=1\iff \exists i\in[n_1],\ \exists j\in[n_2],\ \forall q\in[d]:\ a_i[q]\wedge b_j[q]=0 .$$
--
--   For a function $f$ of these variables and a vector $i$ of the first list, a **subfunction of $f$ on vector $i$** is the function $z\mapsto f(a_i:=z,\ y)$ of $z\in\{0,1\}^d$ obtained by fixing every other variable to a constant $y$. The definition records the set of distinct such functions, as $y$ ranges over all assignments to the other variables.
--
--   These objects let one count the subfunctions of two-list $\mathsf{OV}$ on one vector, which feeds Nechiporuk's formula lower bound in the depth-three wire bound.
--
--   **Formalization Note** The variables are indexed by $([n_1]\times[d])\sqcup([n_2]\times[d])$ with $[n]$ represented by `Fin n`. The set of subfunctions is the image of all full assignments $y$ under $y\mapsto(z\mapsto f(\text{$y$ with vector $i$ replaced by $z$}))$; the values of $y$ on vector $i$ are overwritten, so this is exactly the set of functions obtained by fixing the other variables. Lists of unequal lengths are allowed, unlike the published `ErrAmpOV.kOV`.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.24 (PDF p.26), Lemma 8.1 (two-list OV with lengths n_1, n_2); p.10 (PDF p.12), §3.1 (k-OV) and §3 (subfunctions)

import Mathlib

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The variables of two-list Orthogonal Vectors: coordinate `q` of vector `i` of the first list
is `.inl (i, q)`, coordinate `q` of vector `j` of the second list is `.inr (j, q)`. -/
abbrev TwoListVar (n₁ n₂ d : ℕ) := (Fin n₁ × Fin d) ⊕ (Fin n₂ × Fin d)

/-- Two-list `2-OV` with list lengths `n₁, n₂` (Lemma 8.1, p. 24, PDF 26; §3.1, p. 10, PDF 12):
one iff some vector of the first list and some vector of the second list are orthogonal, i.e.
have no coordinate where both are one. -/
def twoListOV (n₁ n₂ d : ℕ) (x : TwoListVar n₁ n₂ d → Bool) : Bool :=
  decide (∃ i : Fin n₁, ∃ j : Fin n₂, ∀ q : Fin d,
    x (.inl (i, q)) = false ∨ x (.inr (j, q)) = false)

/-- The assignment that agrees with `y` everywhere except on vector `i` of the first list, which
is set to `z`. -/
def setFirstVector {n₁ n₂ d : ℕ} (i : Fin n₁) (y : TwoListVar n₁ n₂ d → Bool)
    (z : Fin d → Bool) : TwoListVar n₁ n₂ d → Bool
  | .inl (i', q) => if i' = i then z q else y (.inl (i', q))
  | .inr v => y (.inr v)

/-- The subfunctions of `f` on vector `i` of the first list (§3.1, p. 10, PDF 12: fix every
variable outside the vector to a constant): the set of distinct functions
`z ↦ f (z on vector i, y elsewhere)` as `y` ranges over all assignments. The values of `y` on
vector `i` itself are overwritten, so `y` effectively ranges over the assignments to the other
variables. -/
def subfunctionsOnFirstVector {n₁ n₂ d : ℕ} (f : (TwoListVar n₁ n₂ d → Bool) → Bool)
    (i : Fin n₁) : Finset ((Fin d → Bool) → Bool) :=
  Finset.univ.image (fun y => fun z => f (setFirstVector i y z))

end HypercliqueAC0.FixedDepth.Supplement


