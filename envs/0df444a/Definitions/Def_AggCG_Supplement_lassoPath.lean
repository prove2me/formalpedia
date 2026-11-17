-- Prove2me | Definitions.Def_AggCG_Supplement_lassoPath
-- name    : AggCG_Supplement_lassoPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:21:10.533755+00:00
-- url     : https://prove2.me/theorems/a70d389a-5582-4d4b-a2ee-6a86d47ee55b
-- title:
--   Lasso path, kinks, and path segments
-- statement:
--   The Lasso path selects the unique minimizer of
--   $$
--   \tfrac12\lVert Xw-y\rVert_2^2+\lambda\lVert w\rVert_1,
--   $$
--   and its sign-pattern and nondegenerate affine segments are the maximal positive-parameter intervals on which the corresponding sign vector or affine formula remains fixed. The Mairal–Yu matrix is the upper-triangular rational design used by Theorem 4.3.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), eq. (1), Theorem 4.3, p.5, PDF p.6; Theorem 5.9, p.10, PDF p.11

import Mathlib

namespace AggCG.Supplement

open Matrix

variable {n p : ℕ}

/-- The Lasso objective `½‖Xw − y‖₂² + λ‖w‖₁` (Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), eq. (1), p.5, PDF p.6). -/
noncomputable def lassoObj (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ((X *ᵥ w) i - y i) ^ 2 + lam * ∑ j, |w j|

/-- `w` minimizes the Lasso objective at `λ`. -/
def IsLassoSol (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ) (w : Fin p → ℝ) : Prop :=
  ∀ w', lassoObj X y lam w ≤ lassoObj X y lam w'

/-- The Lasso path `λ ↦ ŵ(λ)` of (1): the unique minimizer at `λ` when there is exactly one.

**Formalization Note** The minimizer is unique for every `λ > 0` when `X` has full column rank (p.5:
"unique when X has full column rank"; every use has this or has it almost surely). Where it is not unique
the value is `0`, which only matters on a null event in Theorem 5.9. -/
noncomputable def lassoPath (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ) : Fin p → ℝ :=
  open Classical in
  if h : ∃! w, IsLassoSol X y lam w then h.exists.choose else 0

/-- A positive **kink** of a path `w : ℝ → ℝ^p` at `λ > 0`: `w` is affine on no open interval around
`λ` (p.5, Theorem 4.3: "positive Lasso kink"). -/
def IsKink (w : ℝ → (Fin p → ℝ)) (lam : ℝ) : Prop :=
  0 < lam ∧ ¬ ∃ ε > 0, ∃ u v : Fin p → ℝ, ∀ l, |l - lam| < ε → w l = u + l • v

/-- A **sign-pattern segment** of a path (Theorem 4.3, p.5): a maximal nonempty interval of positive
regularization parameters on which the sign vector `sign(w(λ)) ∈ {−1, 0, 1}^p` is constant.

**Formalization Note** Every maximal interval of constant sign pattern counts, including one reduced to a
single parameter value; the all-zero pattern of large `λ` is a segment like any other. -/
def IsSignSegment (w : ℝ → (Fin p → ℝ)) (I : Set ℝ) : Prop :=
  (I ⊆ Set.Ioi 0 ∧ I.Nonempty ∧ I.OrdConnected ∧
      ∀ l ∈ I, ∀ l' ∈ I, (fun j => SignType.sign (w l j)) = fun j => SignType.sign (w l' j)) ∧
    ∀ J : Set ℝ, I ⊆ J → J ⊆ Set.Ioi 0 → J.OrdConnected →
      (∀ l ∈ J, ∀ l' ∈ J, (fun j => SignType.sign (w l j)) = fun j => SignType.sign (w l' j)) → J = I

/-- The number of sign-pattern segments of a path, in `ℕ∞`. -/
noncomputable def signSegmentCount (w : ℝ → (Fin p → ℝ)) : ℕ∞ :=
  {I : Set ℝ | IsSignSegment w I}.encard

/-- A **nondegenerate linear segment** of a path (Theorem 5.9, p.10, PDF p.11): a maximal interval of
positive length inside `(0, ∞)` on which `w` is affine in `λ`. -/
def IsLinearSegment (w : ℝ → (Fin p → ℝ)) (I : Set ℝ) : Prop :=
  (I ⊆ Set.Ioi 0 ∧ I.OrdConnected ∧ (∃ a ∈ I, ∃ b ∈ I, a < b) ∧
      ∃ u v : Fin p → ℝ, ∀ l ∈ I, w l = u + l • v) ∧
    ∀ J : Set ℝ, I ⊆ J → J ⊆ Set.Ioi 0 → J.OrdConnected →
      (∃ u v : Fin p → ℝ, ∀ l ∈ J, w l = u + l • v) → J = I

/-- `K(X, y)`: the number of nondegenerate linear segments of the Lasso path, in `ℕ∞`. -/
noncomputable def lassoSegmentCount (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : ℕ∞ :=
  {I : Set ℝ | IsLinearSegment (lassoPath X y) I}.encard

/-- The Mairal–Yu design of Theorem 4.3 (p.5, PDF p.6) with base `B` in dimension `j`:
`X_{ik} = 0` for `i > k`, `X_{kk} = a_k`, `X_{ik} = 2a_k` for `i < k`, with `a_k = B^{−(k−1)}`
(indices are `0, …, j − 1` here, so `a` at index `k` is `B^{−k}`). The `j`-dimensional truncated
instance of the `p`-dimensional design is `mairalYu (100 p³) j`, its leading `j × j` block. -/
def mairalYu (B : ℚ) (j : ℕ) : Matrix (Fin j) (Fin j) ℚ :=
  fun i k => if k < i then 0 else if i = k then (B ^ k.val)⁻¹ else 2 * (B ^ k.val)⁻¹

end AggCG.Supplement


