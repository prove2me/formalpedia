-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Supplement_FTRL
-- name    : SubquadCutReach_Faster_Supplement_FTRL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:22:58.881176+00:00
-- url     : https://prove2.me/theorems/8df7746e-05a6-4e71-bcb7-6069b44c973a
-- title:
--   Euclidean FTRL with constant step and its regret (§4.1)
-- statement:
--   The online optimisation game of §4.1. In each round an algorithm chooses $y_t\in\mathbb R^n$, then receives a loss vector $\ell_t\in\mathbb R^n$ and incurs loss $\langle \ell_t,y_t\rangle$. Euclidean follow-the-regularised-leader with a constant step $\eta$ starts at $y_1=0$ and updates
--
--   $$y_{t+1}=y_t-\eta\,\ell_t .$$
--
--   The update is not projected onto any set. For a comparator $u\in\mathbb R^n$ the regret after $T$ rounds is
--
--   $$\mathrm{Reg}_T(u)=\sum_{t=1}^T\langle \ell_t,y_t\rangle-\sum_{t=1}^T\langle \ell_t,u\rangle .$$
--
--   This is the general object behind Corollary 4.2; it involves no graph.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`, so the inner product and the norm are the standard Euclidean ones. Rounds are 0-based: `ftrlIter η ℓ t` is the source's $y_{t+1}$, and the regret sums over `t ∈ range T`.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 12, §4.1 (PDF p. 14)

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace SubquadCutReach.Faster.Supplement

/-- §4.1, p. 12 (PDF 14): Euclidean FTRL with a constant step `η`, started at the origin.
Rounds are 0-based: `ftrlIter η ℓ t` is the source's `y_(t+1)`, and
`ftrlIter η ℓ (t+1) = ftrlIter η ℓ t - η • ℓ t`. The update is unprojected. -/
noncomputable def ftrlIter {n : ℕ} (η : ℝ) (ℓ : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => 0
  | t+1 => ftrlIter η ℓ t - η • ℓ t

/-- §4.1, p. 12 (PDF 14): `Reg_T(u) = Σ_{t=1}^T ⟨ℓ_t, y_t⟩ - Σ_{t=1}^T ⟨ℓ_t, u⟩`,
with the standard inner product of `ℝ^n` and 0-based rounds `t ∈ range T`. -/
noncomputable def ftrlRegret {n : ℕ} (η : ℝ) (ℓ : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ t ∈ Finset.range T, inner ℝ (ℓ t) (ftrlIter η ℓ t)) -
    ∑ t ∈ Finset.range T, inner ℝ (ℓ t) u

end SubquadCutReach.Faster.Supplement


