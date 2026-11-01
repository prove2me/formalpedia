-- Prove2me | Definitions.Def_SelfGuidedALP_Bspace
-- name    : SelfGuidedALP_Bspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:37.744979+00:00
-- url     : https://prove2.me/theorems/1da4f484-0d37-464c-b59a-ac285e91062f
-- title:
--   The space $\mathcal B$ of $(2,\rho)$-integrable weighting functions
-- statement:
--   The space of weighting functions is
--   $$
--   \mathcal B:=\{B:\Theta\to\mathbb R:\ \|B/\rho\|_{2,\rho}<\infty\},\qquad \langle B,B'\rangle_{\mathcal B}:=\int_\Theta\frac{B(\theta)B'(\theta)}{\rho(\theta)}\,\mathrm d\theta .
--   $$
--   Its norm is
--   $$
--   \|B/\rho\|_{2,\rho}:=\Bigl(\int_\Theta\frac{B(\theta)^2}{\rho(\theta)}\,\mathrm d\theta\Bigr)^{1/2}.
--   $$
--
--   This Hilbert space carries the orthogonal decomposition behind the mission's goal.
--
--   **Formalization Note** $\mathcal B$ is the $L^2$ space of the weight measure, so elements are almost-everywhere classes. **The norm carries a square root.** Page 9 prints $\|B/\rho\|_{2,\rho}$ as the integral itself, without the root; that is the square of this norm. Finiteness is the same either way, but the paper's bounds are false for the printed quantity, because they would be quadratic in $B$ while the error is linear.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8, and p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_weightMeasure

open MeasureTheory

namespace SelfGuidedALP

/-- The space `ℬ := {B : Θ → ℝ : ‖B/ρ‖_{2,ρ} < ∞}` of `(2,ρ)`-integrable weighting functions
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8).

**Formalization Note.** `ℬ` is Mathlib's `L²` space of `(1/ρ) dθ`. Its inner product is
`⟨B,B'⟩_ℬ = ∫_Θ B B'/ρ dθ`. Its norm `‖B‖` is `‖B/ρ‖_{2,ρ}` **with the square root**,
`(∫_Θ B²/ρ dθ)^{1/2}`: the integral printed on p.9 is the square of this norm (the paper's bounds are
false for the printed quantity). Elements are almost-everywhere classes. -/
abbrev Bspace {d : ℕ} (R : RBClass d) : Type :=
  Lp ℝ 2 (weightMeasure R)

end SelfGuidedALP


