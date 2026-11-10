-- Prove2me | Definitions.Def_KnownFidelity_Rank_sizeBiasedPrior
-- name    : KnownFidelity_Rank_sizeBiasedPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:41.821204+00:00
-- url     : https://prove2.me/theorems/2b9ea5c4-7c6f-4717-bca2-c756eebbaf85
-- title:
--   The size-biased prior $\Pi_b^{(m)}$, Eq. (41)
-- statement:
--   For $a\in\mathbb R^r_{\ge0}$ and an integer $m$, the **size-biased prior** is $Q(a)$ reweighted by the $m$-th moment of $\|G\|_F^2$:
--
--   $$\frac{d\Pi^{(m)}}{dQ}(G)=\frac{\|G\|_F^{2m}}{\mathbb E_{Q}\|G\|_F^{2m}} .$$
--
--   **Formalization Note** The normalizer is a lower Lebesgue integral; it is finite and positive when $\sum_i a_i=1$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.4, Eq. (41), p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_wishartLaw
import Definitions.Def_KnownFidelity_Rank_frobSq

open MeasureTheory

namespace KnownFidelity.Rank

/-- **The size-biased prior `Π_b^{(m)}`, Eq. (41).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.4, Eq. (41), printed p. 17 (PDF p. 19): "For an integer m ≥ 1, define the
size-biased prior dΠ_b^{(m)}/dQ_b (G) = ∥G∥_F^{2m} / E_{Q_b} ∥G∥_F^{2m}."

`sizeBiasedPrior a m` is `Q = wishartLaw a` reweighted by the density
`‖G‖_F^{2m} / E_Q ‖G‖_F^{2m}`.

**Formalization Note.** The normalizer `E_Q ‖G‖_F^{2m}` is a lower Lebesgue integral in `ℝ≥0∞`
(finite and positive when `Σ_i a_i = 1`, since Gaussian moments are finite and `G ≠ 0` with
positive probability), so it never takes a junk value. -/
noncomputable def sizeBiasedPrior {r : ℕ} (a : Fin r → ℝ) (m : ℕ) :
    Measure (Matrix (Fin r) (Fin r) ℂ) :=
  (wishartLaw a).withDensity fun G =>
    ENNReal.ofReal (frobSq G ^ m) / ∫⁻ G', ENNReal.ofReal (frobSq G' ^ m) ∂(wishartLaw a)

end KnownFidelity.Rank


