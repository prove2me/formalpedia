-- Prove2me | Definitions.Def_NonstatNV_Model_NoiseMGFBound
-- name    : NonstatNV_Model_NoiseMGFBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:47.916616+00:00
-- url     : https://prove2.me/theorems/2c976c9e-2be1-4318-8397-18f74f95150c
-- title:
--   Uniform sub-Gaussian bound $\delta$ on the demand noise
-- statement:
--   A model has a **uniform noise bound $\delta$** if for every $\mu\in[\mu_{\min},\mu_{\max}]$ the noise $\epsilon=d-\mu$, $d\sim D_\mu$, satisfies
--
--   $$
--   \mathbb E\big[\exp(\epsilon^2/\delta^2)\big]\le 2,
--   $$
--
--   with the integrand integrable. In the proofs of Lemma 5 and Theorem 2 the paper uses $\delta_s=\inf\{\delta'\ge0:\mathbb E[e^{\epsilon_s^2/\delta'^2}]\le2\}$ and $\delta=\max_s\delta_s$; any $\delta$ satisfying the displayed bound for every law of the family dominates these.
--
--   **Formalization Note** The bound is uniform over the family, so the tuning condition (G.1) on $\gamma$ can be met before the instance is chosen. The condition is meaningful for $\delta>0$, which every use requires.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Proof of Lemma 5, p.37 ($\delta_s$, $\delta=\max_s\delta_s$); (G.1), p.48

import Definitions.Def_NonstatNV_Model

open MeasureTheory

namespace NonstatNV

/-- A uniform sub-Gaussian (Orlicz) bound `δ` on the demand noise `ε = d − μ`
(An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, proof of Lemma 5, p.37: `δ_s = inf{δ' ≥ 0 : E[e^{ε_s²/δ'²}] ≤ 2}` and `δ = max_s δ_s`;
the same `δ` in (G.1), p.48): for every `μ ∈ [μmin, μmax]`, `E_{d∼D_μ}[exp((d − μ)²/δ²)] ≤ 2`,
the integrand being integrable.

**Formalization Note** The bound is uniform over the family, which is what makes a parameter `γ`
satisfying (G.1) exist before the instance is chosen. Any valid `δ` may be used, so the infimum is
covered. The condition is meaningful for `δ > 0`; every use requires `δ > 0`. -/
def Model.NoiseMGFBound (M : Model) (δ : ℝ) : Prop :=
  ∀ μ ∈ Set.Icc M.μmin M.μmax,
    Integrable (fun d : ℝ => Real.exp ((d - μ) ^ 2 / δ ^ 2)) (M.D μ : Measure ℝ) ∧
    ∫ d, Real.exp ((d - μ) ^ 2 / δ ^ 2) ∂(M.D μ : Measure ℝ) ≤ 2

end NonstatNV


