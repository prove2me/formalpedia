-- Prove2me | Definitions.Def_AlwaysValidInference_Efficiency_StoppingLimit
-- name    : AlwaysValidInference_Efficiency_StoppingLimit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:40:24.727276+00:00
-- url     : https://prove2.me/theorems/1401f47f-c4f0-4a3e-bca0-5e4b4087c509
-- title:
--   Probability and mean-square stopping-time convergence
-- statement:
--   The normalized stopping time is $Y_\alpha=T^H(\alpha)/\log(1/\alpha)$, with nontermination represented by infinity. For a non-null parameter $\theta$ the limiting constant is $c=I(\theta,\theta_0)^{-1}$. The stopping-limit predicate requires $Y_\alpha$ to be almost-everywhere measurable, almost surely finite, and square-integrable for every $0<\alpha<1$, and requires both
--   $$\lim_{\alpha\downarrow0}P_\theta(|Y_\alpha-c|>\varepsilon)=0\quad(\varepsilon>0),\qquad\lim_{\alpha\downarrow0}E_\theta[|Y_\alpha-c|^2]=0.$$
--   The deviation is computed in extended nonnegative reals as $\max(Y_\alpha-c,c-Y_\alpha)$. Since the information is strictly positive at every alternative, the limiting constant is finite; an infinite stopping time has infinite error. Square integrability and almost-sure finiteness are part of the conclusion to establish, not additional assumptions about the mSPRT.
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §5.2, equation (10), p. 19 (PDF page = printed page).

import Definitions.Def_AlwaysValidInference_Efficiency_MSPRT

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace AlwaysValidInference.Efficiency

/-- Absolute deviation from a finite limit, retaining infinite errors. -/
noncomputable def extendedDeviation (x c : ℝ≥0∞) : ℝ≥0∞ :=
  max (x - c) (c - x)

noncomputable def normalizedTime {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (H : MixingDistribution E.family.domain) (α : ℝ) (ω : Ω) : ℝ≥0∞ :=
  timeValue (crossingTime E H α ω) / ENNReal.ofReal (Real.log (1 / α))

/-- Convergence in probability and in mean square, including membership in L2
and almost-sure finiteness as conclusions, not assumptions about the algorithm. -/
def StoppingLimit {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (H : MixingDistribution E.family.domain) (θ : ℝ) : Prop :=
  (∀ α ∈ Ioo (0 : ℝ) 1,
    AEMeasurable (normalizedTime E H α) (E.law θ) ∧
    (∀ᵐ ω ∂E.law θ, crossingTime E H α ω < ⊤) ∧
    (∫⁻ ω, (normalizedTime E H α ω) ^ 2 ∂E.law θ) < ⊤) ∧
  (∀ ε : ℝ, 0 < ε →
    Tendsto (fun α => E.law θ {ω | ENNReal.ofReal ε <
      extendedDeviation (normalizedTime E H α ω) (ENNReal.ofReal (E.information θ)⁻¹)})
      (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
  Tendsto (fun α => ∫⁻ ω,
    (extendedDeviation (normalizedTime E H α ω) (ENNReal.ofReal (E.information θ)⁻¹)) ^ 2
      ∂E.law θ) (𝓝[>] (0 : ℝ)) (𝓝 0)

end AlwaysValidInference.Efficiency


