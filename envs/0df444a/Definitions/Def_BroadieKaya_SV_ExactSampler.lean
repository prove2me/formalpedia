-- Prove2me | Definitions.Def_BroadieKaya_SV_ExactSampler
-- name    : BroadieKaya_SV_ExactSampler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:09:20.311566+00:00
-- url     : https://prove2.me/theorems/0e8cb04e-8274-409f-9095-dc71f4e0debb
-- title:
--   The four-step ideal Heston sampler
-- statement:
--   For starting state $(s,v)$ and elapsed time $\Delta$, the sampler input is a triple $(w,U,Z)$. Its measure is the product of the explicit variance-draw law, uniform Lebesgue probability on $(0,1)$, and the standard Gaussian law. Set
--   $$\widehat A=\inf\{x\ge0:U\le F_{v,w}(x)\},\qquad
--   \widehat B=\frac{w-v-\kappa\theta\Delta+\kappa\widehat A}{\sigma},$$
--   $$\widehat S=s\exp\{r\Delta-\widehat A/2+\rho\widehat B+\sqrt{(1-\rho^2)\widehat A}\,Z\},\qquad \widehat V=w.$$
--   Here $F$ is the separately defined exact Fourier candidate, not the SDE's already-correct conditional law. The output measure is the image of the input measure under this explicit map. The same sampled $w$ enters the inverse CDF and the stock formula, preserving the dependence between terminal and integrated variance. At $\rho=\pm1$ the normal term is zero. The quantile's nonempty, bounded-below domain and its probability law are conclusions of the inversion theorem, not sampler assumptions. All computations are ideal real or complex operations, with no finite numerical tolerance.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3 algorithm, p. 219 (PDF 3); §3.2 inversion procedure, p. 221 (PDF 5); §3.3, (23) and following displays, pp. 221–222 (PDF 5–6)

import Definitions.Def_BroadieKaya_SV_HestonModel
import Definitions.Def_BroadieKaya_SV_NoncentralChiSquare
import Definitions.Def_BroadieKaya_SV_BridgeTransforms

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


/-- Inverse-CDF construction over the nonnegative half-line. -/
def bridgeQuantile (p : CIRParameters) (Δ v w U : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ U ≤ bridgeCDF p Δ v w x}

abbrev Draw := ℝ × ℝ × ℝ

/-- Independent variance draw, uniform draw, and normal draw. -/
def drawLaw (p : CIRParameters) (Δ v : ℝ) : Measure Draw :=
  (varianceLaw p Δ v).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (gaussianReal 0 1))

def recoveredIntegral (p : CIRParameters) (Δ v w A : ℝ) : ℝ :=
  (w-v-p.kappa*p.theta*Δ+p.kappa*A)/p.sigma

def sample (p : HestonParameters) (Δ s v : ℝ) (d : Draw) : ℝ × ℝ :=
  let w := d.1
  let A := bridgeQuantile p.cir Δ v w d.2.1
  let B := recoveredIntegral p.cir Δ v w A
  (s*Real.exp (p.r*Δ-A/2+p.rho*B+Real.sqrt ((1-p.rho^2)*A)*d.2.2), w)

def sampleLaw (p : HestonParameters) (Δ s v : ℝ) : Measure (ℝ × ℝ) :=
  (drawLaw p.cir Δ v).map (sample p Δ s v)

end BroadieKaya.SV


