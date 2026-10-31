-- Prove2me | Definitions.Def_BroadieKaya_SV_EndpointBridge
-- name    : BroadieKaya_SV_EndpointBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:06:52.140809+00:00
-- url     : https://prove2.me/theorems/06c68539-ef5c-4a43-b54e-f764e3680ba0
-- title:
--   Endpoint conditioning by weak limits of observation windows
-- statement:
--   For real random variables $A,Y$ on $(\Omega,P)$, condition on the event $|Y-y|<\varepsilon$ by restricting $P$ to this event and dividing by its mass. A probability measure $\mu$ is the endpoint bridge law for $A$ at $Y=y$ if both variables are almost everywhere measurable, every positive-width window has positive mass, and for every bounded continuous $g:\mathbb R\to\mathbb R$,
--   $$\lim_{\varepsilon\downarrow0}E[g(A)\mid |Y-y|<\varepsilon]=\int g\,d\mu.$$
--   The endpoint bridge function selects such a measure when one exists; otherwise its total-function fallback is $\delta_0$. Every theorem using this function at a deterministic endpoint asserts the bridge property in its conclusion, so existence is never an assumption or a hidden oracle. For the diffusion applications $A$ is integrated variance, $Y$ is terminal variance, and the starting state is deterministic. This also fixes the continuous version at a zero terminal endpoint. Random endpoint statements use Mathlib regular conditional distributions, not this window construction.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.2, p. 220 (PDF 4), and Appendix, (39)–(40), pp. 229–230 (PDF 13–14); explicit encoding of the continuous bridge convention

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


/-- Conditioning on a positive-width observation window, not on a singleton. -/
def windowMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (y ε : ℝ) : Measure Ω :=
  (P {ω | |Y ω - y| < ε})⁻¹ • P.restrict {ω | |Y ω - y| < ε}

/-- A continuous endpoint version specified independently by weak limits of window laws. -/
def HasEndpointBridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A Y : Ω → ℝ) (y : ℝ) (μ : Measure ℝ) : Prop :=
  AEMeasurable A P ∧ AEMeasurable Y P ∧ IsProbabilityMeasure μ ∧
  (∀ ε : ℝ, 0 < ε → 0 < P {ω | |Y ω - y| < ε}) ∧
  ∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
    Tendsto (fun ε : ℝ => ∫ ω, g (A ω) ∂(windowMeasure P Y y ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, g x ∂μ))

/-- A chosen weak limit; existence is proved by the bridge milestones.
The Dirac fallback is never used on their admissible inputs. -/
def endpointBridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A Y : Ω → ℝ) (y : ℝ) : Measure ℝ := by
  classical
  exact if h : ∃ μ, HasEndpointBridge P A Y y μ then h.choose else Measure.dirac 0

end BroadieKaya.SV


