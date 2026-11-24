-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Supplement_ConvexOrder
-- name    : TailRiskSharing_VaRConv_Supplement_ConvexOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:42:59.03094+00:00
-- url     : https://prove2.me/theorems/b9f8cc64-cc38-41cf-8b32-67a7b92065bd
-- title:
--   §6 — convex order and convex-order consistency
-- statement:
--   For measurable real random variables $X,Y$, write $X\prec_{\rm cx}Y$ when every convex real function $f$ for which both expectations exist satisfies
--
--   $$\mathbb E[f(X)]\leq\mathbb E[f(Y)].$$
--
--   A risk measure $\rho$ on $\mathcal X$ is convex-order consistent if it preserves this order for $X,Y\in\mathcal X$. No moment condition on $X$ or $Y$ is added.
--
--   The expectation is represented as the difference of the nonnegative integrals of the positive and negative parts. Existence excludes the undefined $\infty-\infty$ case and allows a one-sided infinite expectation. This reading of “both expectations exist” avoids the zero value of a nonintegrable Bochner integral.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 20, §6

import Mathlib

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- §6 p.20, "provided that both expectations exist": undefined infinity-minus-infinity
is excluded, while a one-sided infinite expectation is permitted. -/
def ExpectationExists (P : Measure Ω) (Z : Ω → ℝ) : Prop :=
  (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P) ≠ ⊤ ∨ (∫⁻ ω, ENNReal.ofReal (-Z ω) ∂P) ≠ ⊤

/-- §6 p.20: signed extended expectation. Used only with ExpectationExists. -/
noncomputable def expectationE (P : Measure Ω) (Z : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (Z ω) ∂P) : EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂P) : EReal)

/-- §6 p.20: convex order with all convex real tests whose two expectations exist.
No moment assumption is imposed on X or Y. -/
def ConvexOrder (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f →
    ExpectationExists P (fun ω => f (X ω)) →
    ExpectationExists P (fun ω => f (Y ω)) →
    expectationE P (fun ω => f (X ω)) ≤ expectationE P (fun ω => f (Y ω))

/-- §6 p.20: preservation of convex order on the source domain. -/
def IsConvexOrderConsistent (P : Measure Ω) (dom : Set (Ω → ℝ))
    (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, ConvexOrder P X Y → ρ X ≤ ρ Y

end TailRiskSharing.VaRConv.Supplement


