-- Prove2me | Definitions.Def_StrictMeans
-- name    : StrictMeans
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:26.663873+00:00
-- url     : https://prove2.me/theorems/8200552a-0974-4b7d-842e-c9675cd67d18
-- statement:
--   The disk is the open unit disk in the complex plane. A function f is normalized univalent if it is complex differentiable on the disk, injective there, and satisfies f(0)=0 and f'(0)=1; it is bounded normalized univalent if in addition there is a real R with |f(z)| ≤ R for all z in the disk. For a real exponent p, a function f and a radius r, integralMean(p,f,r) is the average (2π)⁻¹ ∫ from -π to π of |f'(r e^{iθ})|^p dθ of the p-th power of the modulus of the derivative over the circle of radius r. growthExponent(p,f) is the extended-real limsup, as r tends to 1 from below, of log(integralMean(p,f,r)) divided by log(1/(1-r)), measuring the power-law growth rate of this mean near the boundary. boundedSpectrum(p) is the supremum, in the extended reals, of growthExponent(p,f) over all bounded normalized univalent f. kraetzerPrediction(p) is the explicit value p²/4 when |p| ≤ 2 and |p|-1 when |p| > 2. The block only defines these objects, and it does not state or assert any relationship between boundedSpectrum and kraetzerPrediction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StrictMeans.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StrictMeans.lean; bytes 16..1118
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower

def disk : Set ℂ := Metric.ball 0 1

def NormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f disk ∧ Set.InjOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def BoundedNormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  NormalizedUnivalent f ∧ ∃ R : ℝ, ∀ z ∈ disk, ‖f z‖ ≤ R

noncomputable def integralMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p

noncomputable def growthExponent (p : ℝ) (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean p f r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

noncomputable def boundedSpectrum (p : ℝ) : EReal :=
  ⨆ (f : ℂ → ℂ) (_ : BoundedNormalizedUnivalent f), growthExponent p f

noncomputable def kraetzerPrediction (p : ℝ) : EReal :=
  if |p| ≤ 2 then ((p ^ (2 : ℕ) / 4 : ℝ) : EReal)
  else ((|p| - 1 : ℝ) : EReal)



end StrictInverseFirstPower
end OAI


