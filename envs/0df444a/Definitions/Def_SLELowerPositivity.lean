-- Prove2me | Definitions.Def_SLELowerPositivity
-- name    : SLELowerPositivity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:18.689979+00:00
-- url     : https://prove2.me/theorems/81b6b42c-c528-4ef0-a201-34d08430bc0b
-- statement:
--   The block defines a gauge-positivity target for chordal SLE traces. dimension(κ)=1+κ/8 and codimension(κ)=2−dimension(κ). The upper half-plane is {z : Im z>0}. For a path γ from [0,∞) to ℂ, survivingDomain(γ,t) is the set of points z in the upper half-plane minus the image γ([0,t]) whose connected component in that slit set is unbounded. IsCapacityTwoWitness(U,γ,G,F) for a real driving function U says: γ is continuous, γ(0)=0 and Im γ(t)≥0 for all t; for each t, G_t is complex-differentiable on survivingDomain(γ,t) and maps it into the upper half-plane, F_t is complex-differentiable on the upper half-plane and maps it into survivingDomain(γ,t), and F_t and G_t are mutually inverse on these two domains; G_0 is the identity on the upper half-plane; for each z in the surviving domain, t↦G_t(z) has right derivative 2/(G_t(z)−U_t) in t (taken within t≥0); for each t, z(G_t(z)−z) tends to 2t as z→∞ within the surviving domain; and F_t(U_t+iy) tends to γ(t) as y↓0. IsCapacityTwoTrace(U,γ) means suitable G and F exist. IsOrdinaryChordalSLE(κ,γ,P) for a family γ(ω) of paths on a measurable space Ω with measure P requires each γ(ω)(t) to be measurable in ω, and a real Brownian motion B under P such that, for P-almost every ω, γ(ω) is a capacity-two trace with driving function √κ·B_t(ω). IsGauge(h) means h is continuous and monotone on [0,∞), h(0)=0 and h(r)>0 for r>0. hFormula(κ,r)=r^{dimension(κ)}·(log log(1/r))^{codimension(κ)/2}, and HasSmallRadiusFormula(h,f) means h equals f on some right-neighbourhood of 0. extendedGauge(h) applies h to the real number obtained from an extended radius via toReal and converts to a nonnegative extended real, hausdorffGauge(h) is the metric-construction (Hausdorff-type) measure on ℂ with that gauge, and segment(γ,s,t)=γ([s,t]). SourceLowerMainTarget is a defined proposition, not an established theorem: for every probability space (Ω,P) in the stated universe, every κ with 0<κ<8, every ordinary chordal SLE family γ with parameter κ, and every gauge h that agrees with hFormula(κ,·) for small positive radius, almost surely every segment γ([s,t]) with 0<s<t has strictly positive hausdorffGauge(h) measure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SLELowerPositivity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SLELowerPositivity.lean; bytes 16..3296
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Positivity of the explicit Hausdorff gauge on all positive-time SLE segments. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
universe v_lower

noncomputable def dimension (κ : ℝ) : ℝ := 1 + κ / 8

noncomputable def codimension (κ : ℝ) : ℝ := ((2 : ℕ) : ℝ) - dimension κ

def upperHalfPlane : Set ℂ := {z | 0 < z.im}

def survivingDomain (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  {z | z ∈ upperHalfPlane \ (γ '' Icc 0 t) ∧
    ¬ Bornology.IsBounded (connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z)}

def IsCapacityTwoWitness (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G F : ℝ≥0 → ℂ → ℂ) : Prop :=
  Continuous γ ∧ γ 0 = 0 ∧ (∀ t, 0 ≤ (γ t).im) ∧
    (∀ t, DifferentiableOn ℂ (G t) (survivingDomain γ t)) ∧
    (∀ t, DifferentiableOn ℂ (F t) upperHalfPlane) ∧
    (∀ t, MapsTo (G t) (survivingDomain γ t) upperHalfPlane) ∧
    (∀ t, MapsTo (F t) upperHalfPlane (survivingDomain γ t)) ∧
    (∀ t z, z ∈ survivingDomain γ t → F t (G t z) = z) ∧
    (∀ t z, z ∈ upperHalfPlane → G t (F t z) = z) ∧
    (∀ z ∈ upperHalfPlane, G 0 z = z) ∧
    (∀ t z, z ∈ survivingDomain γ t →
      HasDerivWithinAt (fun u : ℝ => G (Real.toNNReal u) z)
        (2 / (G t z - (U t : ℂ))) (Ici 0) (t : ℝ)) ∧
    (∀ t, Tendsto (fun z : ℂ => z * (G t z - z))
      (cocompact ℂ ⊓ 𝓟 (survivingDomain γ t)) (𝓝 (2 * (t : ℂ)))) ∧
    (∀ t, Tendsto (fun y : ℝ => F t ((U t : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (γ t)))

def IsCapacityTwoTrace (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) : Prop :=
  ∃ G F : ℝ≥0 → ℂ → ℂ, IsCapacityTwoWitness U γ G F

def IsOrdinaryChordalSLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (P : Measure Ω) : Prop :=
  (∀ t, Measurable (fun ω => γ ω t)) ∧
  ∃ B : ℝ≥0 → Ω → ℝ, ProbabilityTheory.IsBrownianReal B P ∧
    ∀ᵐ ω ∂P, IsCapacityTwoTrace (fun t => Real.sqrt κ * B t ω) (γ ω)

structure IsGauge (h : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn h (Ici 0)
  monotoneOn : MonotoneOn h (Ici 0)
  zero : h 0 = 0
  positive : ∀ r, 0 < r → 0 < h r

noncomputable def hFormula (κ r : ℝ) : ℝ :=
  r ^ dimension κ * (Real.log (Real.log (1 / r))) ^ (codimension κ / ((2 : ℕ) : ℝ))

def HasSmallRadiusFormula (h f : ℝ → ℝ) : Prop :=
  h =ᶠ[𝓝[>] 0] f

noncomputable def extendedGauge (h : ℝ → ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (h r.toReal)

noncomputable def hausdorffGauge (h : ℝ → ℝ) : Measure ℂ :=
  Measure.mkMetric (extendedGauge h)

def segment (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) : Set ℂ := γ '' Icc s t

def SourceLowerMainTarget : Prop :=
  ∀ (Ω : Type v_lower) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < ((8 : ℕ) : ℝ) →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (segment (γ ω) s t)



end SLEExactGauge
end
end OAI


