-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenVol
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenVol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:29.190833+00:00
-- url     : https://prove2.me/theorems/498b3bca-a194-48e7-a1d0-2a36ccb13ddd
-- title:
--   Pen Vol
-- statement:
--   Definitions and structural lemmas for Pen Vol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenVol.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter
section Vol
variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
def ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : Set ℝ :=
  {r | ∃ (e : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (e + τ) ∧ h ∈ homogeneousSubmodule ι o e ∧
    aeval x g = s * aeval x h ∧ z ∈ conePts σ (coordIdeal o x) ∧ eval z (map σ h) ≠ 0 ∧
    r = ‖eval z (map σ g)‖ / (‖eval z (map σ h)‖ * m.ρ z ^ τ)}
def ratSupNorm (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : ℝ :=
  sSup (ratVals m σ x τ s)
def supNormAll {E : Type*} [Fintype E] (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω)
    (τ : ℕ) (s : Ω) : ℝ :=
  ⨆ e, ratSupNorm (m e) (σ e) x τ s
def IsSmall {E : Type*} (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω) (τ : ℕ) (s : Ω) : Prop :=
  ∀ e (d : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (d + τ) → h ∈ homogeneousSubmodule ι o d →
    aeval x g = s * aeval x h → z ∈ conePts (σ e) (coordIdeal o x) →
    ‖eval z (map (σ e) g)‖ ≤ ‖eval z (map (σ e) h)‖ * (m e).ρ z ^ τ
def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})
def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop
end Vol
end ReciprocityTheory.ChartRestriction.G.Geo


