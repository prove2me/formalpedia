-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:22.123575+00:00
-- url     : https://prove2.me/theorems/43b9652e-ec8e-486e-97bd-b539cd1ae275
-- title:
--   Pen Met
-- statement:
--   Definitions and structural lemmas for Pen Met, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean

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
open MvPolynomial
section On
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}
variable (C ι) in

structure ConeMetricOn (S : Set (ι → C)) where

  ρ : (ι → C) → ℝ
  pos : ∀ z ∈ S, 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), z ∈ S → c • z ∈ S → ρ (c • z) = ‖c‖ * ρ z
def ConeMetric.restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0) :
    ConeMetricOn C ι S where
  ρ := m.ρ
  pos z hz := m.pos z (hS z hz)
  smul c z _ _ := m.smul c z
def ptNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d
def supNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) : ℝ :=
  sSup (ptNormOn m σ d f '' S)
def IsPtsMeasureOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (μ : MeasureTheory.Measure (ι → ℂ)) :
    Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ (S ∩ {z | m.ρ z = 1})ᶜ = 0
def l2NormOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (σ : o →+* ℂ)
    (μ : MeasureTheory.Measure (ι → ℂ)) (d : ℕ) (f : MvPolynomial ι o) : ℝ :=
  Real.sqrt (∫ z, ptNormOn m σ d f z ^ 2 ∂μ)
theorem conePts_ne_zero (σ : o →+* C) (I : Ideal (MvPolynomial ι o)) :
    ∀ z ∈ conePts σ I, z ≠ 0 :=
  fun _ hz => hz.1
end On
section Gauss
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]
end Gauss
section Homog
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]
end Homog
end ReciprocityTheory.ChartRestriction.G.Geo


