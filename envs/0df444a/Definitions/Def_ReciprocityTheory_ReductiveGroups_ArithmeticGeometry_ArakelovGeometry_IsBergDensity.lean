-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:23.206179+00:00
-- url     : https://prove2.me/theorems/55697ade-a7a2-4adf-beaf-fc345bbf9e1e
-- title:
--   Is Berg Density
-- statement:
--   Definitions and structural lemmas for Is Berg Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsBergDensity.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
variable {J : Type} [Fintype J]
def secFun (b : MvPolynomial J ℚ) (z : J → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b)
def wgt (m : ConeMetric ℂ J) (n : ℕ) (z : J → ℂ) : ℝ :=
  (m.ρ z ^ (2 * n))⁻¹
def logRatio (m₀ m₁ : ConeMetric ℂ J) (z : J → ℂ) : ℝ :=
  Real.log (m₁.ρ z / m₀.ρ z)
theorem _root_.ReciprocityTheory.ChartRestriction.G.Geo.ConeMetric.nonneg (m : ConeMetric ℂ J) (z : J → ℂ) :
    0 ≤ m.ρ z := by
  by_cases hz : z = 0
  · subst hz
    have h := m.smul 0 0
    rw [zero_smul, norm_zero, zero_mul] at h
    exact le_of_eq h.symm
  · exact (m.pos z hz).le
def interp (m₀ m₁ : ConeMetric ℂ J) (t : ℝ) : ConeMetric ℂ J where
  ρ z := m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t
  pos z hz := mul_pos (Real.rpow_pos_of_pos (m₀.pos z hz) _) (Real.rpow_pos_of_pos (m₁.pos z hz) _)
  smul c z := by
    rw [m₀.smul, m₁.smul, Real.mul_rpow (norm_nonneg c) (m₀.nonneg z),
      Real.mul_rpow (norm_nonneg c) (m₁.nonneg z)]
    have key : ‖c‖ ^ (1 - t) * ‖c‖ ^ t = ‖c‖ := by
      rcases eq_or_lt_of_le (norm_nonneg c) with h | h
      · rw [← h]
        by_cases ht : t = 0
        · simp [ht]
        · simp [Real.zero_rpow ht]
      · rw [← Real.rpow_add h]
        simp
    calc ‖c‖ ^ (1 - t) * m₀.ρ z ^ (1 - t) * (‖c‖ ^ t * m₁.ρ z ^ t)
        = (‖c‖ ^ (1 - t) * ‖c‖ ^ t) * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by ring
      _ = ‖c‖ * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by rw [key]
def IsDensityFor {D : ℕ} (μ : Measure (J → ℂ)) (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ)
    (ν : (Fin D → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ 1 ν U ∧ (∀ y ∈ U, 0 < ν y) ∧
    ∀ g : (J → ℂ) → ℝ, Measurable g → IsDegZero g → (∀ z, 0 ≤ g z) →
      ∫⁻ z in coneOver U γ, ENNReal.ofReal (g z) ∂μ = ∫⁻ y in U, ENNReal.ofReal (g (γ y) * ν y)
def IsBergDensity (P : Ideal (MvPolynomial J ℤ)) (D : ℕ) (μ : Measure (J → ℂ))
    (m : ConeMetric ℂ J) (β : (J → ℂ) → ℝ) : Prop :=
  IsDegZero β ∧ ∀ (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ) (ν : (Fin D → ℂ) → ℝ),
    IsParam P U γ → IsDensityFor μ U γ ν → ∀ y ∈ U,
      β (γ y) * ((D.factorial : ℝ) * ν y) =
        maDensity (fun _ : Fin D => fun y' => Real.log (m.ρ (γ y'))) y
def mixPot (m₀ m₁ : ConeMetric ℂ J) (D i : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (m₁.ρ z) else Real.log (m₀.ρ z)
def purePot (m : ConeMetric ℂ J) (D : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun _ z => Real.log (m.ρ z)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


