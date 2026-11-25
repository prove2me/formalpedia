-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:15.766587+00:00
-- url     : https://prove2.me/theorems/8e15c2df-5b1c-5618-8e51-12d38afa6b3d
-- title:
--   Chart Cone Objects
-- statement:
--   Definitions and structural lemmas for Chart Cone Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*}
def dehomIdeal (i : (k : K) → ι k) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))
abbrev DehomRing (i : (k : K) → ι k) := MvPolynomial (Σ k, ι k) ℂ ⧸ dehomIdeal i
def dehom (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] DehomRing i :=
  Ideal.Quotient.mkₐ ℂ (dehomIdeal i)
def coneUnit (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ :=
  ∏ k, X ⟨k, i k⟩
abbrev ConeRing (i : (k : K) → ι k) := Localization.Away (coneUnit i)
theorem isUnit_coneX (i : (k : K) → ι k) (k : K) :
    IsUnit (algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (Finset.mem_univ k))) (IsLocalization.Away.algebraMap_isUnit (coneUnit i))
def coneRatio (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ConeRing i :=
  aeval fun p => (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
    algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X p)
theorem coneRatio_X_self (i : (k : K) → ι k) (k : K) : coneRatio i (X ⟨k, i k⟩) = 1 := by
  rw [coneRatio, aeval_X]
  exact (isUnit_coneX i k).val_inv_mul
def ratioMap (i : (k : K) → ι k) : DehomRing i →+* ConeRing i :=
  Ideal.Quotient.lift (dehomIdeal i) (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) (by
    have hle : dehomIdeal i ≤ RingHom.ker (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp [coneRatio_X_self]
    exact fun a ha => hle ha)
omit [Fintype K] in
theorem dehom_X_self (i : (k : K) → ι k) (k : K) : dehom i (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (dehom i), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
theorem dehom_coneUnit (i : (k : K) → ι k) : dehom i (coneUnit i) = 1 := by
  rw [coneUnit, map_prod]
  exact Finset.prod_eq_one fun k _ => dehom_X_self i k
def evalOne (i : (k : K) → ι k) : ConeRing i →+* DehomRing i :=
  IsLocalization.Away.lift (coneUnit i) (g := (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i))
    (by rw [AlgHom.coe_toRingHom, dehom_coneUnit]; exact isUnit_one)
variable [DecidableEq K]
def segreDehom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] DehomRing i :=
  aeval fun a => dehom i (∏ k, X ⟨k, σ a k⟩)
end Objects
end GroundTheory.Heights₂.Heights.Targets


