-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:06.145661+00:00
-- url     : https://prove2.me/theorems/adf0cc82-47b1-4690-b441-693e96589a8e
-- title:
--   Gram Fiber Measures Integral Formula
-- statement:
--   Definitions and structural lemmas for Gram Fiber Measures Integral Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ScaleCont
section Actions
variable {K : Type} [CommRing K] {n M : ℕ}
def tupR (X : Fin n → Fin M → K) (g : Matrix (Fin n) (Fin n) K) : Fin n → Fin M → K :=
  fun a i => ∑ c, X c i * g c a
theorem tupR_tupR (X : Fin n → Fin M → K) (g h : Matrix (Fin n) (Fin n) K) :
    tupR (tupR X g) h = tupR X (g * h) := by
  funext a i
  simp only [tupR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
theorem tupR_one (X : Fin n → Fin M → K) : tupR X 1 = X := by
  funext a i
  simp [tupR, Matrix.one_apply]
def tupAction : DistribMulAction (GL (Fin n) K) (Fin n → Fin M → K) where
  smul q X := tupR X ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  one_smul X := by
    show tupR X (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X
    simp [tupR_one]
  mul_smul q q' X := by
    show tupR X (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tupR (tupR X ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [tupR_tupR, mul_inv_rev, Units.val_mul]
  smul_zero q := by
    show tupR 0 _ = 0
    funext a i
    simp [tupR]
  smul_add q X Y := by
    show tupR (X + Y) _ = tupR X _ + tupR Y _
    funext a i
    simp [tupR, add_mul, Finset.sum_add_distrib]
theorem cT_one' (s : K →+* K) : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT, Matrix.map_one]
theorem cT_mul' (s : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]
def hermAction (s : K →+* K) (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    DistribMulAction (GL (Fin n) K) H where
  smul q S := ⟨cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hmem S _⟩
  one_smul S := by
    apply Subtype.ext
    show cT s (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = S
    simp [cT_one']
  mul_smul q q' S := by
    apply Subtype.ext
    show cT s (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K) * (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (cT s ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (S : Matrix (Fin n) (Fin n) K) * ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [mul_inv_rev, Units.val_mul, cT_mul']
    simp only [Matrix.mul_assoc]
  smul_zero q := by
    apply Subtype.ext
    show cT s _ * ((0 : H) : Matrix (Fin n) (Fin n) K) * _ = 0
    simp
  smul_add q S T := by
    apply Subtype.ext
    show cT s _ * ((S + T : H) : Matrix (Fin n) (Fin n) K) * _ =
      cT s _ * (S : Matrix (Fin n) (Fin n) K) * _ + cT s _ * (T : Matrix (Fin n) (Fin n) K) * _
    simp [Matrix.mul_add, Matrix.add_mul]
variable [TopologicalSpace K] [IsTopologicalRing K]
end Actions
end GlobalTheory.CompanionTheory.SW.ScaleCont


