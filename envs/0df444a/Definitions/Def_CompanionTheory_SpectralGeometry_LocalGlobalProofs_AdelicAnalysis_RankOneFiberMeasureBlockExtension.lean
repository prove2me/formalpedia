-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:06.665165+00:00
-- url     : https://prove2.me/theorems/83c87b60-7e02-41ed-b292-b284cd90e552
-- title:
--   Rank One Fiber Measure Block Extension
-- statement:
--   Definitions and structural lemmas for Rank One Fiber Measure Block Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def sclMat : R →* Matrix (Fin 1) (Fin 1) (R ⊗[F] E) where
  toFun u := Matrix.of fun _ _ => u ⊗ₜ[F] (1 : E)
  map_one' := by
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  map_mul' u v := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
def unitTens : Rˣ →* (R ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E).toMonoidHom
end Alg
end GlobalTheory.CompanionTheory.SW.PiLocalization₂


