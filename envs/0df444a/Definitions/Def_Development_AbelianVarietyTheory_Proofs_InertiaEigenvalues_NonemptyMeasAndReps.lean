-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:41.339571+00:00
-- url     : https://prove2.me/theorems/5c15d90c-7247-4e06-9c7b-0e48423c330b
-- title:
--   Nonempty Meas And Reps
-- statement:
--   Definitions and structural lemmas for Nonempty Meas And Reps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyMeasAndReps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.EtMeas
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
theorem star_smul_K (A : Et F E) (k : A.K) (y : A.L) : star (k • y) = k • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]
theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [← algebraMap_smul A.K c y, star_smul_K, algebraMap_smul]
def starF (A : Et F E) : A.L →ₗ[F] A.L where
  toFun := star
  map_add' := star_add
  map_smul' := star_smul_F A
def formL (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  ((LinearMap.mul F A.L).comp (starF A)).compr₂
    ((Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F)))
def normU (A : Et F E) : A.Lˣ →* A.Kˣ := Units.map (Algebra.norm A.K : A.L →* A.K)
end GlobalTheory.JR.EtMeas


