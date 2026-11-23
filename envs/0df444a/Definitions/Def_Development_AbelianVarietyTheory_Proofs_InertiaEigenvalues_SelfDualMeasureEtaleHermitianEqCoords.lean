-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoords
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoords
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:06:24.958811+00:00
-- url     : https://prove2.me/theorems/aba85841-a56d-4dbb-8f06-0583a3018670
-- title:
--   Self Dual Measure Etale Hermitian Eq Coords
-- statement:
--   Definitions and structural lemmas for Self Dual Measure Etale Hermitian Eq Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualMeasureEtaleHermitianEqCoords.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.Hyp
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
def ccLin (A : Et F E) (e : A.L) : (A.K × A.K) →ₗ[F] A.L where
  toFun := cc A e
  map_add' p q := by simp only [cc, Prod.fst_add, Prod.snd_add, map_add]; ring
  map_smul' c p := by
    simp only [cc, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply F A.K A.L, map_mul]
    ring
def ccEquiv [Unram F E] (A : Et F E) (e : A.L) (h1 : ∀ p, ci A e (cc A e p) = p)
    (h2 : ∀ y, cc A e (ci A e y) = y) : (A.K × A.K) ≃L[F] A.L :=
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  let l : (A.K × A.K) ≃ₗ[F] A.L := { ccLin A e with invFun := ci A e, left_inv := h1, right_inv := h2 }
  { l with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap l.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap }
def tt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) : A.K × A.K → ℂ :=
  pt A ν ψ x (fun q => pt A ν ψ x Φ (q.2, q.1))
end GlobalTheory.JR.Hyp


