-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:43.470931+00:00
-- url     : https://prove2.me/theorems/20f1a025-1289-4fe9-bd8e-5d7fbc82ef35
-- title:
--   Unimodular Hermitian Matrix Congruent One
-- statement:
--   Definitions and structural lemmas for Unimodular Hermitian Matrix Congruent One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
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
namespace GlobalTheory.HermUnimod
section Gen
variable {E : Type} [NormedField E]
def Intg {n m : Type} (h : Matrix n m E) : Prop := ∀ i j, ‖h i j‖ ≤ 1
def Good (n : Type) [Fintype n] [DecidableEq n] (E : Type) [NormedField E] [StarRing E] : Prop :=
  ∀ G : Matrix n n E, G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1
end Gen
section Step
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
end Step
section Main
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
end Main
section Piv
end Piv
section Field
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
end Field
end GlobalTheory.HermUnimod


