-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:35.290807+00:00
-- url     : https://prove2.me/theorems/89f497d5-153d-4202-a0a6-4b4b4daa97d4
-- title:
--   Herm Basis Orthonormal
-- statement:
--   Definitions and structural lemmas for Herm Basis Orthonormal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.OrthBasis
open GlobalTheory.UnitLemma
variable {K : UQ} (B : InvAlg K)
end GlobalTheory.UnitLemma.OrthBasis
namespace GlobalTheory.UnitLemma
open GlobalTheory.UnitLemma.OrthBasis
end GlobalTheory.UnitLemma


