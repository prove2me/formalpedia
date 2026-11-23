-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:54.010255+00:00
-- url     : https://prove2.me/theorems/a57c5b90-4fd9-49df-a778-704a1c8f2319
-- title:
--   Exists Anisotropic Orthogonal Basis Hermitian
-- statement:
--   Definitions and structural lemmas for Exists Anisotropic Orthogonal Basis Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAnisotropicOrthogonalBasisHermitian.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep
end GlobalTheory.UnRep


