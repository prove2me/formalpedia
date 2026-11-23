-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:08.888111+00:00
-- url     : https://prove2.me/theorems/9b24881d-ada7-4155-982b-5eb54e19227c
-- title:
--   Cayley Transform Unitary Skew Involutive
-- statement:
--   Definitions and structural lemmas for Cayley Transform Unitary Skew Involutive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
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
namespace GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
end GlobalTheory.CayleyInv


