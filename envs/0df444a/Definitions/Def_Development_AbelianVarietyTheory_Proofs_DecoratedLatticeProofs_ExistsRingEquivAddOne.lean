-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:43.075801+00:00
-- url     : https://prove2.me/theorems/378b499d-d6a0-4146-ac02-8fec62484eef
-- title:
--   Exists Ring Equiv Add One
-- statement:
--   Definitions and structural lemmas for Exists Ring Equiv Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRingEquivAddOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ShiftVariables
noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)
end GlobalTheory.ShiftVariables


