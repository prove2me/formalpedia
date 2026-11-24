-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:28.489735+00:00
-- url     : https://prove2.me/theorems/94601f4b-b2e6-4f56-8d31-7e6e83d4c7ad
-- title:
--   Exists Admissible Is Unit Det Local Involution
-- statement:
--   Definitions and structural lemmas for Exists Admissible Is Unit Det Local Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolution.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.LocalLift
def invEquiv {O : Type} [CommRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃+* O :=
  { c with invFun := c, left_inv := hc, right_inv := hc }
noncomputable def resInv {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.ResidueField.mapEquiv (invEquiv c hc)).toRingHom
end GlobalTheory.LocalLift


