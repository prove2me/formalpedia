-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
-- name    : GroundTheory_LocalFields_LubinTateReciprocity_RootEval
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:59.699807+00:00
-- url     : https://prove2.me/theorems/b06f0d18-70b5-41c7-8a4b-94e4bedebe6e
-- title:
--   Root Eval
-- statement:
--   Definitions and structural lemmas for Root Eval, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open PowerSeries
section HomExt
variable {B S : Type*} [CommRing B] [CommRing S]
end HomExt
section RootEval
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)
def rootEval : B⟦X⟧ →ₐ[B] AdjoinRoot P :=
  (hP.algEquivQuotient.symm.toAlgHom : B⟦X⟧ ⧸ Ideal.span {(P : B⟦X⟧)} →ₐ[B] AdjoinRoot P).comp
    (Ideal.Quotient.mkₐ B _)
end RootEval
section Hausdorff
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
end Hausdorff
section Coordinates
variable {B : Type*} [CommRing B] {P : Polynomial B}
end Coordinates
end GroundTheory.LocalField


