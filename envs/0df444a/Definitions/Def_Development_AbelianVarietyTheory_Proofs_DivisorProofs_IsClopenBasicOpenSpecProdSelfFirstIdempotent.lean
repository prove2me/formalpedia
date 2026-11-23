-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:50.117121+00:00
-- url     : https://prove2.me/theorems/4e8e2e0c-7e86-46bd-84ba-59ec5687a827
-- title:
--   Is Clopen Basic Open Spec Prod Self First Idempotent
-- statement:
--   Definitions and structural lemmas for Is Clopen Basic Open Spec Prod Self First Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClopenBasicOpenSpecProdSelfFirstIdempotent.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory.AlgConn
abbrev twoπ (O : Type) [CommRing O] : Spec (.of (O × O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))
abbrev fst1 (O : Type) [CommRing O] : Γ(Spec (.of (O × O)), ⊤) :=
  (Scheme.ΓSpecIso (.of (O × O))).inv.hom ((1, 0) : O × O)
end GlobalTheory.AlgConn


