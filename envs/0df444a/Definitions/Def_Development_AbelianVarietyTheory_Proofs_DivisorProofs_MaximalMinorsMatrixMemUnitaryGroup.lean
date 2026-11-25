-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:22.415978+00:00
-- url     : https://prove2.me/theorems/f14e8075-7a1a-4ae4-b661-4c46d3cc2c78
-- title:
--   Maximal Minors Matrix Mem Unitary Group
-- statement:
--   Definitions and structural lemmas for Maximal Minors Matrix Mem Unitary Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
namespace GlobalTheory
noncomputable def strictMonoEquivPowersetCard (a : ℕ) (n : Type*) [LinearOrder n] :
    {s : Fin a → n // StrictMono s} ≃ Set.powersetCard n a :=
  ({ toFun := fun s => OrderEmbedding.ofStrictMono s.1 s.2
     invFun := fun f => ⟨f, f.strictMono⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => by ext; rfl } : {s : Fin a → n // StrictMono s} ≃ (Fin a ↪o n)).trans
    Set.powersetCard.ofFinEmbEquiv
end GlobalTheory


