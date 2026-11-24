-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:33.265986+00:00
-- url     : https://prove2.me/theorems/3b0f3e98-a0a0-4305-bf83-fd8c33dd38ae
-- title:
--   Exists Smaller Unitary Group Embedding
-- statement:
--   Definitions and structural lemmas for Exists Smaller Unitary Group Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
namespace GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}
def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0
def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ
end GlobalTheory.SatakeWeyl.InclusionMultiplication


