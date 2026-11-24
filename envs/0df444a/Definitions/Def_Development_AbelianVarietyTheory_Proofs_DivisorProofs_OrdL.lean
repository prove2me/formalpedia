-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:53.842349+00:00
-- url     : https://prove2.me/theorems/650eba8d-41c3-47e8-a36c-e5cb46a324fa
-- title:
--   Ord L
-- statement:
--   Definitions and structural lemmas for Ord L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrdL.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DiagVol
def ordL {n : Type*} (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) (fun i => 2 * (i.val + 1))
end GlobalTheory.DiagVol


