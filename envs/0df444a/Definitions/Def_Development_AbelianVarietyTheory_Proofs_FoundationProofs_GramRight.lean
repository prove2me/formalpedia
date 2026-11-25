-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:36:56.113899+00:00
-- url     : https://prove2.me/theorems/f14b4ece-9ebf-4f41-98f5-c3f36611e32a
-- title:
--   Gram Right
-- statement:
--   Definitions and structural lemmas for Gram Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
namespace GlobalTheory.LevelUnitary
def incl (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * r' + k + 1)) ℂ :=
  fun p j => if p = levPos k i r' j then 1 else 0
def outer (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ :=
  diagonal fun p => if i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then 0 else 1
variable (k i r' : ℕ)
end GlobalTheory.LevelUnitary


