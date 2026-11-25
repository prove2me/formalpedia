-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundElementaryApply
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundElementaryApply
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:57:58.816746+00:00
-- url     : https://prove2.me/theorems/f13525c3-130e-4221-952a-ef9422c4a28b
-- title:
--   Compact Casimir Bound Elementary Apply
-- statement:
--   Definitions and structural lemmas for Compact Casimir Bound Elementary Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirBoundElementaryApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaiseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
namespace GlobalTheory.CasKAdjoint
def adMat {n : ℕ} (a b : Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun i j =>
  (if i.1 = a ∧ j = (b, i.2) then 1 else 0) - (if i.2 = b ∧ j = (i.1, a) then 1 else 0)
end GlobalTheory.CasKAdjoint


