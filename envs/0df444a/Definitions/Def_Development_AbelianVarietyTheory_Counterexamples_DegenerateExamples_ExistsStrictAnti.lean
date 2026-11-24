-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_DegenerateExamples_ExistsStrictAnti
-- name    : Development_AbelianVarietyTheory_Counterexamples_DegenerateExamples_ExistsStrictAnti
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:19.541517+00:00
-- url     : https://prove2.me/theorems/79399ba2-2c4c-4c2f-81ec-e3ceac0a6666
-- title:
--   Exists Strict Anti
-- statement:
--   Definitions and structural lemmas for Exists Strict Anti, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/DegenerateExamples/ExistsStrictAnti.lean

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ConeCharCheck
def antiMon (r : ℕ) : Submonoid (Multiplicative (Fin r → ℤ)) where
  carrier := {g | Antitone (Multiplicative.toAdd g)}
  one_mem' := fun _ _ _ => le_rfl
  mul_mem' := fun {a b} ha hb i j h => add_le_add (ha h) (hb h)
end GlobalTheory.ConeCharCheck


