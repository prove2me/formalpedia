-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:55.75956+00:00
-- url     : https://prove2.me/theorems/76e8bd07-1c01-4b81-8050-1c495a57a645
-- title:
--   Exists Compact Subgroup
-- statement:
--   Definitions and structural lemmas for Exists Compact Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
namespace GlobalTheory.UnipCompact
variable {n : Type}
theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]
end GlobalTheory.UnipCompact


