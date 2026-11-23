-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:10.68526+00:00
-- url     : https://prove2.me/theorems/32d5c85e-6f57-419b-a473-e3b0aac5c563
-- title:
--   Exists Schwartz Bump Near Identity
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Bump Near Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
namespace GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def topRows (r t : ℕ) (x : Matrix (Fin (r + t)) (Fin r) k) : Matrix (Fin r) (Fin r) k :=
  x.submatrix (Fin.castAdd t) id
end GlobalTheory.GodementJacquet.TestNearE
namespace GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
end GlobalTheory.GodementJacquet.TestNearE


