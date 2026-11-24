-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
-- name    : Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:46.863313+00:00
-- url     : https://prove2.me/theorems/94ed11c6-5d20-4f30-8229-018d3610e2a5
-- title:
--   Indexing guard checks by their destination rows
-- statement:
--   A guard indexing for a relation $v\to w$ assigns a nonempty check $Q(v,w)$ to each edge. The check belongs to the source row's guard family, every inspected socket has destination row $w$, and every guard check arises from some outgoing edge.
--
--   The unary indexing uses the singleton $\{(w,\ast)\}$ and indexes the loop-excluding relation $w\ne v\land v\to w$. This packages the exact correspondence between graph destinations and physical guard supports.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/HighHeadGuardBridge.lean lines 16–48; SHA256 a65d8b6636d5eefcc9838f6d69e96a55e7d1b20201ddaaac2d4b039d43d8cb22; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
The semantic bridge from actual high target sockets to tournament outdegree
budgets. It applies directly to the unary and clustered paired guard families.
Every destination has its own nonempty check, supported only on that row.
-/
namespace SensitivityHighHeadGuardBridge

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityGuardEvents
set_option autoImplicit false

structure GuardIndexing {V S : Type} (guards : GuardFamily V S)
    (arc : V → V → Prop) where
  check : V → V → Finset (V × S)
  member : ∀ v w, arc v w → check v w ∈ guards v
  nonempty : ∀ v w, arc v w → (check v w).Nonempty
  destination : ∀ v w socket, socket ∈ check v w → socket.1 = w
  complete : ∀ v c, c ∈ guards v → ∃ w, arc v w ∧ c = check v w



def unaryIndexing {V : Type} [Fintype V] (arc : V → V → Prop) :
    GuardIndexing (unaryTournamentGuards arc) (fun v w => w ≠ v ∧ arc v w) where
  check := fun _ w => {(w,())}
  member := by
    intro v w hw
    exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
  nonempty := by intro v w _; exact Finset.singleton_nonempty _
  destination := by
    intro v w socket hsocket
    exact congrArg Prod.fst (Finset.mem_singleton.mp hsocket)
  complete := by
    intro v c hc
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨w,(Finset.mem_filter.mp hw).2,rfl⟩


















end
end SensitivityHighHeadGuardBridge


