-- Prove2me | Definitions.Def_FreeReplExchange_Supplement_CycleExchange
-- name    : FreeReplExchange_Supplement_CycleExchange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:33:37.760083+00:00
-- url     : https://prove2.me/theorems/b6af92f6-5c4c-428e-9a34-be0041e42641
-- title:
--   MIC cyclic exchanges of single goods and their binary decision language
-- statement:
--   A **cyclic exchange** has $k\ge2$ distinct agents in cyclic order. Each agent gives one initially owned good to the next agent and receives one from the previous agent. The cycle executes atomically only when all participants accept; onward sharing is forbidden and duplicate receipts count once. A proposal list is MIC when accepting every incident cycle is a best response for each agent against every decision profile.
--
--   A finite accept-all schedule is valid when every round is MIC at the current allocation and every cycle respects a stated length bound. The binary decision language records an exact rational ESC instance and a threshold $T$; it accepts exactly when the instance has three goods and a valid MIC schedule of cycles of length at most $3$ reaches at least $T$ filled slots.
--
--   This language is the decision form of the maximization problem in Theorem 8.
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), section 3.7, pp.28--29 (PDF pp.30--31), Theorem 8

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_BundleExchange

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- A cyclic exchange of single goods, section 3.7, p. 28 (PDF p. 30): `k >= 2` distinct agents
are in cyclic order, and agent `t` gives her initially owned good `good t` to agent `t+1`. -/
structure CycleExchange (A : Type*) (m : ℕ) where
  k : ℕ
  hk : 2 ≤ k
  agent : Fin k → A
  good : Fin k → Fin m
  distinct : Function.Injective agent

/-- The successor of a position in the cyclic order. -/
def CycleExchange.next {A : Type*} {m : ℕ} (c : CycleExchange A m) (t : Fin c.k) : Fin c.k :=
  ⟨(t.val + 1) % c.k, Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 2) c.hk)⟩

/-- Cycle well-formedness: every outgoing good belongs to its giver in the initial allocation, so
onward sharing is excluded, section 3.7, p. 28 (PDF p. 30). -/
def CycleWellFormed {A : Type*} {m : ℕ} (x0 : A → Fin m → Bool)
    (c : CycleExchange A m) : Prop :=
  ∀ t, x0 (c.agent t) (c.good t) = true

open Classical in
/-- Execute a finite list of cycles atomically at allocation `x`; each arc sends `good t` from
`agent t` to the next agent.  Boolean union makes duplicate receipts count once. -/
noncomputable def execCycles {A : Type*} {m : ℕ} (x : A → Fin m → Bool)
    (S : List (CycleExchange A m)) : A → Fin m → Bool :=
  fun i r => x i r || decide (∃ c ∈ S, ∃ t : Fin c.k,
    i = c.agent (c.next t) ∧ r = c.good t)

open Classical in
/-- The cycle allocation under accept/reject decisions.  A cycle executes as a whole exactly when
every one of its participants accepts it. -/
noncomputable def cycleOutcome {A : Type*} {m : ℕ} (x : A → Fin m → Bool)
    (S : List (CycleExchange A m)) (δ : A → CycleExchange A m → Bool) :
    A → Fin m → Bool :=
  execCycles x (S.filter fun c => decide (∀ t, δ (c.agent t) c = true))

/-- Myopic incentive compatibility for a list of atomic cyclic proposals: accepting every incident
cycle is a best response for each agent against every profile of the others' decisions, section 3.7,
pp. 28--29 (PDF pp. 30--31). -/
def IsCycleMICSet {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (U : A → A → Fin m → ℝ) (x : A → Fin m → Bool)
    (S : List (CycleExchange A m)) : Prop :=
  ∀ (i : A) (δ : A → CycleExchange A m → Bool),
    util U i (cycleOutcome x S δ) ≤
      util U i (cycleOutcome x S (Function.update δ i fun _ => true))

/-- Validity of a finite accepting-path schedule of cyclic proposal lists.  Every outgoing good is
initially owned, every cycle has length at most `B`, and every round is MIC at the allocation reached
by preceding accepting rounds. -/
def IsCycleSchedule {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (B : ℕ) :
    (A → Fin m → Bool) → List (List (CycleExchange A m)) → Prop
  | _, [] => True
  | x, S :: rest =>
      (∀ c ∈ S, CycleWellFormed x0 c ∧ c.k ≤ B) ∧ IsCycleMICSet U x S ∧
        IsCycleSchedule x0 U B (execCycles x S) rest

/-- The terminal accepting-profile allocation of a finite cyclic schedule. -/
noncomputable def runCycleSchedule {A : Type*} {m : ℕ} (x0 : A → Fin m → Bool) :
    List (List (CycleExchange A m)) → A → Fin m → Bool
  | [] => x0
  | S :: rest => runCycleSchedule (execCycles x0 S) rest

/-- The restricted decision language underlying Theorem 8: an exact rational ESC instance with
exactly three goods is a yes instance when some finite accepting-path MIC schedule of atomic cycles,
each of length two or three and using only initially owned outgoing goods, reaches the input
filled-slot threshold. -/
def cycleSharingLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ I : SharingInstance, w = encodeSharingInstance I ∧ 0 < I.n ∧ I.m = 3 ∧
      IsESC I.U I.betaReal ∧
      ∃ rounds : List (List (CycleExchange (Fin I.n) I.m)),
        IsCycleSchedule I.x0 I.U 3 I.x0 rounds ∧
          I.threshold ≤ filledCount (runCycleSchedule I.x0 rounds)}

end FreeReplExchange.Supplement


