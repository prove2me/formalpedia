-- Prove2me | Definitions.Def_WilliamsonShmoys_RAMSpec
-- name    : WilliamsonShmoys_RAMSpec
-- status  : Definition
-- author  : @もち
-- created : 2026-11-24T06:01:45.637258+00:00
-- url     : https://prove2.me/theorems/77e2e143-958e-4265-a761-4bc5cbf4d968
-- title:
--   Time-bounded Hoare triples for the planar RAM
-- statement:
--   Time-bounded Hoare-style specifications for the unit-cost RAM of this mission (`PlanarRAMInstruction`, `planarRAMRun`).
--
--   For a program $p$, a state $s$, a predicate $Q$ on states and a bound $t\in\mathbb N$, `RAMReachesWithin p s Q t` means that some state reached by running $p$ from $s$ satisfies $Q$ within $t$ operations:
--
--   $$\exists\,\tau\le t,\quad Q\bigl(\mathrm{run}_p(s,\tau)\bigr).$$
--
--   `RAMSpec p P Q t` is the corresponding triple $\{P\}\;p\;\{Q\}_{\le t}$: from every state satisfying $P$, running $p$ reaches a state satisfying $Q$ within $t$ operations. Entry and exit locations of a code fragment are expressed through the program counter inside $P$ and $Q$, and parameter-dependent costs are expressed by quantifying the triple over ghost parameters.
--
--   These predicates are the interface for building the mission's RAM programs compositionally (sequencing, loops, subroutine calls), instead of reasoning about `planarRAMRun` directly.
-- source:
--   Program-logic interface for the unit-cost RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

namespace WilliamsonShmoys

/-- Running `program` from `s`, some state satisfying `Q` is reached after at most `t`
operations (counted by `planarRAMRun`). -/
def RAMReachesWithin (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (Q : PlanarRAMState → Prop) (t : ℕ) : Prop :=
  ∃ τ, τ ≤ t ∧ Q (planarRAMRun program s τ)

/-- Hoare-style specification with a time bound: from every state satisfying `P`, running
`program` reaches a state satisfying `Q` within `t` operations. Program-counter conditions
(the entry and exit locations of a code fragment) are expressed inside `P` and `Q`. -/
def RAMSpec (program : List PlanarRAMInstruction) (P Q : PlanarRAMState → Prop) (t : ℕ) : Prop :=
  ∀ s, P s → RAMReachesWithin program s Q t

end WilliamsonShmoys


