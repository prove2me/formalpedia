-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_AmbientChain
-- name    : ProcessingNetworks_PacketNetworks_AmbientChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:45:42.496856+00:00
-- url     : https://prove2.me/theorems/97c9ca08-58d8-4a70-a806-7287646e899b
-- title:
--   Irreducibility and positive recurrence of the discrete-time chain Z (restated from mission I)
-- statement:
--   Definition 12.3 speaks of the DTMC $Z = \{Z(\tau), \tau\in\mathbb Z_+\}$ being irreducible and
--   positive recurrent. A countable-state discrete-time Markov chain is represented by its one-step
--   kernel `jump : X → PMF X`, as in mission I. `Irreducible jump` holds when every state is
--   reachable from every other state in finitely many steps. `PositiveRecurrent jump` holds when
--   every state $x$ is recurrent (the chain started at $x$ returns to $x$ with probability one) and
--   the expected return time $E_x(T_x) = \sum_{n\ge 0} P_x(T_x > n)$ is finite.
--
--   **Formalization note.** The notions are mission I's `Stability.Irreducible` and
--   `Stability.PositiveRecurrent jump rate` (Definition D.15) with unit exit rates: a continuous-time
--   chain that holds one unit-mean exponential clock per step of `jump` has $E_x(T_x)$ equal to the
--   expected number of steps of the discrete-time chain before it returns to $x$. Recurrence is part
--   of the definition; finiteness of $\sum_n n f_n(x)$ alone is satisfied by every transient state,
--   whose first-return probabilities sum to less than one, so a definition consisting of that
--   finiteness alone would call a transient chain positive recurrent.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 228, Definition 12.3; p. 46-47 (mission I, restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.PacketNetworks

open scoped ENNReal

/-- `n`-step transition probabilities of a discrete-time Markov chain with one-step kernel
`jump : X → PMF X` (mission I's `Stability.stepIter`; drafts in this series import mission I's
definitions and nothing else). -/
noncomputable abbrev stepIter {X : Type*} (jump : X → PMF X) : ℕ → X → PMF X :=
  Stability.stepIter jump

/-- The chain with one-step kernel `jump` is irreducible: every state is reachable from every
other state in finitely many steps (mission I's `Stability.Irreducible`). -/
abbrev Irreducible {X : Type*} (jump : X → PMF X) : Prop :=
  Stability.Irreducible jump

/-- Positive recurrence of a *discrete-time* Markov chain `Z = {Z(τ), τ ∈ Z+}` with one-step
kernel `jump` (the notion Definition 12.3 invokes for the DTMC `Z`): every state `x` is recurrent
(the chain started at `x` returns to `x` with probability one) and the expected return time
`E_x(T_x) = ∑ₙ P_x(T_x > n)` is finite. This is mission I's continuous-time
`Stability.PositiveRecurrent jump rate` (Definition D.15) with unit exit rates, under which the
continuous-time chain built from `jump` holds one unit-mean exponential clock per step, so
`E_x(T_x)` is the expected number of steps of the discrete-time chain before it returns to `x`.
Recurrence is part of the definition: finiteness of `∑ₙ n · f_n(x)` alone is satisfied by every
transient state, since its first-return probabilities `f_n(x)` sum to less than one. -/
def PositiveRecurrent {X : Type*} (jump : X → PMF X) : Prop :=
  Stability.PositiveRecurrent jump (fun _ => (1 : ℝ))

end ProcessingNetworks.PacketNetworks


