-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain
-- name    : ProcessingNetworks_PacketNetworks_BPAmbientChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:54:05.662442+00:00
-- url     : https://prove2.me/theorems/22f02dfd-9f5b-4695-822d-94fc257f114a
-- title:
--   Reachable states, irreducibility, aperiodicity and positive recurrence on a state space (Lemma 12.18)
-- statement:
--   State-space-relative chain notions for Section 12.5, on top of mission XII's `AmbientChain`
--   (imported): `reachableFrom jump x₀` is the set of states the chain can reach from $x_0$;
--   `IrreducibleOn jump X` says every state of $X$ is reachable from every other state of $X$ (Lemma
--   12.18's "$Z$ is irreducible with state space $\mathcal X$"); `AperiodicOn jump X` says every
--   state of $X$ has period $1$, the only common divisor of its return times
--   $\{n\ge 1 : P_x(Z(n)=x)>0\}$ being $1$; `PositiveRecurrentOn jump X` says every state of $X$
--   is recurrent with finite expected return time (mission I's notions with unit exit rates, as in
--   mission XII's `PositiveRecurrent`).
--
--   **Formalization note.** Lemma 12.18 and Theorem 12.16 assert irreducibility and aperiodicity
--   of $Z$ on the state space $\mathcal X$ of states reachable from $0$, as the proof of Lemma 12.18
--   says explicitly; on all of $\mathbb Z^I_+$ the assertion is false (a class that never receives
--   packets under the policy is never revisited). Aperiodicity is period $1$, not merely a positive
--   self-transition probability, which is the proof's route to it but a stronger property.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 241, Lemma 12.18 (restated from mission XII/I, plus Aperiodic)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_AmbientChain

namespace ProcessingNetworks.PacketNetworks

open scoped ENNReal

/-- The states reachable from `x₀` by the chain with one-step kernel `jump` (including `x₀`
itself, in zero steps): the state space `X` of Lemma 12.18's proof when `x₀ = 0`. -/
def reachableFrom {X : Type*} (jump : X → PMF X) (x₀ : X) : Set X :=
  {y | ∃ n : ℕ, 0 < stepIter jump n x₀ y}

/-- The chain is irreducible with state space `X` (Lemma 12.18's "`Z` is irreducible with state
space `𝒳`"): every state of `X` is reachable from every other state of `X` in finitely many
steps. -/
def IrreducibleOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℕ, 0 < stepIter jump n x y

/-- The chain is aperiodic on the state space `S`: every state `x ∈ S` has period `1`, i.e. the
only common divisor of the return times `{n ≥ 1 : P_x(Z(n) = x) > 0}` is `1`. -/
def AperiodicOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < stepIter jump n x x → d ∣ n) → d = 1

/-- The chain is positive recurrent on the state space `S`: every state `x ∈ S` is recurrent
with finite expected return time (mission I's `Stability.Recurrent` and `Stability.meanReturnTime`
with unit exit rates, as in mission XII's `PositiveRecurrent`, restricted to `S`). -/
def PositiveRecurrentOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, Stability.Recurrent jump x ∧ Stability.meanReturnTime jump (fun _ => (1 : ℝ)) x < ⊤

end ProcessingNetworks.PacketNetworks


