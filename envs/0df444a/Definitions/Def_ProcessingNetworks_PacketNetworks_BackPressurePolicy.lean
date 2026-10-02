-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
-- name    : ProcessingNetworks_PacketNetworks_BackPressurePolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:54:38.219892+00:00
-- url     : https://prove2.me/theorems/9069264d-1147-460d-848c-821c304fa06d
-- title:
--   The MW/BP optimization problem and the back-pressure control policy (Eqs. 12.3, 12.41)
-- statement:
--   **Section 12.4.** At buffer contents $z$, the max-weight/back-pressure (MW/BP) control policy
--   solves $\max_{s\in S(z)} z\cdot Rs$ (Eq. 12.41), where $S(z) := \{s\in S : Bs\le z\}$ (Eq.
--   12.40) is the subset of the schedule set satisfying the packet availability constraint (12.3).
--   The policy is called max-weight for a single-hop network and back-pressure for a multi-hop one.
--   `IsBackPressurePolicy dat S f` says the Markovian policy $f$ of (12.8) chooses, in every
--   timeslot and at every observed state $z$, a solution of (12.41).
--
--   **Formalization note.** `feasibleSchedulesAt`/`bpObjective`/`IsBPOptimal` are phrased for
--   `z : Fin I → ℝ`, so the same definitions serve the discrete state (`z` cast from
--   `Fin I → ℕ`) and the fluid-scale state $\hat Z(t)$ (Lemma 12.20). `IsBPOptimal` is phrased via
--   domination, not `sSup`/`argmax`. The policy function has mission XII's signature
--   $f(z,u)$ so that it is the policy of the DTMC of Section 12.1 and every version of the policy
--   (every tie-breaking rule, deterministic or randomized, Remark 12.19) is covered; such an $f$ is
--   admissible in the sense of Definition 12.3 because $S(z)$ enforces (12.3).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 238, Section 12.4, Eqs. (12.3),(12.41)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- `S(z)` (Eq. 12.40): the schedules in `S` available at buffer contents `z`, i.e. satisfying
the packet availability constraint `Bs ≤ z` (Eq. 12.3). Phrased for `z : Fin I → ℝ` so the same
definition serves the discrete state (`z` cast from `Fin I → ℕ`, Lemmas 12.17-12.18, Theorem
12.16) and the fluid-scale state `Ẑ(t)` (Lemma 12.20). -/
noncomputable def feasibleSchedulesAt {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (z : Fin I → ℝ) : Finset (Fin J → ℕ) :=
  S.filter (fun s => ∀ i, (B dat).mulVec (realize s) i ≤ z i)

/-- The max-weight/back-pressure objective `z·Rs` (Eq. 12.41). -/
noncomputable def bpObjective {I J : ℕ} (dat : PacketNetworkData I J) (z : Fin I → ℝ)
    (s : Fin J → ℕ) : ℝ :=
  z ⬝ᵥ (R dat).mulVec (realize s)

/-- `s` solves the MW/BP optimization problem (12.41) at state `z`: `s ∈ S(z)` and `s` dominates
every alternative in `S(z)`. -/
def IsBPOptimal {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (z : Fin I → ℝ)
    (s : Fin J → ℕ) : Prop :=
  s ∈ feasibleSchedulesAt dat S z ∧
  ∀ s' ∈ feasibleSchedulesAt dat S z, bpObjective dat z s' ≤ bpObjective dat z s

/-- The back-pressure (max-weight) control policy, Section 12.4: a Markovian policy `f` of (12.8)
that, in each timeslot, given the observed buffer contents `z`, chooses a schedule solving (12.41).
The randomization argument `u` is carried so that every "version" of the policy (every
tie-breaking rule, deterministic or randomized, Remark 12.19) is covered; `f` is then admissible
in the sense of Definition 12.3, since `S(z)` enforces (12.3). -/
def IsBackPressurePolicy {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (f : (Fin I → ℕ) → ℝ → (Fin J → ℕ)) : Prop :=
  ∀ z : Fin I → ℕ, ∀ uu : ℝ, 0 < uu → uu < 1 → IsBPOptimal dat S (fun i => (z i : ℝ)) (f z uu)

end ProcessingNetworks.PacketNetworks


