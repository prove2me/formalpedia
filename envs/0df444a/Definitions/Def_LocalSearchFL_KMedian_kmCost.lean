-- Prove2me | Definitions.Def_LocalSearchFL_KMedian_kmCost
-- name    : LocalSearchFL_KMedian_kmCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:09:15.323988+00:00
-- url     : https://prove2.me/theorems/f9532f91-31c1-4500-80ac-4f8853b706c2
-- title:
--   k-median cost, single-swap local optimality, nearest-facility assignments and neighbourhoods $N_A(a)$
-- statement:
--   Fix a metric instance with clients $C$, facilities $F$ and service costs $c_{ji}$.
--
--   1. **k-median cost.** For a nonempty set $S \subseteq F$ of open facilities, every client is served by its nearest open facility, and
--   $$\mathrm{cost}(S) = \sum_{j \in C} \min_{i \in S} c_{ji}.$$
--   2. **Single-swap local optimality.** A swap $\langle s, s' \rangle$ closes a facility $s \in S$ and opens a facility $s' \notin S$, producing $S - s + s' = (S \setminus \{s\}) \cup \{s'\}$. The neighbourhood of $S$ is $\mathcal B(S) = \{S - \{s\} + \{s'\} \mid s \in S,\ s' \notin S\}$, and $S$ is **locally optimum** if
--   $$\mathrm{cost}(S) \le \mathrm{cost}(S - s + s') \quad \text{for all } s \in S,\ s' \in F \setminus S.$$
--   3. **Nearest-facility assignment.** A map $\sigma : C \to F$ is a nearest-facility assignment for a solution $A \subseteq F$ if $\sigma(j) \in A$ and $c_{j\sigma(j)} \le c_{ji}$ for all $i \in A$; ties are broken arbitrarily. The **service cost** of $j$ in $A$ is then $A_j = c_{j\sigma(j)}$.
--   4. **Neighbourhood of a facility.** For an assignment $\sigma$ and a facility $a$, $N_A(a) = \{ j \in C : \sigma(j) = a\}$ is the set of clients that $a$ serves.
--
--   These are the objects of Theorem 3.2 (the cost and the local optimality) and the notation of its proof (service costs $S_j, O_j$ and the sets $N_S(s), N_O(o)$).
--
--   **Formalization Note** The cost is defined only for nonempty $S$ (a proof of nonemptiness is an argument), so no junk value is assigned to the empty solution. $N_A(a)$ is defined from an arbitrary map $\sigma : C \to F$; the statements that use it add the hypothesis that $\sigma$ is a nearest-facility assignment where the paper needs it.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 547 (locally optimum solution), p. 548 (notation A_j, N_A(a); §3 cost; §3.1 neighbourhood B(S))

import Mathlib
import Definitions.Def_LocalSearchFL_Shared_MetricInstance

namespace LocalSearchFL.KMedian

/-- The **k-median cost** of a nonempty set `S` of open facilities (p. 548, §3):
`cost(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}`, every client being served by its nearest open
facility. Only nonempty `S` have a cost. -/
noncomputable def kmCost {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- **Local optimality for single swaps** (p. 547 and §3.1, p. 548): `S` is locally optimum for
the neighbourhood `B(S) = {S − {s} + {s'} | s ∈ S}`, `s' ∉ S`, i.e. no single swap `⟨s, s'⟩`
closing `s ∈ S` and opening `s' ∉ S` decreases the cost. -/
def IsSwapLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  ∀ s ∈ S, ∀ s' : Fa, s' ∉ S →
    kmCost I S hS ≤ kmCost I (insert s' (S.erase s)) (Finset.insert_nonempty s' (S.erase s))

/-- `σ` is a **nearest-facility assignment** for the solution `A` (p. 548): every client `j` is
assigned a facility `σ j ∈ A` at minimum distance from `j` among the facilities of `A`
(ties broken arbitrarily). Then `c_{j σ(j)}` is the service cost `A_j` of `j` in `A`. -/
def IsNearestAssignment {Cl Fa : Type} (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (A : Finset Fa)
    (σ : Cl → Fa) : Prop :=
  ∀ j, σ j ∈ A ∧ ∀ i ∈ A, I.c j (σ j) ≤ I.c j i

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` (p. 548): the set
of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

end LocalSearchFL.KMedian


