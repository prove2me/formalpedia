-- Prove2me | Definitions.Def_LocalSearchFL_UFL_uflCost
-- name    : LocalSearchFL_UFL_uflCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:14:05.930073+00:00
-- url     : https://prove2.me/theorems/cc2a344f-bd2b-4a92-8f5c-3891c1afd095
-- title:
--   UFL cost, add/drop/swap local optimality, nearest-facility assignments and neighbourhoods $N_A(a)$
-- statement:
--   Fix a metric instance with clients $C$, facilities $F$ and service costs $c_{ji}$, and opening costs $f_i$ for $i \in F$.
--
--   1. **Facility, service and total cost.** For a nonempty set $S \subseteq F$ of open facilities,
--   $$\mathrm{cost}_f(S) = \sum_{i \in S} f_i, \qquad \mathrm{cost}_s(S) = \sum_{j \in C} \min_{i \in S} c_{ji}, \qquad \mathrm{cost}(S) = \mathrm{cost}_f(S) + \mathrm{cost}_s(S),$$
--   every client being served by its nearest open facility.
--   2. **Add/drop/swap local optimality.** The neighbourhood of $S$ is
--   $$\mathcal B(S) = \{S + \{s'\}\} \cup \{S - \{s\} \mid s \in S\} \cup \{S - \{s\} + \{s'\} \mid s \in S\},$$
--   and $S$ is **locally optimum** if $\mathrm{cost}(S) \le \mathrm{cost}(S')$ for every $S' \in \mathcal B(S)$: for every facility $s' \in F$, $\mathrm{cost}(S) \le \mathrm{cost}(S \cup \{s'\})$; for every $s \in S$ with $S \setminus \{s\} \neq \emptyset$, $\mathrm{cost}(S) \le \mathrm{cost}(S \setminus \{s\})$; and for every $s \in S$ and $s' \in F$, $\mathrm{cost}(S) \le \mathrm{cost}((S \setminus \{s\}) \cup \{s'\})$.
--   3. **Nearest-facility assignment.** A map $\sigma : C \to F$ is a nearest-facility assignment for a solution $A$ if $\sigma(j) \in A$ and $c_{j\sigma(j)} \le c_{ji}$ for all $i \in A$; ties are broken arbitrarily. The service cost of $j$ in $A$ is then $A_j = c_{j\sigma(j)}$.
--   4. **Neighbourhood of a facility.** For an assignment $\sigma$ and a facility $a$, $N_A(a) = \{ j \in C : \sigma(j) = a\}$ is the set of clients that $a$ serves.
--
--   These are the objects of Theorem 4.3 (the cost and the local optimality) and the notation of the proofs of Lemmas 4.1 and 4.2 ($S_j$, $O_j$, $N_S(s)$, $N_O(o)$).
--
--   **Formalization Note** Only nonempty sets have a cost: the service cost of $\emptyset$ is not defined (it cannot serve any client), so no junk value enters. Accordingly the drop move is only considered when a facility remains open. Adding a facility already in $S$, or swapping $s$ for a facility already in $S$ (or for $s$ itself), are allowed in the Lean predicate; these extra "moves" give neighbours that are $S$ itself or a drop neighbour of $S$, so they add no condition beyond the paper's neighbourhood (4).
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 547 (§2, local optimality), p. 548 (N_S(s), S_j), p. 554 (§4 cost, §4.1 eq. (4), §4.2 cost_f, cost_s)

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_MetricInstance

namespace LocalSearchFL.UFL

/-- The **facility cost** `cost_f(S) = ∑_{i ∈ S} f_i` of a set `S` of open facilities
(§4.2, p. 554). -/
def costF {Fa : Type} (f : Fa → ℝ) (S : Finset Fa) : ℝ :=
  ∑ i ∈ S, f i

/-- The **service cost** `cost_s(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}` of a nonempty set `S` of open
facilities (§4.2, p. 554): every client is served by its nearest open facility. Only nonempty `S`
have a service cost. -/
noncomputable def costS {Cl Fa : Type} [Fintype Cl] (I : MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- The **UFL cost** `cost(S) = cost_f(S) + cost_s(S)` of a nonempty set `S` of open facilities
(§4, p. 554). -/
noncomputable def uflCost {Cl Fa : Type} [Fintype Cl] (I : MetricInstance Cl Fa) (f : Fa → ℝ)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  costF f S + costS I S hS

/-- **Local optimality for the add/drop/swap neighbourhood** (4) of §4.1, p. 554:
`B(S) = {S + {s'}} ∪ {S − {s} | s ∈ S} ∪ {S − {s} + {s'} | s ∈ S}`. The nonempty set `S` is
locally optimum if no neighbour has smaller cost: adding any facility `s'`, dropping any `s ∈ S`
(when a facility remains open), or swapping any `s ∈ S` for any facility `s'`. -/
def IsUFLLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : MetricInstance Cl Fa)
    (f : Fa → ℝ) (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  (∀ s' : Fa, uflCost I f S hS ≤ uflCost I f (insert s' S) (Finset.insert_nonempty s' S)) ∧
  (∀ s ∈ S, ∀ h : (S.erase s).Nonempty, uflCost I f S hS ≤ uflCost I f (S.erase s) h) ∧
  (∀ s ∈ S, ∀ s' : Fa,
    uflCost I f S hS ≤ uflCost I f (insert s' (S.erase s)) (Finset.insert_nonempty s' (S.erase s)))

/-- `σ` is a **nearest-facility assignment** for the solution `A` (p. 548): every client `j` is
assigned a facility `σ j ∈ A` at minimum distance from `j` among the facilities of `A`
(ties broken arbitrarily). Then `c_{j σ(j)}` is the service cost `A_j` of `j` in `A`. -/
def IsNearestAssignment {Cl Fa : Type} (I : MetricInstance Cl Fa) (A : Finset Fa)
    (σ : Cl → Fa) : Prop :=
  ∀ j, σ j ∈ A ∧ ∀ i ∈ A, I.c j (σ j) ≤ I.c j i

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` (p. 548): the set
of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

end LocalSearchFL.UFL


