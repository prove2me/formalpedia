-- Prove2me | Definitions.Def_LocalSearchFL_MultiSwap_kmCost
-- name    : LocalSearchFL_MultiSwap_kmCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:36:34.467988+00:00
-- url     : https://prove2.me/theorems/0bf6e798-c436-48de-b498-63b3c4b2cb63
-- title:
--   k-median cost and local optimality for the p-swap neighbourhood (3)
-- statement:
--   Fix a metric instance with clients $C$, facilities $F$ and service costs $c_{ji}$.
--
--   1. **k-median cost.** For a nonempty set $S \subseteq F$ of open facilities, every client is served by its nearest open facility, and
--   $$\mathrm{cost}(S) = \sum_{j \in C} \min_{i \in S} c_{ji}.$$
--   2. **p-swap local optimality.** For an integer $p$, a swap $\langle A, B\rangle$ deletes a set $A \subseteq S$ of at most $p$ facilities and adds a set $B \subseteq F$ with $|B| = |A|$. The neighbourhood of $S$ is
--   $$\mathcal B(S) = \{(S \setminus A) \cup B \mid A \subseteq S,\ B \subseteq F,\ |A| = |B| \le p\},$$
--   and $S$ is **locally optimum** if $\mathrm{cost}(S) \le \mathrm{cost}(S')$ for every $S' \in \mathcal B(S)$.
--
--   These are the objects of the mission's goal: the cost that local search minimizes and the stopping condition of the $p$-swap local search.
--
--   **Formalization Note** The cost is defined only for nonempty $S$ (a nonemptiness proof is an argument), so no junk value is attached to the empty set. The set $B$ may meet $S$, exactly as in (3). Local optimality quantifies over a proof that the neighbour $(S\setminus A)\cup B$ is nonempty; when $S$ is nonempty every neighbour is nonempty ($A = S$ forces $|B| = |S| \ge 1$), so this restricts nothing.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 547 (local optimality), p. 548 (§3, cost), p. 551 (§3.3, eq. (3))

import Mathlib
import Definitions.Def_LocalSearchFL_Shared_MetricInstance

namespace LocalSearchFL.MultiSwap

/-- The **k-median cost** of a nonempty set `S` of open facilities (p. 548, §3):
`cost(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}`, every client being served by its nearest open
facility. Only nonempty `S` have a cost. -/
noncomputable def kmCost {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- **Local optimality for p-swaps** (p. 547 and §3.3, eq. (3), p. 551): `S` is locally optimum
for the neighbourhood `B(S) = {(S \ A) ∪ B | A ⊆ S, B ⊆ F, |A| = |B| ≤ p}`, i.e. no swap `⟨A, B⟩`
deleting a set `A ⊆ S` of at most `p` facilities and adding a set `B` of `|A|` facilities
decreases the cost. (`B` may meet `S`.) Whenever `S` is nonempty every such neighbour is
nonempty, so the quantifier over its nonemptiness proof `h` restricts nothing. -/
def IsPSwapLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (p : ℕ) (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  ∀ A : Finset Fa, A ⊆ S → ∀ B : Finset Fa, A.card = B.card → A.card ≤ p →
    ∀ h : ((S \ A) ∪ B).Nonempty, kmCost I S hS ≤ kmCost I ((S \ A) ∪ B) h

end LocalSearchFL.MultiSwap


