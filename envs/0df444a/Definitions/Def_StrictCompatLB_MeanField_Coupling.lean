-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_Coupling
-- name    : StrictCompatLB_MeanField_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:07.290976+00:00
-- url     : https://prove2.me/theorems/66500f0a-6aa7-4ad5-904d-f59f308a33a9
-- title:
--   The optimal coupling of the G_N-system with the K_{N,M}-system (pp. 17–18) and mismatches in queue length (Def. 4.6)
-- statement:
--   The **optimal coupling** (§4.1.2) runs two systems with the same policy $\Pi$ (assignment function $p^\Pi$): the $G_N$-system, in state $z$, and the $K_{N,M}$-system on the complete bipartite graph, in state $y$. In each system order the servers by non-decreasing queue length, ties broken arbitrarily.
--
--   1. **Departures.** The potential departure epochs of the $k$-th ordered servers of the two systems are synchronised, $k=1,\dots,N$ (a departure takes place in a system only if that server is non-empty).
--   2. **Arrivals.** The arrival epochs of task type $w$ are synchronised. Let $x^w$ be the LEQD of $w$ in the $G_N$-system and $y^w$ that of the $K_{N,M}$-system (its GEQD), and $p_i=\min(p^\Pi_i(x^w),p^\Pi_i(y^w))$. One uniform variable $U\in[0,1]$ selects $I_1=i$ if
--   $$U\in\Big[\sum_{j<i}p_j,\sum_{j\le i}p_j\Big)\cup\Big[\sum_{j}p_j+\sum_{j<i}(p^\Pi_j(x^w)-p_j),\ \sum_{j}p_j+\sum_{j\le i}(p^\Pi_j(x^w)-p_j)\Big)\qquad(4.5)$$
--   and $I_2=i$ by the same rule with $y^w$ in place of $x^w$ (4.6). The task joins a server of $\mathcal N_w$ with queue length $I_1$ in the $G_N$-system and a server with queue length $I_2$ in the $K_{N,M}$-system, each uniformly at random among such servers.
--
--   At an arrival the systems **mismatch in queue length** if $I_1\ne I_2$ (Definition 4.6); $\Delta_N(t)$ counts the mismatches up to time $t$. The file also defines $\sum_{i\ge1}|Q_i(y)-Q_i(z)|$.
--
--   **Formalization Note** The coupling is described pathwise, event by event: `CoupledStep` relates the pair of states before and after one event and records the mismatch indicator. The orderings are existentially quantified permutations sorting the queue lengths, which covers every tie-breaking rule; the uniform choice of a server of the selected level is rendered as "some server of that level", which is what holds for every realisation. The sum over $i\ge1$ is finite since both $Q_i$ vanish above the longest queue.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, pp. 17–18, §4.1.2 (optimal coupling, (4.5), (4.6)); p. 18, Definition 4.6

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Finset

namespace StrictCompatLB.MeanField

/-! The optimal coupling of Rutten & Mukherjee, arXiv:2008.07562v2, §4.1.2 (pp. 17–18), of the
system on `G_N` (the `G_N`-system, state `z`) with the system on the complete bipartite graph
`K_{N,M}` (the `K_{N,M}`-system, state `y`), both under a policy with assignment function `p`,
described event by event, and the mismatch count of Definition 4.6. -/

/-- The level-selection rule (4.5)/(4.6) (p. 18): with `p_j = min(p^Π_j(x^w), p^Π_j(y^w))`
(`pm`) and the system's own assignment probabilities `p'` (`p^Π(x^w)` for the `G_N`-system,
`p^Π(y^w)` for the `K_{N,M}`-system), the value `u` of the shared uniform variable selects
level `i` if
`u ∈ [∑_{j<i} p_j, ∑_{j≤i} p_j) ∪ [∑_j p_j + ∑_{j<i}(p'_j − p_j), ∑_j p_j + ∑_{j≤i}(p'_j − p_j))`. -/
def SelectsLevel (pm p' : ℕ → ℝ) (u : ℝ) (i : ℕ) : Prop :=
  (∑ j ∈ range i, pm j ≤ u ∧ u < ∑ j ∈ range (i + 1), pm j) ∨
  ((∑' j, pm j) + ∑ j ∈ range i, (p' j - pm j) ≤ u ∧
    u < (∑' j, pm j) + ∑ j ∈ range (i + 1), (p' j - pm j))

/-- One event of the optimal coupling (pp. 17–18), taking the pair of states `(z, y)` to
`(z', y')` and recording `mis = 1` if the event is an arrival at which the two systems
**mismatch in queue length** (Definition 4.6: `I₁ ≠ I₂`) and `mis = 0` otherwise.
* **Departure.** In each system the servers are ordered by non-decreasing queue length
  (`σ₁`, `σ₂`: orderings, ties broken arbitrarily); a potential departure occurs at the `k`-th
  ordered server of both systems simultaneously (only if it is non-empty).
* **Arrival.** A task of type `w` arrives in both systems; with `x^w` the LEQD of `w` in the
  `G_N`-system and `y^w` the GEQD of the `K_{N,M}`-system (its LEQD), one value
  `u ∈ [0, 1]` selects the levels `I₁` by (4.5) and `I₂` by (4.6); the task joins a server
  `v₁ ∈ 𝒩_w` with `z_{v₁} = I₁` in the `G_N`-system and a server `v₂` with `y_{v₂} = I₂` in the
  `K_{N,M}`-system (uniformly among such servers; any of them, pathwise). -/
def CoupledStep (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (p : (ℕ → ℝ) → ℕ → ℝ) (z y z' y' : Fin N → ℕ) (mis : ℕ) : Prop :=
  (∃ σ₁ σ₂ : Fin N ≃ Fin N, Monotone (z ∘ σ₁) ∧ Monotone (y ∘ σ₂) ∧
      ∃ k : Fin N, z' = depart z (σ₁ k) ∧ y' = depart y (σ₂ k) ∧ mis = 0) ∨
  (∃ (w : Fin (M N)) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ I₁ I₂ : ℕ,
        SelectsLevel (fun j => min (p (leqd M G N z w) j) (p (geqd y) j))
          (p (leqd M G N z w)) u I₁ ∧
        SelectsLevel (fun j => min (p (leqd M G N z w) j) (p (geqd y) j))
          (p (geqd y)) u I₂ ∧
        ∃ v₁ v₂ : Fin N, v₁ ∈ nbrW M G N w ∧ z v₁ = I₁ ∧ y v₂ = I₂ ∧
          z' = arrive z v₁ ∧ y' = arrive y v₂ ∧ mis = if I₁ = I₂ then 0 else 1)

/-- `∑_{i ≥ 1} |Q_i(y) − Q_i(z)|`, a finite sum (both terms vanish above the longest queue). -/
noncomputable def occDiffSum {N : ℕ} (z y : Fin N → ℕ) : ℝ :=
  ∑ i ∈ Ico 1 (max (maxLen z) (maxLen y) + 1), |(Qcount y i : ℝ) - (Qcount z i : ℝ)|

end StrictCompatLB.MeanField


