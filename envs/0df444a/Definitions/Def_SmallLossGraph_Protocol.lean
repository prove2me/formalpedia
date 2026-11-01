-- Prove2me | Definitions.Def_SmallLossGraph_Protocol
-- name    : SmallLossGraph_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:50.606729+00:00
-- url     : https://prove2.me/theorems/dcfb9b6f-a40d-4970-bb1d-4b3ab6d6bef1
-- title:
--   Online learning with feedback graphs: closed neighbourhoods, independence bound, adaptive adversary
-- statement:
--   There are $d$ **arms** (actions) $1,\dots,d$. In every round $t$ the learner picks a distribution $w^t$ over the arms, the adversary picks a loss vector $\ell^t=(\ell^t_1,\dots,\ell^t_d)$ with every $\ell^t_i\in[0,1]$, and an arm $I(t)\sim w^t$ is drawn. Feedback is given by an undirected **feedback graph** $G^t$ on the arms, which may change from round to round and is known to the learner before it chooses $w^t$: after playing $I(t)$ the learner observes $\ell^t_j$ for every $j$ in the **closed neighbourhood**
--
--   $$
--   N^t_i=\{i\}\cup\{j : j \text{ adjacent to } i \text{ in } G^t\},\qquad i=I(t).
--   $$
--
--   This file fixes three objects shared by every statement of the mission.
--
--   1. **Closed neighbourhood** $N_i$ of arm $i$ in a graph $G$, as above.
--   2. **Independence bound.** A natural number $\alpha$ *bounds the independent sets* of $G$ if every set of pairwise non-adjacent arms has at most $\alpha$ elements, i.e. $\alpha(G)\le\alpha$ for the independence number $\alpha(G)$.
--   3. **Deterministic adaptive adversary.** A map from the list of arms $I(1),\dots,I(t-1)$ played before round $t$ to the pair $(G^t,\ell^t)$, with every loss in $[0,1]$. Graphs and losses may depend on everything that happened before round $t$, but not on the arm drawn in round $t$.
--
--   **Formalization Note** Arms are `Fin d` and graphs are `SimpleGraph (Fin d)`. Rounds are indexed from $0$: the round index is the length of the arm history. Randomized adversaries are mixtures of deterministic ones, so a high-probability bound against every deterministic adaptive adversary holds against randomized ones too.
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, §2, p.5 (protocol, losses in [0,1]); §2.1, p.5 (feedback graphs, N^t_i, α(G)); §1.2, p.4 (adaptive adversaries); Algorithm 1, p.8 (input α)

import Mathlib

open scoped BigOperators

namespace SmallLossGraph

/-- **Closed neighbourhood `N_i` of an arm in a feedback graph.**
Lykouris–Sridharan–Tardos, *Small-loss bounds for online learning with partial information*,
arXiv:1711.03639v5, §2.1, p.5: "`N^t_i` denotes the set containing arm `i` and all neighbors of
`i` in `G^t` at round `t`". Playing arm `i` reveals the losses of every arm in `N_i`.

**Formalization Note** Arms are `Fin d`; the feedback graph is an undirected `SimpleGraph (Fin d)`
(the paper's graphs are undirected, §2.1). The neighbourhood is *closed*: it contains `i` itself,
unlike Mathlib's `neighborFinset`. Adjacency is decided classically. -/
noncomputable def closedNbhd {d : ℕ} (G : SimpleGraph (Fin d)) (i : Fin d) : Finset (Fin d) :=
  open scoped Classical in Finset.univ.filter (fun j => j = i ∨ G.Adj i j)

/-- **`α` bounds the independent sets of `G`.**
arXiv:1711.03639v5, Algorithm 1, p.8: "an upper bound on the size of maximum independent sets
`α`"; §2.1, p.5: the independence number `α(G)` "is the size of the maximum subset of nodes with
no edges between them".

`IndepBound G α` says every independent set of `G` has at most `α` vertices, i.e. `α(G) ≤ α`.

**Formalization Note** The bound is stated directly on independent sets instead of through
Mathlib's `indepNum` (a supremum). For `d ≥ 1` it forces `α ≥ 1`, since a single vertex is an
independent set. -/
def IndepBound {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) : Prop :=
  ∀ s : Finset (Fin d), G.IsIndepSet (s : Set (Fin d)) → s.card ≤ α

/-- **Deterministic adaptive adversary with feedback graphs.**
arXiv:1711.03639v5, §2, p.5: on each round `t` the adversary picks losses
`ℓ^t = (ℓ^t_1, …, ℓ^t_d)` with `ℓ^t_i ∈ [0,1]`; §2.1, p.5: the undirected feedback graph `G^t`
"is allowed to vary across rounds" and is "known to the player before selecting her distribution
`w^t`"; §1.2, p.4: losses "may be adaptive to the algorithm's choices".

An adversary maps the list of arms `I(1), …, I(t−1)` played before round `t` (oldest first) to the
graph `G^t` (`graph`) and the loss vector `ℓ^t` (`loss`), with every loss in `[0,1]`.

**Formalization Note** Both `G^t` and `ℓ^t` are functions of the earlier arms only: they cannot
depend on the arm `I(t)` drawn in round `t`, but may depend on everything before it (the learner
is deterministic given the earlier arms, so the adversary may also compute `w^t`). Randomized
adversaries are mixtures of deterministic ones, so a high-probability bound that holds against
every deterministic adversary holds against randomized ones. The round index is the length of
the list (0-based). -/
structure Adversary (d : ℕ) where
  /-- The feedback graph `G^t` of the round following the arm history. -/
  graph : List (Fin d) → SimpleGraph (Fin d)
  /-- The loss vector `ℓ^t` of the round following the arm history. -/
  loss : List (Fin d) → Fin d → ℝ
  /-- Every loss lies in `[0, 1]` (§2, p.5). -/
  loss_mem : ∀ h i, loss h i ∈ Set.Icc (0 : ℝ) 1

end SmallLossGraph


