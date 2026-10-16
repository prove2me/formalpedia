-- Prove2me | Definitions.Def_StrategicAlloc_CutChoose_Setting
-- name    : StrategicAlloc_CutChoose_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:35:49.503562+00:00
-- url     : https://prove2.me/theorems/1db64931-5016-4ec9-9be1-b6f936b2c730
-- title:
--   pp. 4–6 — additive valuations, bids, allocations, EFX, maximin share, α-MMS, best response and pure Nash equilibrium
-- statement:
--   This file fixes the model of §2 of Amanatidis et al. for $n$ agents $N=[n]$ and $m$ indivisible goods $M=\{g_1,\dots,g_m\}$.
--
--   1. **Valuations.** Each agent $i$ has a non-negative value $v_i(g)$ for every good $g$, and values bundles additively:
--   $$v_i(S)=\sum_{g\in S} v_i(g),\qquad S\subseteq M.$$
--   2. **Bids.** A bid profile $\mathbf b=(\mathbf b_1,\dots,\mathbf b_n)$ consists of non-negative reported values $b_{ij}\ge 0$, one per agent and good. The truthful bid of agent $i$ is $\mathbf b_i=(v_i(g_1),\dots,v_i(g_m))$.
--   3. **Allocations.** There is no free disposal, so an allocation $(A_1,\dots,A_n)$ is a partition of $M$: the bundles are pairwise disjoint and their union is $M$.
--   4. **EFX (Definition 2.1).** An allocation is envy-free up to any good if for all agents $i,j$ with $A_j\neq\emptyset$ and every good $g\in A_j$ with $v_i(g)>0$,
--   $$v_i(A_i)\ \ge\ v_i(A_j\setminus\{g\}).$$
--   5. **Maximin share (Definition 2.3).** The maximin share of agent $i$ is
--   $$\mu_i=\mu_i(n,M)=\max_{(A_1,\dots,A_n)\in\Pi_n(M)}\ \min_{j} v_i(A_j),$$
--   the maximum over partitions of $M$ into $n$ (possibly empty) bundles of the worst bundle's value.
--   6. **α-MMS (Definition 2.4).** An allocation is $\alpha$-MMS if $v_i(A_i)\ge \alpha\cdot\mu_i$ for every agent $i$; for $\alpha=1$ it is an MMS allocation.
--   7. **Best response and PNE (Definition 2.7).** For a mechanism $\mathcal M$ mapping bid profiles to allocations, agent $i$'s bid $\mathbf b_i$ is a best response to $\mathbf b_{-i}$ if $v_i(\mathcal M(\mathbf b'_i,\mathbf b_{-i}))\le v_i(\mathcal M(\mathbf b))$ for every $\mathbf b'_i\in\mathbb R^m_{\ge 0}$. A bid profile is a pure Nash equilibrium if every agent's bid is a best response.
--
--   These notions are the vocabulary of every statement in the mission: the mechanism reads only bids, while fairness and the agents' payoffs are measured with the true valuations.
--
--   **Formalization Note** Agents are `Fin n` and goods `Fin m`, both 0-based (agent 1 is `0`, good $g_j$ is `j-1`). Valuations and bids are real-valued functions on goods; `val v i S` is the sum over $S$, so additivity holds by construction, and non-negativity of $v$ is stated as a hypothesis in each theorem. The maximin share reuses the published `LittleCharity.MMS.mms`, a supremum over labelled maps of goods to $n$ bundles, applied to $S=M$. EFX is the paper's: only goods of positive value to $i$ are removed (unlike `LittleCharity.MMS.IsEFX`, which removes every good). Deviations in a best response range over all non-negative bid vectors. The objects of items 1–3 and 7 (`val`, `IsBidProfile`, `IsAllocation`, `IsBestResponse`, `IsPNE`) are the shared declarations of `StrategicAlloc.RRFair.Setting`, which this file imports; it declares `IsEFX`, `mu` and `IsApproxMMS`.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 4–6, §2, Definitions 2.1, 2.3, 2.4, 2.7

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.CutChoose

/-- Definition 2.1 (p. 4), EFX: for all agents `i, j` with `A_j ≠ ∅` and every good `g ∈ A_j`
with `v_i(g) > 0`, `v_i(A_j \ {g}) ≤ v_i(A_i)`. Only goods of positive value are removed. -/
def IsEFX {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, (A j).Nonempty → ∀ g ∈ A j, 0 < v i g → StrategicAlloc.RRFair.val v i ((A j).erase g) ≤ StrategicAlloc.RRFair.val v i (A i)

/-- Definition 2.3 (p. 5) with `S = M`: the maximin share `µ_i = µ_i(n, M)` of agent `i`,
the maximum over partitions of `M` into `n` bundles of the minimum bundle value. -/
noncomputable def mu {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  LittleCharity.MMS.mms (StrategicAlloc.RRFair.val v i) n Finset.univ

/-- Definition 2.4 (p. 5): `A` is `α`-MMS if `v_i(A_i) ≥ α · µ_i` for every agent `i`;
`α = 1` is an MMS allocation. -/
def IsApproxMMS {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i, α * mu v i ≤ StrategicAlloc.RRFair.val v i (A i)

end StrategicAlloc.CutChoose


