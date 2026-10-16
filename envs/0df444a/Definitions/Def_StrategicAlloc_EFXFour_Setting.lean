-- Prove2me | Definitions.Def_StrategicAlloc_EFXFour_Setting
-- name    : StrategicAlloc_EFXFour_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T14:14:11.753136+00:00
-- url     : https://prove2.me/theorems/da5352ed-4dda-4cc3-b646-a7aede8aae0e
-- title:
--   pp. 4–6, 18, 20 — additive valuations, bids, allocations, EFX, maximin share, α-MMS, PNE, the class of always-EFX mechanisms, v∗
-- statement:
--   This file fixes the model of §2 of the paper for **two agents** and introduces the class of mechanisms studied in §4.2.
--
--   **Instance.** There are agents $1, 2$ and a finite set $M = \{g_1, \dots, g_m\}$ of indivisible goods. Agent $i$ has a non-negative value $v_i(g)$ for every good $g$, and values bundles additively:
--   $$
--   v_i(S) = \sum_{g \in S} v_i(g), \qquad S \subseteq M.
--   $$
--   An **allocation** $(A_1, A_2)$ is a partition of $M$: the bundles are disjoint and every good is allocated (no free disposal).
--
--   **Fairness (Definitions 2.1, 2.3, 2.4).**
--   1. An allocation is **EFX** (envy-free up to any good) if for every pair of agents $i, j$ with $A_j \neq \emptyset$ and every good $g \in A_j$ with $v_i(g) > 0$, we have $v_i(A_i) \ge v_i(A_j \setminus \{g\})$. It is **EFX from the point of view of agent $i$** if this holds for that fixed $i$ and every $j$.
--   2. The **maximin share** of agent $i$ is
--   $$
--   \mu_i = \max_{(X_1, X_2)} \min\{v_i(X_1), v_i(X_2)\},
--   $$
--   the maximum over all partitions of $M$ into two (possibly empty) bundles.
--   3. An allocation is **$\alpha$-MMS** if $v_i(A_i) \ge \alpha \cdot \mu_i$ for both agents; for $\alpha = 1$ it is an **MMS allocation**.
--
--   **Mechanisms and equilibria (§2.2, Definition 2.7).** Each agent reports a bid vector $\mathbf b_i \in \mathbb R^m_{\ge 0}$; a mechanism $\mathcal M$ maps a bid profile $\mathbf b = (\mathbf b_1, \mathbf b_2)$ to an allocation $\mathcal M(\mathbf b)$. A bid $\mathbf b_i$ is a **best response** to $\mathbf b_{-i}$ if $v_i(\mathcal M(\mathbf b_i', \mathbf b_{-i})) \le v_i(\mathcal M(\mathbf b))$ for every $\mathbf b_i' \in \mathbb R^m_{\ge 0}$, and $\mathbf b$ is a **pure Nash equilibrium (PNE)** if every agent's bid is a best response. Equilibria are judged with the true values $v_i$, while the mechanism sees only bids.
--
--   **The class of §4.2.** A two-agent mechanism on the goods $M$ is **always EFX** if it allocates all goods on every bid profile, has a PNE for every valuation profile $(v_1, v_2)$ on $M$, and every PNE of every such profile yields an EFX allocation with respect to $(v_1, v_2)$.
--
--   **The auxiliary valuation $v^*$ (p. 20)** on four goods $h_1, \dots, h_4$:
--   $$
--   v^*(h_1) = 1.2, \quad v^*(h_2) = v^*(h_3) = 1, \quad v^*(h_4) = 0.1.
--   $$
--
--   These objects are the vocabulary of Theorem 4.5 and its supporting lemmas: an always-EFX mechanism is the hypothesis, and MMS for the equilibrium allocation is the conclusion.
--
--   **Formalization Note** Agents are `Fin 2` and goods `Fin m`, both 0-based (agent $1$ is `0`, good $h_j$ of $v^*$ is `j - 1`). Valuations are per-good values `v i g : ℝ`; bundle values are sums, so additivity holds by construction, and non-negativity is a hypothesis wherever it is needed. The maximin share reuses the published `LittleCharity.MMS.mms` with two labelled bundles. EFX removes only goods of positive value, exactly as in Definition 2.1 (the published `LittleCharity.EFX.IsEFX`, which removes every good, is a different notion and is not used). Deviations in a best response range over all non-negative bid vectors. `val`, `IsBidProfile`, `IsAllocation`, `IsBestResponse`, `IsPNE` (from `StrategicAlloc.RRFair.Setting`) and `IsEFX` (from `StrategicAlloc.CutChoose.Setting`) are imported and stated for any number of agents; this file declares `IsEFXFor` (any number of agents), `mu`, `IsApproxMMS`, `Mechanism`, `IsAlwaysEFXMechanism` (two agents) and `vstar`.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 4–6 (§2, Definitions 2.1, 2.3, 2.4, 2.7), p. 18 (§4.2, the class of mechanisms), p. 20 (proof of Theorem 4.5, v∗)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.EFXFour

/-- EFX "from the point of view" of agent `i` (Lemma 4.4, p. 19): the EFX condition of
Definition 2.1 with the envying agent fixed to `i`. -/
def IsEFXFor {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  ∀ j, (A j).Nonempty → ∀ g ∈ A j, 0 < v i g → StrategicAlloc.RRFair.val v i ((A j).erase g) ≤ StrategicAlloc.RRFair.val v i (A i)

/-- The maximin share `µ_i = µ_i(2, M)` of agent `i` with two agents (Definition 2.3, p. 5),
via the published `LittleCharity.MMS.mms`: the maximum over partitions of `M` into two labelled,
possibly empty, bundles of the smaller bundle value. -/
noncomputable def mu {m : ℕ} (v : Fin 2 → Fin m → ℝ) (i : Fin 2) : ℝ :=
  LittleCharity.MMS.mms (StrategicAlloc.RRFair.val v i) 2 Finset.univ

/-- α-MMS (Definition 2.4, p. 5) for two agents: `v_i(A_i) ≥ α · µ_i` for every agent `i`.
MMS is `α = 1`. -/
def IsApproxMMS {m : ℕ} (α : ℝ) (v : Fin 2 → Fin m → ℝ) (A : Fin 2 → Finset (Fin m)) : Prop :=
  ∀ i, α * mu v i ≤ StrategicAlloc.RRFair.val v i (A i)

/-- A deterministic two-agent mechanism on the goods `Fin m` (p. 5): bid profile ↦ bundles. -/
abbrev Mechanism (m : ℕ) := (Fin 2 → Fin m → ℝ) → Fin 2 → Finset (Fin m)

/-- The class of Theorems 4.5 and 4.7 (p. 18), on a fixed set of goods `Fin m`: the mechanism
allocates all goods on every bid profile (p. 5), has a PNE for every valuation profile, and every
PNE of every valuation profile leads to an EFX allocation (Definition 2.1, w.r.t. `v`). -/
def IsAlwaysEFXMechanism {m : ℕ} (M : Mechanism m) : Prop :=
  (∀ b, StrategicAlloc.RRFair.IsBidProfile b → StrategicAlloc.RRFair.IsAllocation (M b)) ∧
  ∀ v : Fin 2 → Fin m → ℝ, (∀ i g, 0 ≤ v i g) →
    (∃ b, StrategicAlloc.RRFair.IsPNE M v b) ∧ ∀ b, StrategicAlloc.RRFair.IsPNE M v b → StrategicAlloc.CutChoose.IsEFX v (M b)

/-- The auxiliary valuation `v∗` of the proof of Theorem 4.5 (p. 20) on the goods
`h_1, h_2, h_3, h_4` (here `0, 1, 2, 3`): `v∗(h_1) = 1.2`, `v∗(h_2) = v∗(h_3) = 1`,
`v∗(h_4) = 0.1`. -/
noncomputable def vstar : Fin 4 → ℝ := ![6 / 5, 1, 1, 1 / 10]

end StrategicAlloc.EFXFour


