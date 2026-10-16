-- Prove2me | Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting
-- name    : StrategicAlloc_EFXTwoThirds_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T15:57:45.155543+00:00
-- url     : https://prove2.me/theorems/de8c6224-ea25-4ff4-9f10-7545ad915d02
-- title:
--   pp. 4–6, 18 — two agents with additive valuations, bids, allocations, EFX, α-MMS, PNE, and the class of always-EFX mechanisms
-- statement:
--   This definition file fixes the model of Amanatidis et al. (§2) for **two agents** and a finite set $M = \{g_1,\dots,g_m\}$ of indivisible goods, together with the class of mechanisms studied in §4.2.
--
--   1. **Additive valuations.** Each agent $i\in\{1,2\}$ has a non-negative value $v_i(g)$ for every good $g$, and values a bundle $S\subseteq M$ additively: $v_i(S)=\sum_{g\in S} v_i(g)$.
--   2. **Bids.** A bid profile $\mathbf b=(\mathbf b_1,\mathbf b_2)$ consists of non-negative bid vectors $\mathbf b_i\in\mathbb R^m_{\ge 0}$; $b_{ij}$ is the value agent $i$ claims for $g_j$.
--   3. **Allocations.** An allocation $(A_1,A_2)$ is a partition of $M$: the bundles are disjoint and every good is allocated (no free disposal).
--   4. **EFX** (Definition 2.1). $(A_1,A_2)$ is envy-free up to any good if for all agents $i,j$ with $A_j\neq\emptyset$ and every good $g\in A_j$ with $v_i(g)>0$,
--   $$v_i(A_i)\ \ge\ v_i(A_j\setminus\{g\}).$$
--   5. **Maximin share** (Definition 2.3). $\mu_i=\max_{(P_1,P_2)}\min\{v_i(P_1),v_i(P_2)\}$, the maximum over all partitions of $M$ into two bundles.
--   6. **$\alpha$-MMS** (Definition 2.4). $(A_1,A_2)$ is $\alpha$-MMS if $v_i(A_i)\ge \alpha\cdot\mu_i$ for every agent $i$.
--   7. **Best response and PNE** (Definition 2.7). For a mechanism $\mathcal M$ mapping bid profiles to allocations, $\mathbf b_i$ is a best response to $\mathbf b_{-i}$ if $v_i(\mathcal M_i(\mathbf b_i,\mathbf b_{-i}))\ge v_i(\mathcal M_i(\mathbf b'_i,\mathbf b_{-i}))$ for every $\mathbf b'_i\in\mathbb R^m_{\ge0}$; a bid profile is a pure Nash equilibrium (PNE) if every agent bids a best response. Values are always the agents' *true* valuations; the mechanism sees only the bids.
--   8. **The class of §4.2** (p. 18). A two-agent mechanism $\mathcal M$ on the goods $M$ is *always-EFX* if it allocates all goods on every bid profile, has a PNE for every valuation profile $(v_1,v_2)$ on $M$, and every PNE of every valuation profile leads to an allocation that is EFX with respect to $(v_1,v_2)$.
--
--   These are the objects in which Theorem 4.7 and its supporting claims are stated.
--
--   **Formalization Note** Agents are `Fin 2` (agent 1 is `0`), goods are `Fin m` (good $g_j$ is `j - 1`). Valuations are per-good real values `v i g`; non-negativity is a hypothesis of each theorem, and additivity holds by construction. EFX removes only goods of positive value to the envious agent, as in Definition 2.1 (unlike `LittleCharity.EFX.IsEFX`, which removes every good). The maximin share reuses the published `LittleCharity.MMS.mms` with two labelled, possibly empty, bundles. Deviations in a best response range over every non-negative bid vector.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 4–6, §2 (Definitions 2.1, 2.3, 2.4, 2.7), and p. 18, §4.2 (the class of mechanisms)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXTwoThirds

/-- Additive valuation of a bundle (p. 4): agent `i`'s value for `S` is `∑_{g ∈ S} v_i(g)`,
where `v i g` is agent `i`'s (non-negative) value for the good `g`. Agents are `Fin 2`
(agent 1 is `0`, agent 2 is `1`), goods are `Fin m` (good `g_j` is `j - 1`). -/
def val {m : ℕ} (v : Fin 2 → Fin m → ℝ) (i : Fin 2) (S : Finset (Fin m)) : ℝ :=
  ∑ g ∈ S, v i g

/-- A bid profile (p. 5): every agent reports a non-negative bid `b i g = b_{ij}` for every good. -/
def IsBidProfile {m : ℕ} (b : Fin 2 → Fin m → ℝ) : Prop :=
  ∀ i g, 0 ≤ b i g

/-- An allocation (p. 4, no free disposal): the bundles are pairwise disjoint and cover all goods. -/
def IsAllocation {m : ℕ} (A : Fin 2 → Finset (Fin m)) : Prop :=
  Pairwise (fun i j => Disjoint (A i) (A j)) ∧ Finset.univ.biUnion A = Finset.univ

/-- Envy-freeness up to any good (Definition 2.1, p. 4): for all agents `i, j` with `A_j ≠ ∅`,
`v_i(A_i) ≥ v_i(A_j \ {g})` for every good `g ∈ A_j` with `v_i(g) > 0`.
Only goods of positive value to `i` are removed. -/
def IsEFX {m : ℕ} (v : Fin 2 → Fin m → ℝ) (A : Fin 2 → Finset (Fin m)) : Prop :=
  ∀ i j, (A j).Nonempty → ∀ g ∈ A j, 0 < v i g → val v i ((A j).erase g) ≤ val v i (A i)

/-- Best response (Definition 2.7, p. 6): no non-negative bid vector `b'` of agent `i` gives her,
by her true valuation `v_i`, a strictly better bundle than `b_i` does against `b_{-i}`. -/
def IsBestResponse {m : ℕ} (mech : (Fin 2 → Fin m → ℝ) → Fin 2 → Finset (Fin m))
    (v : Fin 2 → Fin m → ℝ) (b : Fin 2 → Fin m → ℝ) (i : Fin 2) : Prop :=
  ∀ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) →
    val v i (mech (Function.update b i b') i) ≤ val v i (mech b i)

/-- Pure Nash equilibrium (Definition 2.7, p. 6): a bid profile in which every agent's bid
vector is a best response to the others'. -/
def IsPNE {m : ℕ} (mech : (Fin 2 → Fin m → ℝ) → Fin 2 → Finset (Fin m))
    (v : Fin 2 → Fin m → ℝ) (b : Fin 2 → Fin m → ℝ) : Prop :=
  IsBidProfile b ∧ ∀ i, IsBestResponse mech v b i

/-- The class of Theorems 4.5 and 4.7 (pp. 18–20), on a fixed set of goods `Fin m`:
it allocates all goods on every bid profile, has a PNE for every valuation profile, and
every PNE of every valuation profile leads to an EFX allocation (Definition 2.1, w.r.t. v). -/
def IsAlwaysEFXMechanism {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m) : Prop :=
  (∀ b, IsBidProfile b → IsAllocation (M b)) ∧
  ∀ v : Fin 2 → Fin m → ℝ, (∀ i g, 0 ≤ v i g) →
    (∃ b, IsPNE M v b) ∧ ∀ b, IsPNE M v b → IsEFX v (M b)

end StrategicAlloc.EFXTwoThirds


