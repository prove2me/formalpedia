-- Prove2me | Definitions.Def_GenericBudgets_MaximinShare_Setting
-- name    : GenericBudgets_MaximinShare_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:09.332+00:00
-- url     : https://prove2.me/theorems/34057613-89fa-4c07-be92-b5a4c506e29c
-- title:
--   Definitions 2.1, 2.3, and 3.1 — allocations, equilibrium, and maximin share
-- statement:
--   Let $M$ be a finite set of indivisible items and $N$ a finite set of agents. A **bundle** is a subset of $M$. An **allocation** assigns every item to exactly one agent; $S_i$ denotes agent $i$'s bundle. For item prices $p_j$, write $p(S)=\sum_{j\in S}p_j$. A bundle $S$ is **demanded** by an agent with valuation $v_i$ and budget $b_i$ when $p(S)\le b_i$ and every strictly preferred bundle costs more than $b_i$. A **competitive equilibrium** is an allocation with nonnegative item prices at which each allocated bundle is demanded. An allocation is **Pareto optimal**, in the paper's strict formulation, when every different allocation makes some agent strictly worse off.
--
--   For integers $d>0$ and $0\le\ell\le d$, an agent partitions the items into $d$ labeled parts, which may be empty. She can retain any $\ell$ parts after an adversary chooses the rest. Her **$\ell$-out-of-$d$ maximin share** is
--
--   $$
--   \max_{(T_1,\ldots,T_d)}\;\min_{L\subseteq[d],\,|L|=\ell}\;v_i\!\left(\bigcup_{t\in L}T_t\right).
--   $$
--
--   An allocation guarantees this share when $v_i(S_i)$ is at least that number (Definition 3.1). This benchmark is used to express the fairness consequence of equilibrium without requiring additive preferences.
--
--   **Formalization Note** Agents and items are `Fin n` and `Fin m`; an allocation is a total function from items to agents, so it clears the market. A partition is likewise a total function from items to part labels. The Lean guarantee uses the equivalent condition that for each partition there is a choice of exactly $\ell$ parts whose value is at most $v_i(S_i)$; a separate sanity theorem checks the equivalence for $d>0$ and $\ell\le d$. Valuations are arbitrary real-valued functions on bundles; the standing assumptions of §2.1 (additivity, normalization, nonnegativity, monotonicity, strictness) are not built into the definitions and are added as hypotheses only where a theorem uses them.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, pp. 6–7, §2.1–2.2, Definitions 2.1 and 2.3; p. 9, Definition 3.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.MaximinShare

/-- The items allocated to agent `i` by the allocation `σ`. -/
def bundle {n m : ℕ} (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => σ j = i)

/-- Definition 2.1: nonnegative item prices and demand for every agent's allocated bundle. -/
def IsCE {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ)
    (σ : Fin m → Fin n) (p : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∀ i, GenericBudgets.AlmostEqual.IsDemanded (v i) (b i) p (bundle σ i)

/-- Definition 2.3: every different allocation makes some agent strictly worse off. -/
def IsPO {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (σ : Fin m → Fin n) : Prop :=
  ∀ σ', σ' ≠ σ → ∃ i, v i (bundle σ' i) < v i (bundle σ i)

/-- The union of the parts with indices in `L` of a partition `T`. -/
def partsUnion {m d : ℕ} (T : Fin m → Fin d) (L : Finset (Fin d)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => T j ∈ L)

/-- Definition 3.1: for every partition, some choice of exactly `ℓ` parts is no better
than the agent's allocated bundle. For `0 < d` and `ℓ ≤ d`, this is the paper's
maximum-over-partitions, minimum-over-choices comparison. -/
def GuaranteesMMS {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (σ : Fin m → Fin n) (i : Fin n) (ℓ d : ℕ) : Prop :=
  ∀ T : Fin m → Fin d, ∃ L : Finset (Fin d),
    L.card = ℓ ∧ v i (partsUnion T L) ≤ v i (bundle σ i)

end GenericBudgets.MaximinShare


