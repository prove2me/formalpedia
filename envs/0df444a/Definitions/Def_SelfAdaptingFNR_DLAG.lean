-- Prove2me | Definitions.Def_SelfAdaptingFNR_DLAG
-- name    : SelfAdaptingFNR_DLAG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:46.065782+00:00
-- url     : https://prove2.me/theorems/bf66ae0b-8713-443f-9d96-900d14289771
-- title:
--   The Lagrangian flow program D-LAG and $z^{\mathrm{LAG}}$
-- statement:
--   **(D-LAG)** has variables $x_{t,j}(s_j,a_j)$ for $t\in\mathcal T$, $j\in\mathcal J$, $s_j\in\mathcal S_{t,j}$, $a_j\in\mathcal A_{t,j}(s_j)$:
--   $$\max_x\ \sum_{t\in\mathcal T}\sum_{j\in\mathcal J}\sum_{s_j\in\mathcal S_{t,j}}\sum_{a_j\in\mathcal A_{t,j}(s_j)}r_{t,j}(s_j,a_j)\,x_{t,j}(s_j,a_j)$$
--   subject to
--   1. (7) $\sum_{a_j\in\mathcal A_{0,j}(s^0_j)}x_{0,j}(s^0_j,a_j)=1$ for all $j$;
--   2. (8) $\sum_{a_j\in\mathcal A_{t,j}(s_j)}x_{t,j}(s_j,a_j)=\sum_{s_j'\in\mathcal S_{t-1,j}}\sum_{a_j'\in\mathcal A_{t-1,j}(s_j')}\mathbb P(s_j\mid s_j',a_j')\,x_{t-1,j}(s_j',a_j')$ for $t\in\mathcal T\setminus\{0\}$, all $j$, $s_j$;
--   3. (9) $\sum_{j}\sum_{s_j}\sum_{a_j\in\mathcal A_{t,j}(s_j)}x_{t,j}(s_j,a_j)\,C_{t,k,j}(s_j,a_j)\le b_k$ for $t\in\mathcal T$, $k\in\mathcal K$;
--   4. (10) $x\ge 0$.
--
--   Constraints (7), (8), (10) are the **component flow constraints**, shared with FNR. $z^{\mathrm{LAG}}$ is the optimal value of D-LAG. In D-LAG the linking constraints hold only on average, through (9).
--
--   **Formalization Note** (8) is written for period $t+1$ with $t+1<T$, and (7) is imposed when $T>0$. Variables are functions of all quadruples; only those with $t<T$ and $a_j\in\mathcal A_{t,j}(s_j)$ appear. $z^{\mathrm{LAG}}$ is an `EReal` supremum; the paper defines it as the optimal value of D-LAG or of its dual LAG.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §2.3, p.10, (D-LAG), (7)–(10); §4.1, p.17 (definition of $z^{\mathrm{LAG}}$)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_WDP

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- A **component flow variable** `x t j sⱼ aⱼ = x_{t,j}(sⱼ,aⱼ)`, used by D-LAG and FNR. -/
abbrev WDP.FlowVar (M : WDP J K T) : Type :=
  (t : ℕ) → (j : Fin J) → M.S t j → M.Act t j → ℝ

/-- The **component flow constraints (7), (8), (10)** of D-LAG (Nadarajah & Cire, SSRN 4081430,
Aug. 2023, §2.3, p.10), shared by FNR as its constraint (17):
* (7) `∑_{aⱼ ∈ 𝒜_{0,j}(s⁰ⱼ)} x_{0,j}(s⁰ⱼ, aⱼ) = 1` for every `j`;
* (8) `∑_{aⱼ ∈ 𝒜_{t,j}(sⱼ)} x_{t,j}(sⱼ,aⱼ) = ∑_{s′ⱼ ∈ 𝒮_{t−1,j}} ∑_{a′ⱼ ∈ 𝒜_{t−1,j}(s′ⱼ)}
  ℙ(sⱼ|s′ⱼ,a′ⱼ) x_{t−1,j}(s′ⱼ,a′ⱼ)` for `t ∈ 𝒯 ∖ {0}`, every `j` and `sⱼ`;
* (10) `x ≥ 0`.

**Formalization Note.** (8) is written for period `t + 1` with `t + 1 < T`; (7) is imposed when
`0 < T`. Variables exist for every `(t, j, sⱼ, aⱼ)`, but only those with `t < T` and
`aⱼ ∈ 𝒜_{t,j}(sⱼ)` (the paper's variables) occur in any constraint or objective; (10) is imposed
on exactly those. -/
def WDP.FlowConstraints (M : WDP J K T) (x : M.FlowVar) : Prop :=
  (0 < T → ∀ j, ∑ a ∈ M.A 0 j (M.s0 j), x 0 j (M.s0 j) a = 1) ∧
  (∀ t, t + 1 < T → ∀ j (s : M.S (t + 1) j),
    ∑ a ∈ M.A (t + 1) j s, x (t + 1) j s a =
      ∑ s' : M.S t j, ∑ a' ∈ M.A t j s', M.P t j s' a' s * x t j s' a') ∧
  (∀ t, t < T → ∀ j (s : M.S t j), ∀ a ∈ M.A t j s, 0 ≤ x t j s a)

/-- Feasibility for **(D-LAG)** (p.10): the flow constraints (7), (8), (10) and the averaged
linking constraints (9)
`∑ⱼ ∑_{sⱼ ∈ 𝒮_{t,j}} ∑_{aⱼ ∈ 𝒜_{t,j}(sⱼ)} x_{t,j}(sⱼ,aⱼ) C_{t,k,j}(sⱼ,aⱼ) ≤ b_k` for `t ∈ 𝒯`,
`k ∈ 𝒦`. -/
def WDP.DLAGFeasible (M : WDP J K T) (x : M.FlowVar) : Prop :=
  M.FlowConstraints x ∧
  ∀ t, t < T → ∀ k, ∑ j, ∑ s : M.S t j, ∑ a ∈ M.A t j s, x t j s a * M.C t k j s a ≤ M.b k

/-- The common objective of **D-LAG and FNR**,
`∑_{t ∈ 𝒯} ∑ⱼ ∑_{sⱼ ∈ 𝒮_{t,j}} ∑_{aⱼ ∈ 𝒜_{t,j}(sⱼ)} r_{t,j}(sⱼ,aⱼ) x_{t,j}(sⱼ,aⱼ)` (pp.10, 17). -/
noncomputable def WDP.flowObjective (M : WDP J K T) (x : M.FlowVar) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ j, ∑ s : M.S t j, ∑ a ∈ M.A t j s, M.r t j s a * x t j s a

/-- `z^LAG`, the **optimal value of D-LAG** (p.17: "Let `z^LAG` and `z^FNR` denote the optimal
objective values of D-LAG (or LAG) and FNR"), the supremum in `EReal` of the objective over the
D-LAG feasible set. -/
noncomputable def WDP.zLAG (M : WDP J K T) : EReal :=
  sSup ((fun x => (M.flowObjective x : EReal)) '' {x | M.DLAGFeasible x})

end SelfAdaptingFNR


