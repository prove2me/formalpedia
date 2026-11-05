-- Prove2me | Definitions.Def_SelfAdaptingFNR_DLP
-- name    : SelfAdaptingFNR_DLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:43.117212+00:00
-- url     : https://prove2.me/theorems/8b0211d8-15d2-4e32-88c7-10ace7f36e41
-- title:
--   The linear program DLP (dual of the LP formulation of the Bellman equations) and its optimal value
-- statement:
--   **(DLP)** is the network-flow program, dual to the linear-programming formulation (PLP) of the Bellman equations (1), with variables $x_t(s,a)$ for $t\in\mathcal T$, $s\in\mathcal S_t$, $a\in\mathcal A_t(s)$:
--   $$\max_x\ \sum_{t\in\mathcal T}\sum_{s\in\mathcal S_t}\sum_{a\in\mathcal A_t(s)}r_t(s,a)\,x_t(s,a)$$
--   subject to
--   1. $\sum_{a\in\mathcal A_0(s^0)}x_0(s^0,a)=1$;
--   2. $\sum_{a\in\mathcal A_t(s)}x_t(s,a)=\sum_{s'\in\mathcal S_{t-1}}\sum_{a'\in\mathcal A_{t-1}(s')}\mathbb P(s\mid s',a')\,x_{t-1}(s',a')$ for $t\in\mathcal T\setminus\{0\}$, $s\in\mathcal S_t$;
--   3. $x_t(s,a)\ge 0$.
--
--   $z^{\mathrm{DLP}}$ denotes its optimal value, the supremum of the objective over the feasible set in the extended reals.
--
--   **Formalization Note** The paper prints the right-hand summation of constraint 2 over "$s\in\mathcal S_{t-1}$, $a\in\mathcal A_{t-1}(s)$" with summand in $s',a'$; the sum runs over $s',a'$. Variables are functions of all triples; only those with $t<T$ and $a\in\mathcal A_t(s)$ appear. Constraint 1 is imposed when $T>0$. The optimal value is an `EReal` supremum ($-\infty$ for an empty feasible set).
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §2.1, p.7, (PLP)–(DLP)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_WDP

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- A **DLP variable**: `x t s a` is the joint state–action probability `x_t(s,a)`. -/
abbrev WDP.DLPVar (M : WDP J K T) : Type :=
  (t : ℕ) → ((j : Fin J) → M.S t j) → ((j : Fin J) → M.Act t j) → ℝ

/-- Feasibility for **(DLP)**, the dual of the linear-programming formulation (PLP) of the Bellman
equations (1), Nadarajah & Cire, SSRN 4081430 (Aug. 2023), §2.1, p.7:
1. `∑_{a ∈ 𝒜₀(s⁰)} x₀(s⁰, a) = 1`;
2. `∑_{a ∈ 𝒜_t(s)} x_t(s, a) = ∑_{s′ ∈ 𝒮_{t−1}} ∑_{a′ ∈ 𝒜_{t−1}(s′)} ℙ(s|s′,a′) x_{t−1}(s′,a′)` for
   `t ∈ 𝒯 ∖ {0}` and `s ∈ 𝒮_t`;
3. `x_t(s,a) ≥ 0` for `t ∈ 𝒯`, `s ∈ 𝒮_t`, `a ∈ 𝒜_t(s)`.

**Formalization Note.** The flow constraint is written for period `t + 1` with `t + 1 < T`. The
paper prints the right-hand summation indices as `s ∈ 𝒮_{t−1}`, `a ∈ 𝒜_{t−1}(s)` while the
summand is in `s′, a′`; the summation runs over `s′, a′` (typo). `x` is a function of all triples;
values outside `t < T`, `a ∈ 𝒜_t(s)` occur in no constraint and no objective, so they are the
paper's absent variables. The normalization (1) is imposed only when `0 < T` (for `T = 0` there
are no decision periods and no variables). -/
def WDP.DLPFeasible (M : WDP J K T) (x : M.DLPVar) : Prop :=
  (0 < T → ∑ a ∈ M.actionSet 0 M.s0, x 0 M.s0 a = 1) ∧
  (∀ t, t + 1 < T → ∀ s : (j : Fin J) → M.S (t + 1) j,
    ∑ a ∈ M.actionSet (t + 1) s, x (t + 1) s a =
      ∑ s' : (j : Fin J) → M.S t j, ∑ a' ∈ M.actionSet t s', M.transProb t s' a' s * x t s' a') ∧
  (∀ t, t < T → ∀ (s : (j : Fin J) → M.S t j), ∀ a ∈ M.actionSet t s, 0 ≤ x t s a)

/-- The **DLP objective** `∑_{t ∈ 𝒯} ∑_{s ∈ 𝒮_t} ∑_{a ∈ 𝒜_t(s)} r_t(s,a) x_t(s,a)` (p.7). -/
noncomputable def WDP.DLPObjective (M : WDP J K T) (x : M.DLPVar) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ s : (j : Fin J) → M.S t j, ∑ a ∈ M.actionSet t s,
    M.reward t s a * x t s a

/-- The **optimal value of DLP**, the supremum in `EReal` of the objective over the feasible set
(`⊥` if the feasible set were empty, `⊤` if the objective were unbounded). -/
noncomputable def WDP.zDLP (M : WDP J K T) : EReal :=
  sSup ((fun x => (M.DLPObjective x : EReal)) '' {x | M.DLPFeasible x})

end SelfAdaptingFNR


