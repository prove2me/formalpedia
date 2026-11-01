-- Prove2me | Definitions.Def_GreedyReusableNet_IndepSystemAssumption
-- name    : GreedyReusableNet_IndepSystemAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:46.332216+00:00
-- url     : https://prove2.me/theorems/40aaac8e-7b19-42e8-b76b-bc14e83184d3
-- title:
--   Assumption 1 (Independence System)
-- statement:
--   **Assumption 1.** For every period $t<T$: the family $\mathscr A_t$ of action sets is an **independence system** over the basis $\mathcal B_t$, that is, $\emptyset\in\mathscr A_t$, every subset of a member of $\mathscr A_t$ is a member, and every action set consists of bundles of $\mathcal B_t$; and every bundle $B\in\mathcal B_t$ has at most $L$ arms, $|B|\le L$.
--
--   Downward closure is what lets a policy drop bundles from an action set (for instance those below a reward threshold) and still take a feasible action; $L$ is the network size that appears in every competitive ratio of the paper.
--
--   **Formalization Note** Uses the published predicate `SubsamplingSM.Offline.IsIndepSystem` ($\emptyset$ feasible, downward closed). Periods are $0$-based.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 1, p.9

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_GreedyReusableNet_ProblemInstance

namespace GreedyReusableNet

/-- **Assumption 1 (Independence System)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, p.9):
"`𝒜_t` is an independence system over the basis `𝓑_t`. Meanwhile, there exists some `L ∈ ℤ₊`
such that `∀t ∈ [T], ∀B ∈ 𝓑_t`, we have `|B| ≤ L`."

For every period `t < T`: `𝒜_t` contains `∅` and is closed under subsets
(`SubsamplingSM.Offline.IsIndepSystem`), every action set consists of bundles of `𝓑_t` ("each
element in `𝒜_t` is subset of `𝓑_t`", p.9), and every bundle has at most `L` arms.

**Formalization Note** Periods are 0-based (`t < T`); `L : ℕ` is a parameter of the predicate. -/
def IndepSystemAssumption {N : ℕ} (I : ProblemInstance N) (T L : ℕ) : Prop :=
  ∀ t < T,
    SubsamplingSM.Offline.IsIndepSystem (· ∈ (I.period t).actions) ∧
    (∀ A ∈ (I.period t).actions, A ⊆ (I.period t).bundles) ∧
    ∀ B ∈ (I.period t).bundles, B.card ≤ L

end GreedyReusableNet


