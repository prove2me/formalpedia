-- Prove2me | Definitions.Def_GreedyReusableNet_NonOverlappingActivation
-- name    : GreedyReusableNet_NonOverlappingActivation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:37.888595+00:00
-- url     : https://prove2.me/theorems/b8929f48-da2d-4a06-9d7c-4b8046634d6f
-- title:
--   Assumption 3 (Non-overlapping Activation)
-- statement:
--   **Assumption 3.** For every period $t<T$, action set $\mathcal A\in\mathscr A_t$ and counting vector $n$, any two different bundles that are activated together are disjoint: no outcome of the activation law of $(\mathcal A,n)$ contains two different bundles with a common arm. Hence every arm is activated at most once per period.
--
--   The paper states the assumption as $\mathbb E[\mathbb 1^\pi_t\{B_1\}\mathbb 1^\pi_t\{B_2\}]=0$ for overlapping $B_1\neq B_2$ and every online policy, and explains it on the same page as "for each random realization of the activation mechanism, any two different activated sets do not have arms in common", which is the condition stated here.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 3, p.10

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance

namespace GreedyReusableNet

/-- **Assumption 3 (Non-overlapping Activation)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1,
p.10): "`∀t ∈ [T]`, if `B_1, B_2` are two different elements in `𝓑_t` such that
`B_1 ∩ B_2 ≠ ∅`, then `𝔼[𝟙^π_t{B_1} · 𝟙^π_t{B_2}] = 0` holds for any online policy `π`."

Encoded, as the paper explains it on the same page ("for each random realization of the
activation mechanism, any two different activated sets do not have arms in common"), as a
condition on the support of the activation law: for every period `t < T`, every action set
`A ∈ 𝒜_t` and every counting vector `n`, two different bundles activated together are disjoint.

**Formalization Note** Activated bundles lie in `A ⊆ 𝓑_t` (`ActivatesWithinAction`,
`IndepSystemAssumption`), so they are elements of `𝓑_t` as in the printed statement. -/
def NonOverlappingActivation {N : ℕ} (I : ProblemInstance N) (T : ℕ) : Prop :=
  ∀ t < T, ∀ A ∈ (I.period t).actions, ∀ n : Fin N → ℕ,
    ∀ S ∈ ((I.period t).act A n).support, ∀ B₁ ∈ S, ∀ B₂ ∈ S, B₁ ≠ B₂ → Disjoint B₁ B₂

end GreedyReusableNet


