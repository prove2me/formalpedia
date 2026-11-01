-- Prove2me | Definitions.Def_GreedyReusableNet_ActivatesWithinAction
-- name    : GreedyReusableNet_ActivatesWithinAction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:47.070693+00:00
-- url     : https://prove2.me/theorems/737f6404-cf61-4cfb-afad-3cd1c73ca492
-- title:
--   Activated bundles belong to the action taken
-- statement:
--   For every period $t<T$, every action set $\mathcal A\in\mathscr A_t$ and every counting vector $n$, every outcome $\mathcal A_{\mathrm{act}}$ of the activation law of $(\mathcal A,n)$ satisfies $\mathcal A_{\mathrm{act}}\subseteq\mathcal A$: only bundles of the action taken can be activated (Algorithm 1, step 3: "The nature independently samples an $\mathcal A^\pi_{t,\mathrm{act}}\subset\mathcal A^\pi_t$").
--
--   **Formalization Note** This is part of the paper's model rather than a numbered assumption; it is stated as a predicate because the activation law is data of the instance.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Algorithm 1 step 3, p.8; p.9

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance

namespace GreedyReusableNet

/-- **Activated bundles belong to the action taken** (Simchi-Levi, Zheng & Zhu, SSRN 3981123,
Algorithm 1 step 3, p.8, and §2.1, p.9): "The nature independently samples an
`𝒜^π_{t,act} ⊂ 𝒜^π_t`."

For every period `t < T`, every action set `A ∈ 𝒜_t` and every counting vector `n`, every
outcome in the support of the activation law `act A n` is a subset of `A`.

**Formalization Note** This is part of the model of §2.1 rather than a numbered assumption; it
is stated separately because the activation law is data of the instance. -/
def ActivatesWithinAction {N : ℕ} (I : ProblemInstance N) (T : ℕ) : Prop :=
  ∀ t < T, ∀ A ∈ (I.period t).actions, ∀ n : Fin N → ℕ,
    ∀ S ∈ ((I.period t).act A n).support, S ⊆ A

end GreedyReusableNet


