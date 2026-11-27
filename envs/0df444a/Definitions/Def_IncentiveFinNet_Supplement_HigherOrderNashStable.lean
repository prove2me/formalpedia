-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_HigherOrderNashStable
-- name    : IncentiveFinNet_Supplement_HigherOrderNashStable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:28:19.258594+00:00
-- url     : https://prove2.me/theorems/a16b9185-1d2f-4db8-ae31-dffe32e60ce4
-- title:
--   Higher-Order Nash Stability (Definition 5; cartels nonempty)
-- statement:
--   A feasible point $(W,P)$ of a network setting is **Higher-Order Nash Stable** (Definition 5) if:
--
--   1. **Nash equilibrium.** No agent $i$ has an action such that some resulting network $(W',P')$ (Definition 4) is strictly better for $i$: $g_i(W',P') \le g_i(W,P)$.
--   2. **Cartel robustness.** For every nonempty proper subset $T \subsetneq [n]$ of agents there is no feasible point $(W',P')$ that differs from $(W,P)$ only at entries $(a,b)$ with $a\in T$ and $b \in T$ and gives every agent of $T$ strictly higher utility:
--   $$
--   \neg\ \forall k\in T,\ g_k(W,P) < g_k(W',P').
--   $$
--
--   This strengthens pairwise stability and pairwise Nash equilibrium by allowing coalitions of agents to deviate together, in the spirit of strong Nash equilibrium.
--
--   **Formalization Note** The paper's cartel clause ranges over every proper subset $S\subset[n]$. For $S=\emptyset$ it fails for every $(W,P)$: $(W,P)$ itself differs from $(W,P)$ only on $\emptyset$, and "all agents in $\emptyset$ have higher utility" holds vacuously. The proof of Theorem 3 (A.6, p.37) considers only $(W',P')\neq(W,P)$, which forces the cartel to be nonempty; for a nonempty cartel, $(W',P') = (W,P)$ improves nobody. So the definition takes nonempty cartels, which is equivalent to adding the proof's condition $(W',P')\ne(W,P)$.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Definition 5 (Higher-Order Nash Stability), p.13; proof of Theorem 3, A.6, p.37

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_ResultingNetwork

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Definition 5 (Higher-Order Nash Stability)**, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, p.13: "A feasible `(W, P)` is Higher-Order Nash Stable if:
1. Nash equilibrium: No agent `i` has an action such that the resulting network `(W′, P′)` is
strictly better for `i`.
2. Cartel robustness: For any proper subset `S ⊂ [n]` of agents, there is no feasible point
`(W′, P′)` that differs from `(W, P)` only for indices `{i, j}` with `i ∈ S, j ∈ S` such that all
agents in `S` have higher utility under `(W′, P′)` than `(W, P)`."

**Formalization Note**
* Actions and resulting networks are those of `ResultingNetwork` (Definition 4); "strictly better"
  and "higher utility" are strict inequalities of the utility (1).
* The cartel `T` ranges over **nonempty** proper subsets of `[n]`. For `T = ∅` the printed clause
  fails for every `(W, P)`: `(W, P)` itself differs from `(W, P)` only on `∅`, and "all agents in
  `∅` have higher utility" holds vacuously. The proof of Theorem 3 (A.6, p.37) takes
  `(W′, P′) ≠ (W, P)`, which forces `T ≠ ∅`; with `T ≠ ∅` and `(W′, P′) = (W, P)` no agent of `T`
  gains, so requiring `T ≠ ∅` and requiring `(W′, P′) ≠ (W, P)` give the same condition. -/
def HigherOrderNashStable {n : ℕ} (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  Feasible S W P ∧
  (∀ (i : Fin n) (w' p' : Fin n → ℝ) (W' P' : Matrix (Fin n) (Fin n) ℝ),
    ResultingNetwork S W P i w' p' W' P' → ¬ S.utility i W P < S.utility i W' P') ∧
  (∀ T : Finset (Fin n), T.Nonempty → T ≠ Finset.univ →
    ∀ W' P' : Matrix (Fin n) (Fin n) ℝ, Feasible S W' P' →
      (∀ a b, (a ∉ T ∨ b ∉ T) → W' a b = W a b ∧ P' a b = P a b) →
      ¬ ∀ k ∈ T, S.utility k W P < S.utility k W' P')

end IncentiveFinNet.Supplement


