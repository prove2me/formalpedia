-- Prove2me | Definitions.Def_PosetSecretary_LowerBound_Setting
-- name    : PosetSecretary_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:27.587531+00:00
-- url     : https://prove2.me/theorems/911d1eba-dd3e-45fb-93f8-99ca32e02193
-- title:
--   §3.1, §3.3, Definition 3.4, Figure 8 — consistent scorings, OPT, selection rules, expected score, and ω disjoint k-chains
-- statement:
--   The objects of the **poset secretary problem** (Salem–Gupta, §3.1 and §3.3) and of the lower-bound instance of Appendix F.
--
--   Let $(\mathcal C,\preceq)$ be a finite partially ordered set of candidates.
--
--   1. A **scoring consistent with the order** is a function $w:\mathcal C\to\mathbb R$ whose values (the true scores) are nonnegative and pairwise distinct, and which satisfies $a\prec b\Rightarrow w(a)<w(b)$.
--   2. For a selection capacity $k\in\mathbb N$, the **offline optimum** is
--   $$\mathrm{OPT}(w,k)=\max\Big\{\sum_{a\in S}w(a)\;:\;S\subseteq\mathcal C,\ |S|\le k\Big\},$$
--   the largest total score achievable with knowledge of the true scores (Definition 3.4).
--   3. A **selection rule with capacity $k$** is a probability distribution $\mu$ on the subsets of $\mathcal C$ supported on sets of at most $k$ elements: $\mu(S)\ge0$, $\sum_S\mu(S)=1$, and $\mu(S)=0$ whenever $|S|>k$. It models the law of the set an algorithm selects.
--   4. The **expected score** of $\mu$ under $w$ is $\mathbb E[w(\mathrm{Alg})]=\sum_S\mu(S)\sum_{a\in S}w(a)$, and the **selection probability** of $a$ is $p(a)=\sum_{S\ni a}\mu(S)$.
--   5. The poset $\mathrm{Chains}(\omega,k)$ is the disjoint union of $\omega$ chains with $k$ elements each: its elements are pairs $(i,x)$ with $i\in\{0,\dots,\omega-1\}$, $x\in\{0,\dots,k-1\}$, and $(i,x)\preceq(i',y)$ iff $i=i'$ and $x\le y$. It is the poset of Figure 8 with $n=\omega k$ elements.
--
--   These are the objects in which Proposition 5.1 (no algorithm beats competitive ratio $\omega$ on posets of width $\omega$) and its proof are stated.
--
--   **Formalization Note** An algorithm for the poset secretary problem sees only the poset and the arrival order, so on a fixed poset its randomness induces a distribution of the selected set that does not depend on the scores; selection rules are exactly such distributions, and the class contains every online algorithm. Nonnegativity and distinctness of the scores are standing assumptions of the model (§3.1, p. 7). OPT is a finite maximum (`Finset.sup'`) over a family that always contains $\emptyset$. In `ChainsPoset ω k` (Mathlib's disjoint order on a sigma type) the $j$th best element of chain $i$ is $(i,k-j)$.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), §3.1 p. 7, §3.3 p. 11, Definition 3.4 p. 12, Appendix F Figure 8 p. 42

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.LowerBound

variable {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]

/-- A (randomized) selection rule with capacity `k`: a probability distribution `μ` on the set of
selected elements, supported on sets of at most `k` elements. On a fixed poset, every algorithm for the
poset secretary problem (which sees only the poset and the arrival order) induces such a distribution,
independently of the scores. -/
def IsSelectionRule (k : ℕ) (μ : Finset β → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1 ∧ ∀ s, k < s.card → μ s = 0

/-- The expected total score `E[w(Alg(I))]` of the selected set under the selection rule `μ`. -/
def expectedScore (μ : Finset β → ℝ) (w : β → ℝ) : ℝ :=
  ∑ s, μ s * ∑ a ∈ s, w a

/-- The probability that the element `a` is selected under `μ` (the page's `p_j^i`). -/
def selProb (μ : Finset β → ℝ) (a : β) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => a ∈ s), μ s

/-- The poset of Figure 8 (Appendix F, p. 42) with `n = ωk`: `ω` pairwise incomparable chains
`Fin ω`, each a chain of `k` elements `Fin k`. The order is Mathlib's disjoint-sum order on a sigma
type: `⟨i, x⟩ ≤ ⟨i', y⟩` iff `i = i'` and `x ≤ y`. The `j`th best element of chain `i` is
`⟨i, k - j⟩`. -/
abbrev ChainsPoset (ω k : ℕ) : Type := Σ _ : Fin ω, Fin k

end PosetSecretary.LowerBound


