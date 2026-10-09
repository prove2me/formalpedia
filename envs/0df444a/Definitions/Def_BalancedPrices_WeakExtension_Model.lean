-- Prove2me | Definitions.Def_BalancedPrices_WeakExtension_Model
-- name    : BalancedPrices_WeakExtension_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:56.336458+00:00
-- url     : https://prove2.me/theorems/8dbd6777-380a-4afa-8021-a414625b40cc
-- title:
--   Definition 3.4, p. 551 — weakly (α, β₁, β₂)-balanced pricing rules
-- statement:
--   This file adds weak balancedness (Definition 3.4) to the deterministic model of Dütting, Feldman, Kesselheim and Lucier, whose objects (outcome profiles, $x_{[i-1]}$, welfare, $v(\mathrm{OPT}(v,S))$, pricing rules) are those of the shared model file `BalancedPrices.Extension.Model`.
--
--   There are $n$ agents; agent $i$ has an outcome space $X_i$ with a null outcome $\emptyset$, and $\mathcal F\subseteq X=X_1\times\cdots\times X_n$ is the set of feasible outcome profiles. For a profile $x$, $x_{[i-1]}$ keeps the outcomes of the agents before $i$ and gives $\emptyset$ to the others; $v(x)=\sum_i v_i(x_i)$ is the welfare and $v(\mathrm{OPT}(v,S))=\sup_{x\in S}v(x)$ the optimal welfare over $S$ ($0$ for $S=\emptyset$).
--
--   A **pricing rule** assigns to agent $i$, outcome $x_i$ and feasible partial allocation $y\in\mathcal F$ a price $p_i(x_i\mid y)\in[0,\infty]$ (p. 548).
--
--   **Definition 3.4.** Let $\alpha>0$ and $\beta_1,\beta_2\ge 0$. A pricing rule $p^v$ is **weakly $(\alpha,\beta_1,\beta_2)$-balanced** for the valuation profile $v$, with respect to an allocation rule $\mathrm{ALG}$, a family $(\mathcal F_x)_{x\in X}$ and the indexing of the players, if for all $x\in\mathcal F$:
--   - (a) $\displaystyle\sum_{i} p^v_i(x_i\mid x_{[i-1]}) \ \ge\ \frac1\alpha\bigl(v(\mathrm{ALG}(v)) - v(\mathrm{OPT}(v,\mathcal F_x))\bigr)$, and
--   - (b) for all $x'\in\mathcal F_x$:
--   $$\sum_{i} p^v_i(x'_i\mid x_{[i-1]}) \ \le\ \beta_1\, v(\mathrm{OPT}(v,\mathcal F_x)) + \beta_2\, v(\mathrm{ALG}(v)).$$
--
--   Weak balancedness relaxes property (b) of $(\alpha,\beta)$-balancedness (Definition 3.1) by an additional budget proportional to the benchmark welfare $v(\mathrm{ALG}(v))$; it is the hypothesis of Theorem 3.5 and of the composition result Theorem B.3.
--
--   **Formalization Note.** Agents are `Fin n`, 0-based: the paper's agent $i$ is index $i-1$, and $x_{[i-1]}$ is `pre nul x i`, which keeps the indices $j<i$. Prices take values in `ENNReal` with $\top=\infty$. In (a) the right side is passed through `ENNReal.ofReal`, which turns a negative value into $0$; since prices are nonnegative this is the page's meaning. Price sums are never converted to reals. The pricing-rule condition ($\infty$ off $\mathcal F$) is `BalancedPrices.Extension.IsPricingRule` of the shared model file; this file does not restate it. `WeakBalanced` takes the outcome $a=\mathrm{ALG}(v)$ rather than the rule, since Definition 3.4 uses ALG only through $v(\mathrm{ALG}(v))$; $\alpha>0$, $\beta_1,\beta_2\ge0$ and the valuation bounds $[0,1]$ are hypotheses of the theorems that use it.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), pp. 547–548 (§2, pricing rules), p. 551, Definition 3.4

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model

namespace BalancedPrices.WeakExtension

/-- Definition 3.4: the pricing rule `p` is weakly `(α, β₁, β₂)`-balanced for the valuation
profile `v`, with respect to the outcome `a = ALG(v)`, the family `Fam` and the index order. -/
def WeakBalanced {n : ℕ} {X : Fin n → Type*} (nul : BalancedPrices.Extension.Outcome X)
    (α β₁ β₂ : ℝ) (F : Set (BalancedPrices.Extension.Outcome X))
    (Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X)) (v : BalancedPrices.Extension.Valuation X)
    (a : BalancedPrices.Extension.Outcome X) (p : BalancedPrices.Extension.PriceRule X) : Prop :=
  ∀ x ∈ F,
    ENNReal.ofReal ((1 / α) * (BalancedPrices.Extension.welfare v a - BalancedPrices.Extension.optVal v (Fam x))) ≤
      ∑ i, p i (x i) (BalancedPrices.Extension.pre nul x i) ∧
    ∀ x' ∈ Fam x,
      (∑ i, p i (x' i) (BalancedPrices.Extension.pre nul x i)) ≤
        ENNReal.ofReal (β₁ * BalancedPrices.Extension.optVal v (Fam x) + β₂ * BalancedPrices.Extension.welfare v a)

end BalancedPrices.WeakExtension


