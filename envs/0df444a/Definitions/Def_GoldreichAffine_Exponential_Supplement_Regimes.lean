-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_Supplement_Regimes
-- name    : GoldreichAffine_Exponential_Supplement_Regimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:19.872534+00:00
-- url     : https://prove2.me/theorems/522c005e-f018-4fb6-b287-12b81a42df6b
-- title:
--   Subexponential cost and near-half bit-fixing affine advantage (Theorem 2)
-- statement:
--   Fix a predicate family $(M_b)_{b\ge1}$, a real $s>1$ and a real $\gamma>0$. As in the published asymptotic regime of this mission, set $m_n=\lceil n^s\rceil$, $b_n=\lceil\gamma\log_2 n\rceil$, and let $W_n=\{w\in\{0,\dots,n\}: |w-n/2|\le\sqrt{n\ln n}\}$ be the typical seed weights. Write $C^\star(n,w;\gamma)$ for the optimal idealized cost of the guess-and-affine-approximation attack with these parameters.
--
--   **Subexponential cost** (for this fixed $\gamma$) means that $C^\star(n,w;\gamma)=2^{o(n)}$ uniformly over $w\in W_n$: for every $\varepsilon>0$ there is $N$ such that for all $n\ge N$ the size parameters are valid and
--
--   $$\log_2 C^\star(n,w;\gamma)\le\varepsilon n\qquad\text{for every } w\in W_n .$$
--
--   **Near-half advantage** means that for every fixed $\theta\in(0,1)$,
--
--   $$\lim_{b\to\infty}\operatorname{adv}_{\lceil\theta b\rceil}(M_b)=\frac12 ,$$
--
--   where $\operatorname{adv}_{b'}$ is the published bit-fixing affine advantage (Definition 5).
--
--   These two properties are the two sides of Theorem 2.
--
--   **Formalization Note** The threshold $N$ is chosen before $w$, which is the uniformity over $W_n$ required in §3.3. The logarithm is the published extended $\log_2$ on $[0,\infty]$, so an infinite cost never satisfies the bound. Only the upper estimate is written: $C^\star\ge1$ holds in the cost model (App. A.5), so $\log_2C^\star\ge0$ needs no clause. Here $\theta b$ is rounded up, $\lceil\theta b\rceil$, following the paper's rounding convention (§2). Unlike the published `ExponentialCostProperty`, which quantifies over all $\gamma$ internally, the cost property here is for one fixed $\gamma$.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 8 (PDF p. 9), §3.3 and Theorem 2; proof App. A.5, pp. 21–22 (PDF pp. 22–23)

import Definitions.Def_GoldreichAffine_Exponential_Asymptotic
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 2 (printed p.8 / PDF p.9), cost side, for one fixed gamma:
    log₂ C*(n,w;gamma) ≤ eps·n eventually, with N chosen before w (uniform over W_n).
    The base regime (m = ⌈n^s⌉, b = ⌈gamma log₂ n⌉, ValidSize) is reused unchanged. -/
noncomputable def SubexponentialCost (M : PredicateFamily) (s γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ValidSize s γ n ∧
    ∀ w : ℕ, TypicalWeight n w →
      logCost (asymptoticCost M s γ n w) ≤ (((ε * (n : ℝ)) : ℝ) : EReal)

/-- Theorem 2, advantage side: adv_{⌈theta b⌉}(M_b) → 1/2 for every theta in the OPEN interval (0,1). -/
noncomputable def NearHalfAdvantage (M : PredicateFamily) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε → ∃ B : ℕ,
    ∀ b : ℕ, B ≤ b → 1 ≤ b → |advantage (M b) (remainingArity θ b) - 1 / 2| < ε

end GoldreichAffine.Exponential.Supplement


