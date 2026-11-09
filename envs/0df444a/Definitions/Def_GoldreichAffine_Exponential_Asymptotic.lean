-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_Asymptotic
-- name    : GoldreichAffine_Exponential_Asymptotic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:38.516298+00:00
-- url     : https://prove2.me/theorems/64a5433b-fe7e-4e68-aba8-d25eef458232
-- title:
--   Rounded asymptotic regime and uniformly quantified cost property
-- statement:
--   A predicate family has an arbitrary Boolean predicate $M_b$ for each positive integer $b$. Fix real $s>1$ and, for each real $\gamma>0$, set
--   $$m_n=\lceil n^s\rceil,\qquad b_n=\lceil\gamma\log_2n\rceil,\qquad j_\theta(b)=\lceil\theta b\rceil.$$
--   The typical weights are
--   $$\mathcal W_n=\{w\in\{0,\ldots,n\}:|w-n/2|\le\sqrt{n\ln n}\}.$$
--   The vanishing-advantage property means: for every $\theta\in(0,1]$ and $\varepsilon>0$ there is $B$ such that every integer $b\ge\max(B,1)$ satisfies $|\operatorname{adv}_{j_\theta(b)}(M_b)|<\varepsilon$. The exponential-cost property means
--   $$\forall\gamma>0\ \forall c\in(0,2^{-(s-1)/\gamma})\ \exists N\ \forall n\ge N\ \forall w\in\mathcal W_n:\quad C^\star(n,w;\gamma)>2^{cn}.$$
--   The threshold $N$ depends on the family and the displayed fixed parameters, and is independent of $w$. Both properties concern all sufficiently large integers, rather than a chosen subsequence. This layer specifies the scope of the characterization without assuming either property.
--
--   **Formalization Note** Families have a harmless extra zero-arity entry, never used in any claim. Eventual validity also requires $n\ge2$, positive $m_n,b_n$ and $b_n\le n$; these hold eventually for each fixed $s>1,\gamma>0$. The bound retains strict inequalities and the exact constant. No explicit convergence rate is chosen for an arbitrary family.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 8 (PDF p. 9), §3.3 and Theorem 1 with its following explanatory paragraph; rounding convention §2, p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_AttackModel
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Only positive family entries are ever used in the statements. Entry zero is ignored. -/
abbrev PredicateFamily := (b : ℕ) → Predicate b

noncomputable def outputCount (s : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ s⌉₊
noncomputable def nonlinearArity (γ : ℝ) (n : ℕ) : ℕ := ⌈γ * logTwo n⌉₊
noncomputable def remainingArity (θ : ℝ) (b : ℕ) : ℕ := ⌈θ * (b : ℝ)⌉₊

noncomputable def TypicalWeight (n w : ℕ) : Prop :=
  w ≤ n ∧ |(w : ℝ) - (n : ℝ) / 2| ≤ Real.sqrt ((n : ℝ) * Real.log n)

/-- Eventually automatic validity; b≤n; a positive XOR arity is available eventually. -/
noncomputable def ValidSize (s γ : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ 0 < outputCount s n ∧ 0 < nonlinearArity γ n ∧ nonlinearArity γ n ≤ n

noncomputable def asymptoticCost (M : PredicateFamily) (s γ : ℝ) (n w : ℕ) : ℝ≥0∞ :=
  optimalCost (M (nonlinearArity γ n)) n (outputCount s n) w

noncomputable def VanishingAdvantage (M : PredicateFamily) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ B : ℕ,
    ∀ b : ℕ, B ≤ b → 1 ≤ b → |advantage (M b) (remainingArity θ b)| < ε

/-- N is outside n,w and may depend on M,s,gamma,c. Both inequalities are strict. -/
noncomputable def ExponentialCostProperty (M : PredicateFamily) (s : ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ c : ℝ, 0 < c → c < (2 : ℝ) ^ (-(s - 1) / γ) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ValidSize s γ n ∧
      ∀ w : ℕ, TypicalWeight n w →
        ENNReal.ofReal ((2 : ℝ) ^ (c * (n : ℝ))) < asymptoticCost M s γ n w

end GoldreichAffine.Exponential


