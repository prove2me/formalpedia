-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_AttackModel
-- name    : GoldreichAffine_Exponential_AttackModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:42.490853+00:00
-- url     : https://prove2.me/theorems/ab94e367-49be-4355-a18d-3749f293ae3d
-- title:
--   Expected capacities, real count polytope and exact idealized cost
-- statement:
--   Fix $n,m,b\ge1$, $b\le n$, a weight $w\le n$ and a predicate $M$ on $b$ bits. For each feasible reduced guess $(n′,w′)$ let $t=n-n′$. Its overlap classes satisfy $0\le r\le b$, $r\le t$ and $b-r\le n′$. Define
--   $$\mu_r=m\frac{\binom t r\binom{n′}{b-r}}{\binom n b},\qquad q_r=\max_{Q\in\mathcal R_{b-r}(M),\ f\in\mathcal A_{b-r}}\Pr[Q(Z_{b-r})=f(Z_{b-r})].$$
--   Every residual and affine function is allowed, even if its local fixing is incompatible with the guessed values. Equation selection uses real counts $k_r$, with $0\le k_r\le\mu_r$ and $k=\sum_rk_r\le n′$. The model assigns success $\prod_rq_r^{k_r}$ and candidate work $2^{n′-k}$. Its cost and optimum are
--   $$C(n′,w′,\mathbf k)=\frac{2^{n′-k}}{p_{\rm guess}\prod_rq_r^{k_r}},\qquad C^\star=\min_{(n′,w′)\text{ feasible},\ \mathbf k\text{ feasible}}C(n′,w′,\mathbf k).$$
--   All sums and products include only feasible classes. Counts zero are always feasible; $n′=0$ is retained. This is the source's idealized GE-based work factor with polynomial overhead suppressed. It does not postulate any theorem about actual random-system ranks or error independence.
--
--   **Formalization Note** Counts form a function on natural indices; entries outside feasible classes have no effect. Real powers preserve fractional counts. Costs live in $[0,+\infty]$ and use complete-lattice infima. On valid source inputs, $1\le C^\star\le2^n$, the minimum is attained, and it agrees with the real optimum: there are finitely many reduced guesses and a compact finite-dimensional count polytope for each. The extended base-two logarithm takes values $-\infty$ and $+\infty$ at zero and infinity, rather than silently mapping either to zero. No boundedness, transfer estimate or cost bound is a structure field.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 6 (PDF p. 7), §3.2, Eqs. (1)–(6), continued on p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_FixedWeight
import Definitions.Def_GoldreichAffine_Exponential_Generator
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Only feasible overlap classes are included, including zero-capacity classes. -/
def overlaps (n b np : ℕ) : Finset ℕ :=
  (Finset.range (b + 1)).filter fun r => r ≤ n - np ∧ b - r ≤ np

noncomputable def capacity (n m b np r : ℕ) : ℝ :=
  (m : ℝ) * ((n - np).choose r : ℝ) * (np.choose (b - r) : ℝ) / (n.choose b : ℝ)

noncomputable def reliability {b : ℕ} (M : Predicate b) (np wp r : ℕ) : ℝ≥0∞ :=
  (bestAgreement M (b - r) (fixedWeightMass np wp (b - r)) : ℝ≥0∞)

noncomputable def countTotal (n b np : ℕ) (k : ℕ → ℝ) : ℝ :=
  ∑ r ∈ overlaps n b np, k r

/-- Values outside overlaps do not enter any sum, constraint, product or optimization. -/
noncomputable def FeasibleCounts (n m b np : ℕ) (k : ℕ → ℝ) : Prop :=
  (∀ r ∈ overlaps n b np, 0 ≤ k r ∧ k r ≤ capacity n m b np r) ∧
    countTotal n b np k ≤ (np : ℝ)

noncomputable def subSuccess {b : ℕ} (M : Predicate b)
    (n np wp : ℕ) (k : ℕ → ℝ) : ℝ≥0∞ :=
  ∏ r ∈ overlaps n b np, (reliability M np wp r) ^ (k r)

/-- Equations (1)--(5). ENNReal divisions keep zero success at infinity.
    On feasible source inputs success is positive and this is a finite real cost. -/
noncomputable def cost {b : ℕ} (M : Predicate b)
    (n w np wp : ℕ) (k : ℕ → ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((np : ℝ) - countTotal n b np k) /
    (guessingProbability n w np wp * subSuccess M n np wp k)

/-- Equation (6), with every realizable reduced guess and every real count vector.
    Reduction forgets only the identities of positions: (1)--(5) depend on np,wp alone.
    Complete-lattice infima have no empty/unbounded-real-set default. -/
noncomputable def optimalCost {b : ℕ} (M : Predicate b) (n m w : ℕ) : ℝ≥0∞ :=
  ⨅ (np : ℕ) (wp : ℕ) (_ : FeasiblePair n w np wp)
    (k : ℕ → ℝ) (_ : FeasibleCounts n m b np k), cost M n w np wp k

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Extended log₂: log₂ 0 = -∞ and log₂ +∞ = +∞; no conversion-to-zero default. -/
noncomputable def logCost (C : ℝ≥0∞) : EReal :=
  ENNReal.log C * ((Real.log 2)⁻¹ : ℝ)

end GoldreichAffine.Exponential


