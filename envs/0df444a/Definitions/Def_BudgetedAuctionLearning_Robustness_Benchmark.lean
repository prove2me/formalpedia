-- Prove2me | Definitions.Def_BudgetedAuctionLearning_Robustness_Benchmark
-- name    : BudgetedAuctionLearning_Robustness_Benchmark
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:41.713267+00:00
-- url     : https://prove2.me/theorems/bbc4afef-4b54-4b55-b0b7-e652239889e9
-- title:
--   Optimization Programs (4) and (5) — the budgeted Stackelberg value OPT and the Lagrangian supremum $R^\star(\mu)$
-- statement:
--   The budgeted Stackelberg value in the auction is the supremum in Optimization Program (4):
--
--   $$\mathrm{OPT}=\sup\ q\,U_O(\hat V^{(1)})+(1-q)\,U_O(\hat V^{(2)})$$
--
--   over randomized maps $\hat V^{(1)},\hat V^{(2)}$, multipliers $\lambda_1,\lambda_2\ge 0$ and $q\in[0,1]$, subject to
--
--   $$q\lambda_1P_O(\hat V^{(1)})+(1-q)\lambda_2P_O(\hat V^{(2)})\le\rho_O,\qquad \lambda_iP_L(\hat V^{(i)})\ge\rho_L\ \ (i=1,2).$$
--
--   For $\mu\ge0$, Optimization Program (5) defines
--
--   $$R^\star(\mu)=\sup\ U_O(\hat V)-\mu\lambda P_O(\hat V)\quad\text{subject to}\quad\lambda P_L(\hat V)\ge\rho_L,\ \lambda\ge0.$$
--
--   Both are computed from the data and neither is a free parameter. They are the benchmark of the main theorem and the bridge from budgets to Lagrangian rewards.
--
--   **Formalization Note.** Both suprema are taken in `EReal`, so an empty feasible set gives $-\infty$. Coefficients multiply payments in `ℝ≥0∞`, where $0\cdot\infty=0$, so a zero-weight phase with infinite first-price payment contributes nothing. The learner inequality binds a zero-weight phase too, as printed.
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Optimization Programs (4), (5), printed p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_AuctionModel
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- The constraints of Optimization Program (4). `ℝ≥0∞` multiplication gives a zero coefficient
times an infinite payment the value `0`. The learner inequality binds each phase, also at weight
zero, as printed. -/
def BSEFeasible (fmt : AuctionFormat) (D : Measure ValuePair) (ρL ρO q : ℝ)
    (V₁ V₂ : RandomizedFakeValue) (lam₁ lam₂ : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ lam₁ ∧ 0 ≤ lam₂ ∧
    ENNReal.ofReal (q * lam₁) * randPayO fmt D V₁ +
        ENNReal.ofReal ((1 - q) * lam₂) * randPayO fmt D V₂ ≤ ENNReal.ofReal ρO ∧
    ENNReal.ofReal ρL ≤ ENNReal.ofReal lam₁ * randPayL fmt D V₁ ∧
    ENNReal.ofReal ρL ≤ ENNReal.ofReal lam₂ * randPayL fmt D V₂

/-- `OPT`, the value of Optimization Program (4): an actual supremum in `EReal`, so an empty
feasible set gives `⊥ = -∞`, never a default `0`. -/
noncomputable def bseValue (fmt : AuctionFormat) (D : Measure ValuePair) (ρL ρO : ℝ) : EReal :=
  ⨆ (q : ℝ) (V₁ : RandomizedFakeValue) (V₂ : RandomizedFakeValue) (lam₁ : ℝ) (lam₂ : ℝ)
    (_ : BSEFeasible fmt D ρL ρO q V₁ V₂ lam₁ lam₂),
    ((ENNReal.ofReal q * randValue D V₁ + ENNReal.ofReal (1 - q) * randValue D V₂ : ℝ≥0∞) : EReal)

/-- `R★(μ)`, the supremum of Optimization Program (5) at a multiplier `μ`. The penalty is an extended
nonnegative number: an infinite penalty gives `-∞`, a zero coefficient gives `0`. An empty feasible
set gives `⊥`. -/
noncomputable def lagrangianBenchmark (fmt : AuctionFormat) (D : Measure ValuePair) (ρL μ : ℝ) : EReal :=
  ⨆ (V : RandomizedFakeValue) (lam : ℝ)
    (_ : 0 ≤ lam ∧ ENNReal.ofReal ρL ≤ ENNReal.ofReal lam * randPayL fmt D V),
    ((randValue D V : ℝ≥0∞) : EReal) -
      ((ENNReal.ofReal (μ * lam) * randPayO fmt D V : ℝ≥0∞) : EReal)

end BudgetedAuctionLearning.Robustness


