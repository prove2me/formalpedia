-- Prove2me | Definitions.Def_ModernOnlineLearning_Portfolio_Setting
-- name    : ModernOnlineLearning_Portfolio_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:53.627011+00:00
-- url     : https://prove2.me/theorems/d3a25414-9662-4660-a148-2c34023a110b
-- title:
--   Chapter 10 setting — simplex uniform prior, F-weighted portfolios, and wealth
-- statement:
--   Let $d\ge2$ be the number of stocks. A portfolio $u\in\Delta^{d-1}$ has nonnegative weights that sum to one. For nonnegative market vectors $w_t$, its constantly rebalanced wealth after $T$ rounds is
--
--   $$W_T(u)=\prod_{t=1}^{T}\langle w_t,u\rangle.$$
--
--   The uniform prior $F_d$ is the probability measure on $\Delta^{d-1}$ obtained from Lebesgue measure in the first $d-1$ coordinates, scaled by $(d-1)!$; the last coordinate is one minus their sum. Algorithm 10.1 predicts in round $t$ with the wealth-weighted barycenter
--
--   $$x_t(i)=\frac{\int_{\Delta^{d-1}}u_i W_{t-1}(u)\,F_d(du)}{\int_{\Delta^{d-1}}W_{t-1}(u)\,F_d(du)}.$$
--
--   Its wealth is $\prod_{t=1}^{T}\langle w_t,x_t\rangle$. The stock-choice monomial $\prod_{t=1}^{T}u_{j_t}$ pairs the market model with the generic sequence types used later.
--
--   **Formalization Note** Rounds are numbered from one, with index zero unused. The simplex prior is a push-forward from the standard coordinate chart; the chart is proved measurable. The integral ratio is defined as a total Lean function, while the theorem asserts positive wealth on admissible markets.
-- source:
--   Orabona, arXiv:1912.13213v10, §10.1, p. 170; Algorithm 10.1, p. 172; Definition 10.2, p. 173

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- The nonnegative coordinate chart of the simplex, with its final coordinate omitted. -/
def chartDomain (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1}

/-- Reinsert the final simplex coordinate as one minus the other coordinates. -/
def chartPortfolio (d : ℕ) (y : Fin (d - 1) → ℝ) : Fin d → ℝ :=
  fun i => if h : i.val < d - 1 then y ⟨i.val, h⟩ else 1 - ∑ k, y k

/-- The coordinate chart is measurable, so its push-forward does not take Lean's
zero-measure fallback for non-measurable maps. -/
theorem measurable_chartPortfolio (d : ℕ) : Measurable (chartPortfolio d) := by
  rw [measurable_pi_iff]
  intro i
  dsimp [chartPortfolio]
  split_ifs <;> fun_prop

/-- The chart domain is a measurable subset of coordinate space. -/
theorem measurableSet_chartDomain (d : ℕ) : MeasurableSet (chartDomain d) := by
  unfold chartDomain
  measurability

/-- Uniform probability measure on the simplex, via Lebesgue measure in the first `d-1`
coordinates. The factor `(d-1)!` is the reciprocal of the chart simplex volume. -/
noncomputable def uniformPrior (d : ℕ) : MeasureTheory.Measure (Fin d → ℝ) :=
  MeasureTheory.Measure.map (chartPortfolio d)
    (((Nat.factorial (d - 1) : ENNReal) •
      (MeasureTheory.volume.restrict (chartDomain d))))

/-- Wealth of a constantly rebalanced portfolio from an initial wealth of one. -/
def wealthCRP {d : ℕ} (w : ℕ → Fin d → ℝ) (u : Fin d → ℝ) (T : ℕ) : ℝ :=
  ∏ t ∈ Finset.Icc 1 T, ∑ i, w t i * u i

/-- Wealth of a fixed portfolio before round `t`; round zero is unused. -/
def wealthBefore {d : ℕ} (w : ℕ → Fin d → ℝ) (u : Fin d → ℝ) (t : ℕ) : ℝ :=
  ∏ s ∈ Finset.Ico 1 t, ∑ i, w s i * u i

/-- Algorithm 10.1, componentwise: the wealth-weighted barycenter of the prior. -/
noncomputable def weightedPortfolio {d : ℕ} (F : MeasureTheory.Measure (Fin d → ℝ))
    (w : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i => (∫ u, u i * wealthBefore w u t ∂F) /
    (∫ u, wealthBefore w u t ∂F)

/-- Wealth of the sequential portfolio from an initial wealth of one. -/
def portfolioWealth {d : ℕ} (w : ℕ → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (T : ℕ) : ℝ :=
  ∏ t ∈ Finset.Icc 1 T, ∑ i, w t i * x t i

/-- The monomial indexed by a sequence of stock choices. -/
def sequenceMonomial {d T : ℕ} (j : Fin T → Fin d) (u : Fin d → ℝ) : ℝ :=
  ∏ t : Fin T, u (j t)

end ModernOnlineLearning.Portfolio


