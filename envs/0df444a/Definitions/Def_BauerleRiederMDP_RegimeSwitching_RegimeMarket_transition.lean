-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket_transition
-- name    : BauerleRiederMDP_RegimeSwitching_RegimeMarket_transition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:14.162367+00:00
-- url     : https://prove2.me/theorems/579158ee-1be5-47e3-8f88-c443363ed4e8
-- title:
--   Row $k\mapsto p_{jk}$ of the environment transition matrix as a probability measure
-- statement:
--   For an environment state $j$, the row $(p_{jk})_{k\in E_Y}$ of the transition matrix of $(Y_n)$, viewed as the probability measure $\sum_k p_{jk}\,\delta_k$ on $E_Y$: the conditional law of $Y_{n+1}$ given $Y_n=j$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (4.18), p.101 (PDF p.115)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The row `p_{j·}` of the transition matrix of the environment chain as a probability measure
on `E_Y`: `k ↦ p_{jk}` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), (4.18), p.101, PDF p.115). -/
noncomputable def RegimeMarket.transition {EY : Type*} [Fintype EY] [MeasurableSpace EY]
    [MeasurableSingletonClass EY] {d : ℕ} (M : RegimeMarket EY d) (j : EY) :
    ProbabilityMeasure EY :=
  ⟨∑ k, ENNReal.ofReal (M.p j k) • Measure.dirac k, by
    constructor
    simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => M.p_nonneg j k), M.sum_p, ENNReal.ofReal_one]⟩

end BauerleRiederMDP.RegimeSwitching


