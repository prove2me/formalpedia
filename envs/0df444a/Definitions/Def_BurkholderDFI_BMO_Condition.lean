-- Prove2me | Definitions.Def_BurkholderDFI_BMO_Condition
-- name    : BurkholderDFI_BMO_Condition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:59.176217+00:00
-- url     : https://prove2.me/theorems/689363b1-fc13-47eb-8304-867dcb53c811
-- title:
--   Condition (19.1): unit conditional second-moment tail bound
-- statement:
--   Let $f=(f_n)_{n\ge1}$ have difference sequence $d$ relative to an increasing sequence of sigma-fields $(\mathcal A_n)_{n\ge0}$. **Condition (19.1)** says that, for every $n\ge1$,
--
--   $$\mathbf E\left[\sum_{k=n}^{\infty}d_k^2\,\middle|\,\mathcal A_n\right]\le1\qquad\text{almost surely}.$$
--
--   This is the normalized bounded-mean-oscillation condition used in Theorem 19.1. It controls the entire future squared-increment tail, including the increment at $n$.
--
--   **Formalization Note** The sum and conditional expectation are $[0,\infty]$-valued, so they remain meaningful before integrability of the tail is known. The conditioning sigma-field is $\mathcal A_n$, and the first term is $d_n^2$, exactly as printed. The inequality is almost everywhere because conditional expectation is defined up to null sets.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (19.1), p. 37, https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (19.1), p. 37: the conditional expectation given `𝒜_n` of the nonnegative sum
`∑_{k=n}^∞ d_k²` is at most one for each `n ≥ 1`. -/
def BMOCondition {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ)
    (P : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    condLExp (ℱ n) P (fun ω => ∑' j : ℕ, ENNReal.ofReal (BurkholderDFI.SquareFnLp.dseq f (n + j) ω ^ 2)) ≤ᵐ[P] 1

end BurkholderDFI.BMO


