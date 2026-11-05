-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction
-- name    : BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:11.919953+00:00
-- url     : https://prove2.me/theorems/29f3b1b8-cbde-4f58-beed-6dfa73a0692d
-- title:
--   Upper bounding function
-- statement:
--   A measurable function $b:E\to\mathbb R_+$ is an **upper bounding function** for the model if there exist $c_r,c_g,\alpha_b\in\mathbb R_+$ such that for all $n=0,\dots,N-1$:
--
--   1. $r_n^+(x,a)\le c_r\,b(x)$ for all $(x,a)\in D_n$;
--   2. $g_N^+(x)\le c_g\,b(x)$ for all $x\in E$;
--   3. $\int b(x')\,Q_n(dx'\mid x,a)\le\alpha_b\,b(x)$ for all $(x,a)\in D_n$.
--
--   If $r_n$ and $g_N$ are bounded above, then $b\equiv 1$ is an upper bounding function.
--
--   **Formalization Note.** The integral in 3 is a Lebesgue integral in $[0,\infty]$, so 3 includes its finiteness.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.4.1, p.28

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- `b : E → ℝ_+` is an upper bounding function for the Markov Decision Model (Bäuerle & Rieder
(2011), Definition 2.4.1, p.28, PDF 43): `b` is measurable and there exist `c_r, c_g, α_b ∈ ℝ_+`
such that for all `n = 0, …, N-1`: (i) `r_n⁺(x, a) ≤ c_r b(x)` on `D_n`; (ii) `g_N⁺(x) ≤ c_g b(x)`;
(iii) `∫ b(x') Q_n(dx' | x, a) ≤ α_b b(x)` on `D_n`.

**Formalization Note.** The integral in (iii) is a Lebesgue integral in `[0, ∞]`, so (iii) also
says it is finite. -/
def IsUpperBoundingFunction {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) : Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧
  ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
    (∀ n < N, ∀ xa ∈ M.D n, max (M.r n xa) 0 ≤ cr * b xa.1) ∧
    (∀ x, max (M.g x) 0 ≤ cg * b x) ∧
    ∀ n < N, ∀ xa ∈ M.D n,
      ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) ≤ ENNReal.ofReal (αb * b xa.1)

end BauerleRiederMDP.FiniteHorizon


