-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_DPMaps
-- name    : ArapostathisAC_VanishingDiscount_DPMaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:51.439916+00:00
-- url     : https://prove2.me/theorems/521df9be-7287-4522-8e90-401fa4221c5e
-- title:
--   The dynamic programming maps $T$ and $T_\beta$ of (2.5)–(2.6) in the countable model
-- statement:
--   In the countable-state controlled Markov process of §5, the **undiscounted dynamic programming map** (2.5) sends a function $v:S\to\mathbb R$ to
--   $$T(v)(i)=\inf_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)\,v(j)\Big\},\qquad i\in S,$$
--   and, for $0<\beta<1$, the **discounted dynamic programming map** (2.6) is $T_\beta(v)=T(\beta v)$, that is,
--   $$T_\beta(v)(i)=\inf_{a\in U(i)}\Big\{c(i,a)+\beta\sum_{j\in S}P(j\mid i,a)\,v(j)\Big\}.$$
--   The discounted cost optimality equation (2.7) says that $J^*_\beta$ is a fixed point of $T_\beta$.
--
--   **Formalization Note.** `bellmanT` is real valued: the infimum is over the nonempty set $U(i)$ and the series is Lean's `tsum`, which is $0$ for a non-summable family, so statements about `bellmanT` assume the series converge. `discBellman` is $T_\beta$ for functions $v:S\to[0,\infty]$, computed in $[0,\infty]$, where every series and infimum is defined; it is applied to the possibly infinite $J^*_\beta$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, (2.5), (2.6), (2.7)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The undiscounted dynamic programming map (2.5) (p. 289) in the countable model:
`T(v)(i) = inf_{a ∈ U(i)} {c(i, a) + Σ_j P(j | i, a) v(j)}`, a real infimum over the nonempty set
`U(i)`. The series is a `tsum`; statements using `bellmanT` assume it is summable. -/
noncomputable def bellmanT (M : CMP A) (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  ⨅ a : M.U i, (M.c i a + ∑' j, prob M i a j * v j)

/-- The discounted dynamic programming map `T_β(v) = T(βv)` of (2.6)–(2.7) (p. 289) for
`v : ℕ → [0, ∞]`, computed in `[0, ∞]`:
`T_β(v)(i) = inf_{a ∈ U(i)} {c(i, a) + β Σ_j P(j | i, a) v(j)}`. -/
noncomputable def discBellman (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  ⨅ a ∈ M.U i, (ENNReal.ofReal (M.c i a) + ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * v j)

end ArapostathisAC.VanishingDiscount


