-- Prove2me | Definitions.Def_FreedmanTail_varSum
-- name    : FreedmanTail_varSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:41.107003+00:00
-- url     : https://prove2.me/theorems/14a2ac76-de2d-4698-a6d7-66cf2f6b7d6a
-- title:
--   Accumulated conditional variance $T_n = V_1 + \cdots + V_n$
-- statement:
--   Let $\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots$ be a filtration and $X_1, X_2, \dots$ real random variables. With $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty]$ define
--   $$T_n = V_1 + \cdots + V_n , \qquad T_0 = 0 .$$
--   $T_n$ is Freedman's intrinsic clock: the bound (4.1) controls $S_n$ on the event that $T_n$ is small.
--
--   **Formalization Note** In Lean the $i$-th summand ($i = 0, 1, \dots$) is the conditional variance of $X_i$ (the paper's $X_{i+1}$) given $\mathcal F_i$, i.e. the paper's $V_{i+1}$. Values lie in $[0, \infty]$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, §1, p. 101 and (1.2) Definition (g), p. 101

import Mathlib
import Definitions.Def_FreedmanTail_condVarE

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **The accumulated conditional variance `T_n = V_1 + ⋯ + V_n`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, §1, p. 101:
"Let V_n = Var{X_n | F_{n−1}}", and (1.2) Definition (g): "(g) T_n = V_1 + ··· + V_n, so
T_0 = 0".

`varSum F μ X n ω = ∑_{i < n} condVarE (F i) μ (X i) ω ∈ [0, ∞]`.

**Formalization Note.** Lean's `X i` is the paper's `X_{i+1}` and is conditioned on `F i`
(the paper's `F_i`), so the `i`-th summand is the paper's `V_{i+1} = Var{X_{i+1} | F_i}`. The
conditional variances take values in `[0, ∞]` (see `condVarE`), so `T_n ∈ [0, ∞]`. -/
noncomputable def varSum {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℕ mΩ)
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, condVarE (F i) μ (X i) ω

end FreedmanTail


