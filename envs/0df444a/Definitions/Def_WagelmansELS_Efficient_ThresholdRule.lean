-- Prove2me | Definitions.Def_WagelmansELS_Efficient_ThresholdRule
-- name    : WagelmansELS_Efficient_ThresholdRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:47.421087+00:00
-- url     : https://prove2.me/theorems/765e1dfd-ce72-49e9-b992-2388427992cd
-- title:
--   Section 2: successor slopes and the threshold selector
-- statement:
--   For $t\in E_i$ before the sentinel, let $\operatorname{succ}_i(t)$ be the next larger index in $E_i$. Its consecutive-point ratio is
--   $$r_i(t)=\frac{G(t)-G(\operatorname{succ}_i(t))}{D(t)-D(\operatorname{succ}_i(t))}.$$
--   The selected next production period is
--   $$q(i)=\min\Bigl(\{n+1\}\cup\{t\in E_i:t<n+1,\ r_i(t)<c_i\}\Bigr).$$
--   It is the first efficient period, in increasing period order, whose ratio to its successor falls below the current marginal production cost, and is $n+1$ if no ratio does.
--
--   This is the selection made by the paper's Algorithm and the display after Proposition 2.
--
--   **Formalization Note** The successor returns the sentinel outside its intended domain; every theorem uses it on an efficient nonsentinel period. On that domain the denominator is positive. The finite minimum is always nonempty because the sentinel is inserted.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), pp. S149–S150, Section 2, display following Proposition 2 and Algorithm, Iterations

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient
namespace Instance
variable (P : Instance)

/-- The next efficient period after `t`; the default is the sentinel. -/
noncomputable def succ (i t : ℕ) : ℕ :=
  let S := (E P i).filter (fun u => t < u)
  if h : S.Nonempty then S.min' h else P.n + 1

/-- Slope between consecutive efficient points. -/
noncomputable def ratio (i t : ℕ) : ℝ :=
  (P.G t - P.G (succ P i t)) / (P.D t - P.D (succ P i t))

/-- The first efficient period whose slope to its successor is below `c_i`,
or the sentinel if there is none. -/
noncomputable def q (i : ℕ) : ℕ :=
  let S := insert (P.n + 1)
    ((E P i).filter (fun t => t < P.n + 1 ∧ ratio P i t < P.c i))
  S.min' (by simp [S])

end Instance
end WagelmansELS.Efficient


