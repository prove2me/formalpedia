-- Prove2me | Definitions.Def_MultiServerAppt_alphaSys
-- name    : MultiServerAppt_alphaSys
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:13.434265+00:00
-- url     : https://prove2.me/theorems/e2a1817c-5867-42af-8cec-00c10fe82f01
-- title:
--   The initial vectors $\alpha_{s+i}$, Eq. (15)
-- statement:
--   The vectors $\alpha_{s+i}$ are defined by recursion on $i$: $\alpha_s$ is the initial vector, and
--
--   $$\alpha_{s+i+1}=f\big(\alpha_{s+i}\exp(S_{s+i}\,x_{s+i+1}),\ \alpha\big).$$
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.12, and Eq. (15), p.14

import Mathlib
import Definitions.Def_MultiServerAppt_sysMat
import Definitions.Def_MultiServerAppt_alphaInit
import Definitions.Def_MultiServerAppt_alphaStep

open Matrix

namespace MultiServerAppt

/-- The initial vectors `α_{s+i}` of the system, by the recursion of Eq. (15): `α_s` is `alphaInit`,
and `α_{s+i+1} = f(α_{s+i} exp(S_{s+i} x_{s+i+1}), α)`. Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, §4.1 p.12 and Eq. (15), p.14. -/
noncomputable def alphaSys {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ)
    (s : ℕ) (x : ℕ → ℝ) : (i : ℕ) → State ι s i → ℝ
  | 0 => alphaInit α s
  | i + 1 =>
    alphaStep α s i (alphaSys α S s x i ᵥ* NormedSpace.exp (x (s + i + 1) • sysMat α S s i))

end MultiServerAppt


