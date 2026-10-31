-- Prove2me | Definitions.Def_ApproxVI_Yc
-- name    : ApproxVI_Yc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:10.607174+00:00
-- url     : https://prove2.me/theorems/412575d6-9a85-4f74-879c-763f34272ce9
-- title:
--   The piecewise-constant trajectory $Y_c$
-- statement:
--   For a sequence $(y_n)$ (the drift terms $y_n\in H(x_n)$ of (18)),
--
--   $$
--   Y_c(t)=y_n,\qquad t\in[t_n,t_{n+1}).
--   $$
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, p.22

import Mathlib
import Definitions.Def_ApproxVI_segIdx

namespace ApproxVI

/-- The piecewise-constant trajectory `Y_c(t) := yₙ` for `t ∈ [tₙ, tₙ₊₁)` of Ramaswamy &
Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*, arXiv:1709.04673v5, §6.1, p.22.

**Formalization Note** `n` is `segIdx a t`, the index of the interval containing `t`. -/
noncomputable def Yc {d : ℕ} (a : ℕ → ℝ) (y : ℕ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  y (segIdx a t)

end ApproxVI


