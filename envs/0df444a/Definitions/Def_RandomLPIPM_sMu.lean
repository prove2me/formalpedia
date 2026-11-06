-- Prove2me | Definitions.Def_RandomLPIPM_sMu
-- name    : RandomLPIPM_sMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:14.687666+00:00
-- url     : https://prove2.me/theorems/80259bd5-b768-496f-9903-c0a3ebbe0b3d
-- title:
--   The dual central path point $s_\mu(A)=\mu/x_\mu(A)$
-- statement:
--   The dual slack of the $\mu$-central path point of LP(A) is
--   $$s_\mu(A)=\frac{\mu}{x_\mu(A)}\qquad\text{(coordinatewise)},$$
--   so that $x_\mu\cdot s_\mu=\mu\mathbf 1_n$ and $s_\mu-\mathbf 1\in\operatorname{im}A^\top$.
--
--   Together with $x_\mu$ it forms the primal-dual central path $(x_\mu,s_\mu)$ of LP(A).
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (1), p.6; p.22; p.4 ($s_\mu=\mu/x_\mu$)

import Mathlib
import Definitions.Def_RandomLPIPM_xMu

open Matrix

namespace RandomLPIPM

/-- **The dual central path point `s_μ(A)` of LP(A).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (1) p.6 and p.22: the central
path point satisfies `x·s = μ1`, so `s_μ = μ / x_μ` coordinatewise (p.4: "`s_μ = μ/x_μ`"). -/
noncomputable def sMu {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (μ : ℝ) : Fin n → ℝ :=
  fun i => μ / xMu A μ i

end RandomLPIPM


