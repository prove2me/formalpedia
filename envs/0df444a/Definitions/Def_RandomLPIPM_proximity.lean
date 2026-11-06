-- Prove2me | Definitions.Def_RandomLPIPM_proximity
-- name    : RandomLPIPM_proximity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:02.847821+00:00
-- url     : https://prove2.me/theorems/bb74a4a1-bc89-4c7b-b8dd-0af4f8b59a93
-- title:
--   Proximity $E_\mu(x)=\|(x-x_\mu)/x_\mu\|_2$
-- statement:
--   For a strictly feasible $x$ and $\mu>0$, the proximity of $x$ to the central path point $x_\mu=x(\mu)$ is
--   $$E_\mu(x)=\Big\|\frac{x-x_\mu}{x_\mu}\Big\|_2 ,$$
--   with the quotient taken coordinatewise.
--
--   It is the centrality measure maintained by Algorithm 1 ($E_\mu(x)\le\varepsilon$) and assumed by basis identification ($E_{\hat\mu}(\hat x)\le 1/6$).
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §8.2, p.73; Algorithm 1, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_centralX
import Definitions.Def_ColumnRandLP_Norms

open Matrix

namespace RandomLPIPM

/-- **Proximity `E_μ(x) = ‖(x − x_μ)/x_μ‖`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §8.2, p.73: "Our proximity measure to the
central path is `E_μ(x) := ‖(x − x_μ)/x_μ‖`" (coordinatewise quotient), with the unsubscripted
Euclidean norm of Sections 8–9 (Theorem 2.1, p.8, writes `‖·‖₂`); Algorithm 1 and Theorem 9.3 use it
for the general (LP) with `x_μ = x(μ)`. -/
noncomputable def proximity {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ColumnRandLP.l2Norm (fun i => (x i - centralX A b c μ i) / centralX A b c μ i)

end RandomLPIPM


