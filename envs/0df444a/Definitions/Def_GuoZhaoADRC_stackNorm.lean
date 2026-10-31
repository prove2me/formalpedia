-- Prove2me | Definitions.Def_GuoZhaoADRC_stackNorm
-- name    : GuoZhaoADRC_stackNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:26.160347+00:00
-- url     : https://prove2.me/theorems/87f7c6ef-b2e8-46e1-9a2a-f119b5e65a88
-- title:
--   Euclidean norm of a stacked vector $\|(v^1,\dots,v^m)\|$
-- statement:
--   For blocks $v^i\in\mathbb R^{k_i}$, this is the Euclidean norm of the concatenated vector,
--
--   $$\|v\|=\Bigl(\sum_{i=1}^m\|v^i\|^2\Bigr)^{1/2}.$$
--
--   It gives the norms $\|e\|$ and $\|\eta\|$ of the stacked error vectors $e=(e^{1\top},\dots,e^{m\top})^\top$ and $\eta=x-z$ used in (3.9)–(3.29).
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, notation after (1.6), p.1730; norms ‖e‖, ‖η‖ of (3.9)–(3.29)

import Mathlib

namespace GuoZhaoADRC

/-- **The Euclidean norm of a stacked vector `(v^1, …, v^m)`, `‖v‖ = (∑_i ‖v^i‖²)^{1/2}`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), `e = (e^{1⊤}, …, e^{m⊤})^⊤`, `η = x − z` after (1.6),
p.1730; the norms `‖e‖`, `‖η‖` of (3.9)–(3.29).

**Formalization Note.** This is the Euclidean norm of the concatenation of the blocks. -/
noncomputable def stackNorm {m : ℕ} {k : Fin m → ℕ}
    (v : (i : Fin m) → EuclideanSpace ℝ (Fin (k i))) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

end GuoZhaoADRC


