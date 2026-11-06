-- Prove2me | Definitions.Def_RandomLPIPM_phi
-- name    : RandomLPIPM_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:29.183527+00:00
-- url     : https://prove2.me/theorems/ebca68e9-dada-47ac-9d44-b439f754b2f1
-- title:
--   Re-centering objective $\Phi_{x,\mu}$, (116)
-- statement:
--   For a strictly feasible $x$ (with $X=\operatorname{Diag}(x)$), cost $c$ and $\mu>0$,
--   $$\Phi_{x,\mu}(u)=\Big(\frac{Xc}{\mu}-\mathbf 1\Big)^{\!\top}u+\sum_{i=1}^n\tilde d(u_i),\qquad u\in\ker(AX).$$
--   On $\|u\|_\infty\le 1/4$ it equals $F_\mu(x\cdot(\mathbf 1+u))-F_\mu(x)$, the change of the log-barrier when moving from $x$ to $x(\mathbf 1+u)$; outside that box it is the quadratic extension.
--
--   **Formalization Note** Defined on all of $\mathbb R^n$; the restriction to $\ker(AX)$, i.e. $A(x\cdot u)=0$, is stated wherever $\Phi_{x,\mu}$ is minimized.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (114) p.77 and (116), p.78

import Mathlib
import Definitions.Def_RandomLPIPM_dTilde

open Matrix

namespace RandomLPIPM

/-- **The smoothed re-centering objective `Φ_{x,μ}`, (116).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (116), p.78:
`Φ_{x,μ}(u) := (Xc/μ − 1)ᵀu + ∑ᵢ d̃(uᵢ)`, `u ∈ ker(AX)`, where `X = Diag(x)`.

**Formalization Note.** Defined on all of `ℝⁿ`; the restriction to `ker(AX)` (i.e. `A(x·u) = 0`) is
stated where `Φ` is minimized. -/
noncomputable def phi {n : ℕ} (c x : Fin n → ℝ) (μ : ℝ) (u : Fin n → ℝ) : ℝ :=
  (fun i => x i * c i / μ - 1) ⬝ᵥ u + ∑ i, dTilde (u i)

end RandomLPIPM


