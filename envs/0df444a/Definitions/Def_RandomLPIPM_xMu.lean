-- Prove2me | Definitions.Def_RandomLPIPM_xMu
-- name    : RandomLPIPM_xMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:58.172598+00:00
-- url     : https://prove2.me/theorems/7c2d1b9a-6385-4a4e-9a05-ab32fde4b95a
-- title:
--   The $\mu$-central path point $x_\mu(A)$ of $\mathrm{LP}(A)$
-- statement:
--   For $A\in\mathbb R^{d\times n}$, LP(A) is the program
--   $$\min_{x\in\mathbb R^n_{\ge0}}\ \mathbf 1_n^\top x\quad\text{s.t.}\quad Ax=A\mathbf 1_n ,$$
--   with dual $\max (A\mathbf 1_n)^\top y$ s.t. $A^\top y+s=\mathbf 1_n$, $s\ge0$. For $\mu>0$, $x_\mu(A)$ is the unique minimizer of $\mathbf 1^\top x-\mu\sum_i\ln x_i$ over $\{x>0: Ax=A\mathbf 1\}$; equivalently $(x_\mu,s_\mu)$ is the unique solution of $x\cdot s=\mu\mathbf 1$, $x-\mathbf 1\in\ker A$, $s-\mathbf 1\in\operatorname{im}A^\top$, $x,s>0$.
--
--   The path starts at $x_1(A)=\mathbf 1_n$ and converges to an optimal solution as $\mu\to0$.
--
--   **Formalization Note** Defined through the barrier form, which the paper states as equivalent to the defining equations (p.22). It is the general central path with $b=A\mathbf 1$ and $c=\mathbf 1$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (16) and the definition after it, p.22; (1), p.6

import Mathlib
import Definitions.Def_RandomLPIPM_centralX

open Matrix

namespace RandomLPIPM

/-- **The `μ`-central path point `x_μ(A)` of LP(A).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (16) and the definition after it,
p.22: LP(A) is `min 1ᵀx` s.t. `Ax = A1`, `x ≥ 0`, and `x_μ(A)` is the unique minimizer of
`1ᵀx − μ ∑ ln xᵢ` over `{x > 0 : Ax = A1}`.

**Formalization Note.** Section 3 defines `(x_μ, s_μ)` by the equations `x·s = μ1`, `x − 1 ∈ ker A`,
`s − 1 ∈ im Aᵀ`, and states (p.22) that `x_μ` is equivalently the barrier minimizer; the barrier
form is used here. `1ᵀx/μ − ∑ log xᵢ` and `1ᵀx − μ ∑ ln xᵢ` have the same minimizer for `μ > 0`. -/
noncomputable def xMu {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (μ : ℝ) : Fin n → ℝ :=
  centralX A (A *ᵥ 1) 1 μ

end RandomLPIPM


