-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_barrier
-- name    : VBSDP_Duality_Supplement_barrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:05:31.151989+00:00
-- url     : https://prove2.me/theorems/d9c38dc7-9081-47a4-b1cb-9ffb3c919937
-- title:
--   (42), p. 70 — the logarithmic barrier ϕ(x) = log det F(x)⁻¹
-- statement:
--   Let $F_0,\dots,F_m$ be symmetric $n\times n$ real matrices and $F(x)=F_0+\sum_{i=1}^mx_iF_i$. The **logarithmic barrier** of the linear matrix inequality $F(x)\ge0$ is
--
--   $$\phi(x)=\begin{cases}\log\det F(x)^{-1}&\text{if }F(x)>0,\\+\infty&\text{otherwise,}\end{cases}$$
--
--   where $F(x)>0$ means positive definite. It is finite exactly on $\mathbf X=\{x\mid F(x)>0\}$ and grows without bound towards the boundary of $\mathbf X$.
--
--   **Formalization Note** The Lean definition is the real number $\log\det F(x)^{-1}$ (`Real.log` of the determinant of Mathlib's matrix inverse) for every $x$. It agrees with the page on $\mathbf X$; outside $\mathbf X$, where the page sets $+\infty$, it is a junk value, and every statement of the mission that uses $\phi$ (the analytic center, the line search and Theorem 4.1) only evaluates or compares it at points with $F(x)>0$, which is where the page's $\phi$ is finite and the comparison is meaningful.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 70 (PDF p. 22), (42); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Duality.Supplement

/-- The logarithmic barrier (42), p. 70: `ϕ(x) = log det F(x)⁻¹`. The page sets
`ϕ(x) = +∞` when `F(x)` is not positive definite; this real-valued version is only meant
to be evaluated where `F(x) ≻ 0`, and every statement using it restricts to such points. -/
noncomputable def barrier {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) : ℝ :=
  Real.log ((VBSDP.Duality.lmi F₀ F x)⁻¹).det

end VBSDP.Duality.Supplement


