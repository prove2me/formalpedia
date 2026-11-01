-- Prove2me | Definitions.Def_ScutaruFid_stateKernel
-- name    : ScutaruFid_stateKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:06.017897+00:00
-- url     : https://prove2.me/theorems/a9b82992-bf80-4ebe-afe3-1006e073bab8
-- title:
--   Kernel of the Gaussian state with matrix $A$ and mean $u=(\alpha,\tau)$
-- statement:
--   Let $A=\begin{pmatrix}a_{qq}&a_{pq}\\ a_{pq}&a_{pp}\end{pmatrix}$ be a real symmetric matrix with $a_{qq}>0$, and $u=(\alpha,\tau)\in\mathbb R^2$. Put, as in (12)–(13),
--
--   $$
--   a=\frac{\det A+1}{4a_{qq}}-i\,\frac{a_{pq}}{2a_{qq}},\qquad b=-\frac{\det A-1}{4a_{qq}} .
--   $$
--
--   The **kernel of the displaced squeezed thermal state** with matrix $A$ and mean $u$ is
--
--   $$
--   K_{A,u}(x,y)=\frac{1}{\sqrt{\pi a_{qq}}}\exp\Big[-a(x-\alpha)^2-\bar a(y-\alpha)^2-2b(x-\alpha)(y-\alpha)+i\tau(x-y)\Big].
--   $$
--
--   It is the kernel $e^{i\tau(x-y)}\langle x-\alpha|\rho_2'|y-\alpha\rangle$ of (16), where $\rho_2'$ is the undisplaced state (15), normalized to trace $1$. When $A$ is positive definite with $\det A\ge1$, the operator with this kernel is the Gaussian state whose matrix (11) (twice the covariance matrix of $(Q,P)$) is $A$ and whose means are $\langle Q\rangle=\alpha$, $\langle P\rangle=\tau$ (theorems `characteristic_function`, `displaced_state_kernel`). The vacuum is $A=I$, $u=0$, with kernel $\pi^{-1/2}e^{-(x^2+y^2)/2}$.
--
--   **Formalization Note** `stateKernel A u`, with index $0$ for $Q$ and $1$ for $P$: $a_{qq}=A_{00}$, $a_{pq}=A_{01}$, $\alpha=u_0$, $\tau=u_1$. Only $A_{00}$, $A_{01}$ and $\det A$ enter. The constant $1/\sqrt{\pi a_{qq}}$ is the paper's $e^{g'}$ from the trace normalization on p.1, since $2(\operatorname{Re}a+b)=1/a_{qq}$. Expanded, the kernel is (16) with $l=2(a+b)\alpha+i\tau$ (the page prints $2(a+d)\alpha+i\tau$, a misprint corrected in `displaced_state_kernel`).
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eqs. (12), (13), (15), (16), p.2

import Mathlib

namespace ScutaruFid

/-- **Kernel of the displaced squeezed thermal state with covariance matrix `A` and mean `u`.**
Scutaru, arXiv:quant-ph/9708013v1, p.2, eqs. (12), (13), (15), (16) (with `l` corrected, see
below): "a = (detA + 1)/(4a_qq) − i a_pq/(2a_qq) (12), d = ā and b = −(detA − 1)/(4a_qq) (13)",
"<x|ρ′2|y> = exp[−(ax² + dy² + 2bxy) + g′] (15)", "<x|ρ2|y> = exp[iτ(x − y)] <x−α|ρ′2|y−α>".

For a real `2 × 2` matrix `A = [[a_qq, a_pq], [a_pq, a_pp]]` and `u = (α, τ)`, with
`a = (det A + 1)/(4 a_qq) − i a_pq/(2 a_qq)` and `b = −(det A − 1)/(4 a_qq)`,

`stateKernel A u x y = (π a_qq)^{−1/2} · exp(−a (x−α)² − ā (y−α)² − 2b (x−α)(y−α) + iτ(x − y))`.

**Formalization Note** `A` is normalized as in (11): `A = 2 ×` the covariance matrix of `(Q, P)`
with `ħ = 1`, so the vacuum has `A = I`; index `0` is `Q`, index `1` is `P`. Only the entries
`A 0 0 = a_qq`, `A 0 1 = a_pq` and `det A` enter (the mission's theorems assume `A` symmetric
positive definite with `det A ≥ 1`). `u 0 = α` is the mean of `Q` and `u 1 = τ` the mean of `P`.
The constant `(π a_qq)^{−1/2}` is the paper's `exp g′` from the trace normalization on p.1
(`g′ = −ln √(π/(2(Re a + b)))`, and `2(Re a + b) = 1/a_qq`). Expanded, the kernel is (16) with
`l = 2(a + b)α + iτ`; the page prints `l = 2(a + d)α + iτ`, a misprint (see the theorem
`displaced_state_kernel`). -/
noncomputable def stateKernel (A : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) (x y : ℝ) : ℂ :=
  let a : ℂ := (((A.det + 1) / (4 * A 0 0) : ℝ) : ℂ) - Complex.I * ((A 0 1 / (2 * A 0 0) : ℝ) : ℂ)
  let b : ℂ := ((-(A.det - 1) / (4 * A 0 0) : ℝ) : ℂ)
  let X : ℂ := ((x - u 0 : ℝ) : ℂ)
  let Y : ℂ := ((y - u 0 : ℝ) : ℂ)
  (((Real.sqrt (Real.pi * A 0 0))⁻¹ : ℝ) : ℂ) *
    Complex.exp (-(a * X ^ 2 + star a * Y ^ 2 + 2 * b * X * Y) +
      Complex.I * ((u 1 : ℝ) : ℂ) * (((x - y : ℝ)) : ℂ))

end ScutaruFid


