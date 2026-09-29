-- Prove2me | Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
-- name    : ThreeOpSplitting_Accel_Algorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:57:34.262504+00:00
-- url     : https://prove2.me/theorems/d0892c1f-8a8a-428f-84ee-e2a2d31c185f
-- title:
--   Algorithm 3 — the three-operator splitting scheme with varying stepsizes (recursion (3.8))
-- statement:
--   Let $H$ be a real vector space, let $J_A, J_B : \mathbb{R} \to (H \to H)$ be two families of maps ($J_A(\gamma)$ plays the role of the resolvent $J_{\gamma A}$), let $C : H \to H$, let $(\gamma_k)_{k \ge 0}$ be a sequence of stepsizes and let $x_A^0 \in H$. **Algorithm 3** (Algorithm 1 with acceleration) produces the sequence of states $(x_A^k, x_B^k, u_B^k)_{k \ge 0}$ defined by
--   $$x_B^0 = J_{\gamma_0 B}(x_A^0), \qquad u_B^0 = \tfrac{1}{\gamma_0}\big(x_A^0 - J_{\gamma_0 B}(x_A^0)\big),$$
--   and, for $k \ge 0$ (recursion (3.8)),
--   $$\begin{aligned} x_B^{k+1} &= J_{\gamma_k B}(x_A^k + \gamma_k u_B^k),\\ u_B^{k+1} &= \tfrac{1}{\gamma_k}\big(x_A^k + \gamma_k u_B^k - x_B^{k+1}\big),\\ x_A^{k+1} &= J_{\gamma_{k+1} A}\big(x_B^{k+1} - \gamma_{k+1} u_B^{k+1} - \gamma_{k+1} C x_B^{k+1}\big). \end{aligned}$$
--
--   The stepsize changes in the middle of an iteration: $x_B^{k+1}$ and $u_B^{k+1}$ use $\gamma_k$, while $x_A^{k+1}$ already uses $\gamma_{k+1}$. With a constant stepsize the scheme reduces to Algorithm 1 with relaxation $\lambda_k \equiv 1$ under the change of variable $z^k = x_A^{k-1} + \gamma_{k-1} u_B^{k-1}$. The initial point $x_A^0$ is free; the $z^0$ mentioned in the paper's Algorithm 3 is never used.
--
--   **Formalization Note** The iteration is a function of $x_A^0$, the stepsize sequence, the two resolvent families and $C$; the three components are the fields `xA`, `xB`, `uB` of the state. Indices are those of the paper: the paper's Algorithm 3 loop at $k = 1, 2, \dots$ is the $k \mapsto k+1$ step here, identical to (3.8).
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 842, Algorithm 3 and recursion (3.8) of Proposition 3.1

import Mathlib

namespace ThreeOpSplitting.Accel

/-- The state `(x_A^k, x_B^k, u_B^k)` of Algorithm 3 after `k` iterations. -/
structure AccelState (H : Type*) where
  /-- `x_A^k` -/
  xA : H
  /-- `x_B^k` -/
  xB : H
  /-- `u_B^k` -/
  uB : H

/-- Algorithm 3 of Davis–Yin (Algorithm 1 with acceleration), equivalently recursion (3.8),
with resolvent families `JA γ = J_{γA}`, `JB γ = J_{γB}`, single-valued `C`, stepsizes
`γ : ℕ → ℝ` and initial point `x_A^0 = xA0`:

* `x_B^0 = J_{γ₀B}(x_A^0)`, `u_B^0 = (1/γ₀)(x_A^0 - x_B^0)`;
* for `k ≥ 0`:
  `x_B^{k+1} = J_{γ_k B}(x_A^k + γ_k u_B^k)`,
  `u_B^{k+1} = (1/γ_k)(x_A^k + γ_k u_B^k - x_B^{k+1})`,
  `x_A^{k+1} = J_{γ_{k+1} A}(x_B^{k+1} - γ_{k+1} u_B^{k+1} - γ_{k+1} C x_B^{k+1})`. -/
noncomputable def accelIter {H : Type*} [AddCommGroup H] [Module ℝ H]
    (JA JB : ℝ → H → H) (C : H → H) (γ : ℕ → ℝ) (xA0 : H) : ℕ → AccelState H
  | 0 =>
    { xA := xA0
      xB := JB (γ 0) xA0
      uB := (γ 0)⁻¹ • (xA0 - JB (γ 0) xA0) }
  | k + 1 =>
    let s := accelIter JA JB C γ xA0 k
    let xB' := JB (γ k) (s.xA + γ k • s.uB)
    let uB' := (γ k)⁻¹ • (s.xA + γ k • s.uB - xB')
    { xA := JA (γ (k + 1)) (xB' - γ (k + 1) • uB' - γ (k + 1) • C xB')
      xB := xB'
      uB := uB' }

end ThreeOpSplitting.Accel


