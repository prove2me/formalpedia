-- Prove2me | Definitions.Def_PsiPhi
-- name    : PsiPhi
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-28T09:29:35.009066+00:00
-- url     : https://prove2.me/theorems/a9b940c3-3eb1-4829-a724-3648dcee00ab
-- title:
--   The stretching reparameterisation of a half-line and its explicit inverse
-- statement:
--   For a natural number $n$ we define two functions on the real line. The first, $\psi_n$, is the identity on the ray $(-\infty, n]$ and on the short interval $(n, n+1)$ is given by $n + \frac{x-n}{n+1-x}$. The second, $\varphi_n$, is the identity on $(-\infty, n]$ and on $(n, \infty)$ is given by $n + \frac{y-n}{1+y-n}$. The two are inverse to one another wherever both are defined: writing $u = x-n \in (0,1)$ the map $\psi_n$ sends $u$ to $u/(1-u)$, while writing $v = y-n > 0$ the map $\varphi_n$ sends $v$ to $v/(1+v)$, and these are literal algebraic inverses. The map $\psi_n$ is a homeomorphism from the open half-line $\{x : x < n+1\}$ onto all of $\mathbb{R}$.
-- source:
--   Auxiliary definitions for BraidsLinksMCG.puncturedPlane_succ_left_factor_homeomorph_v1.

import Mathlib

namespace PsiPhi

noncomputable section

/-- `psi_n` on all of `ℝ`, used on the domain `{x : ℝ // x < n + 1}`. -/
def psi (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ n then x else n + (x - n) / (n + 1 - x)

/-- `phi_n` on all of `ℝ`; its values always land in `{x : ℝ // x < n + 1}`. -/
def phi (n : ℕ) (y : ℝ) : ℝ :=
  if y ≤ n then y else n + (y - n) / (1 + y - n)

end

end PsiPhi


