-- Prove2me | Definitions.Def_SmoothNestedSim_RKHS
-- name    : SmoothNestedSim_RKHS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:01.425002+00:00
-- url     : https://prove2.me/theorems/6d5b9c0c-00a5-455a-b30d-fae5f7685326
-- title:
--   RKHS $\mathcal N_k(\Omega)$ of a kernel, as a set of functions
-- statement:
--   Let $k$ be a positive definite kernel on $E$ and $\Omega\subseteq E$. The paper defines $\mathcal N^0_k(\Omega)$ as the space of functions $x\mapsto\sum_{i=1}^n\beta_i k(x,x_i)$ ($n\ge1$, $\beta_i\in\mathbb R$, $x_i\in\Omega$) with the inner product $\langle\sum_i\beta_i k(\cdot,x_i),\sum_j\tilde\beta_j k(\cdot,\tilde x_j)\rangle:=\sum_i\sum_j\beta_i\tilde\beta_j k(x_i,\tilde x_j)$, and the **RKHS** $\mathcal N_k(\Omega)$ as the closure of $\mathcal N^0_k(\Omega)$ with respect to the induced norm.
--
--   Realised as functions on $\Omega$, $\mathcal N_k(\Omega)$ is the set of $f$ for which some finite $C$ satisfies
--
--   $$
--   \Bigl(\sum_{i=1}^N c_i f(x_i)\Bigr)^2 \le C\sum_{i,j=1}^N c_i c_j k(x_i,x_j)\quad\text{for all } N,\ c\in\mathbb R^N,\ x\in\Omega^N .
--   $$
--
--   With the Matérn kernel this is the space $\mathcal N_\Psi(\Omega)$ of Assumption 3, norm-equivalent to the Sobolev space of order $\nu+d/2$.
--
--   **Formalization Note** Functions are taken on the whole space $E$; only their values on $\Omega$ matter. The description by the displayed inequality coincides with the closure construction for positive definite kernels (Aronszajn's criterion).
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3, p.11 (definition of N_k(Ω)); p.12 (N_Ψ(Ω))

import Mathlib
import Definitions.Def_SmoothNestedSim_IsRKHSBound

namespace SmoothNestedSim

/-- **The RKHS `N_k(Ω)` induced by a kernel `k` on `Ω`, as a set of functions** (Wang, Wang,
Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6, §3, p.11: "the RKHS induced by `k`,
denoted by `N_k(Ω)`, is defined as the closure of `N⁰_k(Ω)` with respect to the norm
`‖·‖_{N⁰_k(Ω)}`"). A function `f` belongs to `N_k(Ω)` when some finite `C` bounds its squared
RKHS norm in the sense of `IsRKHSBound`.

**Formalization Note.** Functions are taken on the whole ambient space `E` and only their
values on `Ω` matter: `f` and `g` that agree on `Ω` are both members or both not, with the same
norm. For a positive definite `k` (the Matérn kernel with `ν > 0`), this set is exactly the
closure of `N⁰_k(Ω)` realised as functions on `Ω` (Moore–Aronszajn), by Aronszajn's
criterion (see `IsRKHSBound`). -/
def RKHS {E : Type*} (k : E → E → ℝ) (Ω : Set E) : Set (E → ℝ) :=
  {f | ∃ C : ℝ, IsRKHSBound k Ω f C}

end SmoothNestedSim


