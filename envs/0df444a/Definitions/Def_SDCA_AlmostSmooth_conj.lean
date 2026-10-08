-- Prove2me | Definitions.Def_SDCA_AlmostSmooth_conj
-- name    : SDCA_AlmostSmooth_conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:37.870159+00:00
-- url     : https://prove2.me/theorems/cfd5f167-02b8-46ec-82d0-5f4d2c61cff2
-- title:
--   The convex conjugate $\varphi^*(u)=\sup_z(zu-\varphi(z))$ of a scalar function, and scalar sub-gradients
-- statement:
--   Let $\varphi:\mathbb R\to\mathbb R$ be a scalar function. Its **convex conjugate** is the extended-real function
--
--   $$
--   \varphi^*(u)=\sup_{z\in\mathbb R}\bigl(zu-\varphi(z)\bigr)\in(-\infty,+\infty],\qquad u\in\mathbb R .
--   $$
--
--   It is never $-\infty$, since the choice $z=0$ gives the lower bound $-\varphi(0)$, and it may equal $+\infty$; for instance, for an $L$-Lipschitz $\varphi$ it is $+\infty$ whenever $|u|>L$.
--
--   Two notions of sub-gradient accompany it.
--
--   1. A real number $g$ is a **sub-gradient of $\varphi$ at $a$**, written $g\in\partial\varphi(a)$, if $\varphi(z)\ge\varphi(a)+g(z-a)$ for every $z\in\mathbb R$.
--   2. A real number $u$ is a **sub-gradient of $\varphi^*$ at $v$**, written $u\in\partial\varphi^*(v)$, if $\varphi^*(v)$ is finite and $\varphi^*(v')\ge\varphi^*(v)+u(v'-v)$ for every $v'\in\mathbb R$.
--
--   These are the conjugate and sub-differentials used throughout the paper: the dual problem (2) is written with the conjugates $\varphi_i^*$ of the losses, and the refined dual strong convexity condition (4) is stated with sub-gradients of $\varphi_i^*$.
--
--   **Formalization Note** The conjugate is the supremum in `EReal` of the real numbers $zu-\varphi(z)$, so an unbounded supremum is $+\infty$ rather than a junk real value. In $u\in\partial\varphi^*(v)$ the inequality is in `EReal` with the real term $u(v'-v)$ coerced, and finiteness of $\varphi^*(v)$ is part of the definition.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 2 (conjugate, sub-gradient notation) and p. 12 (sub-differential notation)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_conj

namespace SDCA.AlmostSmooth

/-- `g` is a sub-gradient of the scalar function `φ` at `a`, `g ∈ ∂φ(a)` (p. 2, p. 12):
`φ(z) ≥ φ(a) + g (z − a)` for every `z`. -/
def IsSubgrad (φ : ℝ → ℝ) (a g : ℝ) : Prop :=
  ∀ z : ℝ, φ a + g * (z - a) ≤ φ z

/-- `u` is a sub-gradient of the (`EReal`-valued) conjugate `φ*` at `v`, `u ∈ ∂φ*(v)`:
`φ*(v)` is finite and `φ*(v') ≥ φ*(v) + u (v' − v)` for every `v'`. -/
def IsConjSubgrad (φ : ℝ → ℝ) (v u : ℝ) : Prop :=
  SDCA.Lipschitz.conj φ v ≠ ⊤ ∧ ∀ v' : ℝ, SDCA.Lipschitz.conj φ v + ((u * (v' - v) : ℝ) : EReal) ≤ SDCA.Lipschitz.conj φ v'

end SDCA.AlmostSmooth


