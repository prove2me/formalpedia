-- Prove2me | Definitions.Def_NoetherIVP_core
-- name    : NoetherIVP_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T14:38:44.133236+00:00
-- url     : https://prove2.me/theorems/9497fa87-869d-4fab-8e88-df8a657a5784
-- title:
--   Noether 1918: the first-order variational set-up
-- statement:
--   This file sets up the objects of Emmy Noether's *Invariante Variationsprobleme* (1918)
--   for a first-order variational problem with $n$ independent variables
--   $x = (x_1,\dots,x_n)$ and $m$ dependent variables $u = (u_1,\dots,u_m)$.
--
--   **Derivatives on the base.** For a scalar function $g$ on $\mathbb{R}^n$, $\partial_l g(x)$
--   is the derivative of $g$ at $x$ in the direction of the $l$-th standard basis vector, and
--   the divergence of a vector field $A = (A_1,\dots,A_n)$ is
--   $\operatorname{Div}A(x) = \sum_{l} \partial_l A_l(x)$. For a field
--   $u : \mathbb{R}^n \to \mathbb{R}^m$, the array of first derivatives is
--   $(\partial u)(x)_{l i} = \partial_l u_i(x)$.
--
--   **The Lagrangian and its partial derivatives.** A Lagrangian is a function $f(x,q,v)$ with
--   $q \in \mathbb{R}^m$ and $v \in \mathbb{R}^{n\times m}$. Its partial derivatives
--   $\partial f/\partial q_i$ and $\partial f / \partial v_{l i}$ are the derivatives of the
--   partially applied maps $q \mapsto f(x,q,v)$ and $v \mapsto f(x,q,v)$ in the direction of the
--   corresponding basis vector. Along a field $u$, $f[u](x) = f(x,u(x),(\partial u)(x))$ and the
--   **momenta** are $p_{l i}[u](x) = (\partial f/\partial v_{l i})(x,u(x),(\partial u)(x))$.
--
--   **Lagrange expressions.** $\psi_i[u](x) = (\partial f/\partial q_i)(x,u(x),(\partial u)(x))
--   - \sum_l \partial_l p_{l i}[u](x)$: the left-hand sides of the Euler–Lagrange equations.
--
--   **Variations.** Given a variation field $\delta u$, the variation of the Lagrangian at fixed
--   $x$ is $\delta f = \sum_i \bigl( (\partial f/\partial q_i)\,\delta u_i + \sum_l (\partial f/\partial v_{l i})\,\partial_l \delta u_i \bigr)$;
--   the partial-integration vector of equation (3) is $A_l = -\sum_i p_{l i}\,\delta u_i$;
--   and Noether's vector of equation (12) is $B_l = A_l - f[u]\,\Delta x_l$. Equation (9),
--   which converts the generators $\Delta u, \Delta x$ of an infinitesimal transformation into a
--   variation at fixed $x$, is $\delta u_i = \Delta u_i - \sum_l (\partial_l u_i)\,\Delta x_l$.
-- source:
--   E. Noether, Invariante Variationsprobleme, Nachr. Ges. Wiss. Göttingen, Math-phys. Kl. (1918) 235-257; Tavel translation, arXiv:physics/0503066v3, §1-§2, pp. 1-5, equations (2), (3), (9), (12).

import Mathlib

/-!
# Noether, *Invariante Variationsprobleme* (1918) — the variational set-up

Formal counterparts of the objects Noether uses in §1–§2 of the paper, in the case of
`n` independent variables `x₁, …, xₙ`, `m` dependent variables `u₁, …, u_m`, and a
Lagrangian depending on the `u`'s and their first derivatives.
-/

namespace NoetherIVP

open Finset

/-- Partial derivative of a scalar field on `ℝⁿ` along the `l`-th coordinate. -/
noncomputable def dirD {n : ℕ} (l : Fin n) (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single l 1)

/-- Divergence `Div A = ∂A₁/∂x₁ + … + ∂Aₙ/∂xₙ` of a vector field on `ℝⁿ`. -/
noncomputable def divg {n : ℕ} (A : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ l : Fin n, dirD l (fun y => A y l) x

/-- The array of first derivatives `∂uᵢ/∂x_l` of a field `u : ℝⁿ → ℝᵐ`. -/
noncomputable def jac {n m : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) :
    Fin n → Fin m → ℝ := fun l i => dirD l (fun y => u y i) x

/-- Partial derivative `∂f/∂uᵢ` of the Lagrangian. -/
noncomputable def pdU {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ) (i : Fin m)
    (x : Fin n → ℝ) (q : Fin m → ℝ) (v : Fin n → Fin m → ℝ) : ℝ :=
  fderiv ℝ (fun w : Fin m → ℝ => f x w v) q (Pi.single i 1)

/-- Partial derivative `∂f/∂(∂uᵢ/∂x_l)` of the Lagrangian. -/
noncomputable def pdV {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ) (l : Fin n) (i : Fin m)
    (x : Fin n → ℝ) (q : Fin m → ℝ) (v : Fin n → Fin m → ℝ) : ℝ :=
  fderiv ℝ (fun w : Fin n → Fin m → ℝ => f x q w) v (Pi.single l (Pi.single i 1))

/-- The Lagrangian evaluated along a field `u`. -/
noncomputable def lagr {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) : ℝ := f x (u x) (jac u x)

/-- The momentum `∂f/∂(∂uᵢ/∂x_l)` evaluated along a field `u`. -/
noncomputable def mom {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ) (u : (Fin n → ℝ) → Fin m → ℝ)
    (l : Fin n) (i : Fin m) (x : Fin n → ℝ) : ℝ := pdV f l i x (u x) (jac u x)

/-- The Lagrange expression `ψᵢ = ∂f/∂uᵢ - Σ_l ∂/∂x_l (∂f/∂(∂uᵢ/∂x_l))`. -/
noncomputable def lagrangeExpr {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ) (u : (Fin n → ℝ) → Fin m → ℝ)
    (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  pdU f i x (u x) (jac u x) - ∑ l : Fin n, dirD l (mom f u l i) x

/-- The variation `δf` of the Lagrangian produced by a variation field `δu` of the `u`'s
(the independent variables being held fixed). -/
noncomputable def varF {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, (pdU f i x (u x) (jac u x) * du x i
    + ∑ l : Fin n, pdV f l i x (u x) (jac u x) * dirD l (fun y => du y i) x)

/-- The boundary vector `A` produced by the partial integration in equation (3):
`A_l = -Σᵢ (∂f/∂(∂uᵢ/∂x_l)) δuᵢ`. -/
noncomputable def bdryA {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) (l : Fin n) : ℝ :=
  -∑ i : Fin m, mom f u l i x * du x i

/-- Noether's vector `B = A - f · Δx` of equation (12). -/
noncomputable def curB {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ)
    (x : Fin n → ℝ) (l : Fin n) : ℝ := bdryA f u du x l - lagr f u x * dx x l

/-- Equation (9): the variation `δuᵢ = Δuᵢ - Σ_l (∂uᵢ/∂x_l) Δx_l` attached to an
infinitesimal transformation with generators `Δu` and `Δx`. -/
noncomputable def deltaU {n m : ℕ} (u Du : (Fin n → ℝ) → Fin m → ℝ)
    (dx : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  Du x i - ∑ l : Fin n, jac u x l i * dx x l

end NoetherIVP


