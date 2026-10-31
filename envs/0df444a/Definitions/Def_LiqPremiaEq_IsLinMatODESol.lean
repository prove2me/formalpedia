-- Prove2me | Definitions.Def_LiqPremiaEq_IsLinMatODESol
-- name    : LiqPremiaEq_IsLinMatODESol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:03.860116+00:00
-- url     : https://prove2.me/theorems/60bda3d2-89ef-4c11-bca7-88aad8a22ede
-- title:
--   Solutions of the linear matrix ODE $Y'(\tau)=A(\tau)Y(\tau)$, $Y(0)=I$, on an interval
-- statement:
--   Let $I\subseteq\mathbb R$ be a set containing $0$ (an interval $[0,T]$ or $[0,T')$) and $A:\mathbb R\to\mathbb R^{m\times m}$. A function $Y:\mathbb R\to\mathbb R^{m\times m}$ **solves the linear matrix ODE**
--
--   $$Y'(\tau)=A(\tau)Y(\tau),\qquad Y(0)=I_m\qquad(7.3)$$
--
--   on $I$ if $Y(0)=I_m$ and at every $\tau\in I$ the derivative of $Y$ within $I$ (one-sided at an endpoint) equals $A(\tau)Y(\tau)$.
--
--   The ODEs (4.9) and (7.7) for the fundamental matrices $\Phi$ and $\Phi_F$ have this form.
--
--   **Formalization Note** Derivatives of matrix functions are taken entrywise (`HasMatDerivWithinAt`), so that no norm instance on matrices is needed. Linear ODEs with continuous coefficients have unique solutions, so "the solution" of the paper is any `Y` satisfying the predicate.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eq. (7.3), p.17; eqs. (4.9), p.8 and (7.7), p.18

import Mathlib

open Matrix

namespace LiqPremiaEq

/-- `F' = G` at `τ` within the set `I`, for a matrix-valued function of one real variable:
every entry `τ ↦ F(τ)ᵢⱼ` has derivative `Gᵢⱼ` at `τ` within `I`.

**Formalization Note** Matrix derivatives are taken entrywise, so that no norm instance on
`Matrix m n ℝ` is needed; on a finite-dimensional space this is the same derivative as for any
norm. At an endpoint of an interval the derivative is one-sided. -/
def HasMatDerivWithinAt {m n : Type*} (F : ℝ → Matrix m n ℝ) (G : Matrix m n ℝ) (I : Set ℝ)
    (τ : ℝ) : Prop :=
  ∀ i j, HasDerivWithinAt (fun x => F x i j) (G i j) I τ

/-- `Y` solves the linear matrix ODE `Y'(τ) = A(τ) Y(τ)`, `Y(0) = I`, on the set `I ∋ 0`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (7.3), p.17; the same form as (4.9) (p.8) and
(7.7) (p.18).

**Formalization Note** The ODE is required at every point of `I` with derivatives within `I`
(one-sided at the endpoints). Linear ODEs with continuous coefficients have unique solutions, so
"the unique solution" of the paper is any `Y` satisfying this predicate. -/
def IsLinMatODESol {m : Type*} [Fintype m] [DecidableEq m] (I : Set ℝ)
    (A : ℝ → Matrix m m ℝ) (Y : ℝ → Matrix m m ℝ) : Prop :=
  Y 0 = 1 ∧ ∀ τ ∈ I, HasMatDerivWithinAt Y (A τ * Y τ) I τ

end LiqPremiaEq


