-- Prove2me | Definitions.Def_RestartPD_LPSharp_LP
-- name    : RestartPD_LPSharp_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:16.807978+00:00
-- url     : https://prove2.me/theorems/e79dbd41-2dc9-4d85-a8ce-2b83f11ade4f
-- title:
--   (17)–(20), pp. 13–14 — the LP Lagrangian (19), F(z), the KKT system Kz ≥ h of (20), the residual ‖(h − Kz)⁺‖ and v
-- statement:
--   The standard-form linear program and its primal-dual objects. Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and consider
--   $$\min_{x\in\mathbb R^n} c^\top x\ \text{ s.t. } Ax=b,\ x\ge0, \qquad (17)$$
--   its dual $\max_{y} b^\top y$ s.t. $A^\top y\le c$ (18), and its Lagrangian form
--   $$\min_{x\ge0}\max_{y\in\mathbb R^m} L(x,y)=c^\top x+y^\top b-y^\top Ax. \qquad (19)$$
--   Here $X=\{x\in\mathbb R^n: x\ge0\}$, $Y=\mathbb R^m$.
--
--   1. $F(z)=(c-A^\top y,\ Ax-b)$, the vector $(\nabla_x L,-\nabla_y L)$.
--   2. The KKT system (20) is $Kz\ge h$ with
--   $$K=\begin{pmatrix} I & 0\\ -A & 0\\ A & 0\\ 0 & -A^\top\\ -c^\top & b^\top\end{pmatrix},\qquad h=\begin{pmatrix}0\\-b\\b\\-c\\0\end{pmatrix},$$
--   i.e. $x\ge0$, $Ax=b$, $A^\top y\le c$, $c^\top x\le b^\top y$.
--   3. The **KKT residual** $\|(h-Kz)^+\|$: the Euclidean norm, over all $2n+2m+1$ rows, of the componentwise positive part of $h-Kz$.
--   4. The vector $v=\big((-c+A^\top y)^+,\ b-Ax\big)$ used in the proof of Lemma 4.
--
--   The residual $\|(h-Kz)^+\|$ is the usual termination metric of LP solvers; the paper bounds it by the normalized duality gap.
--
--   **Formalization Note** The paper prints (18) as "$A^\top y\ge c$"; $K$ and $h$ are built exactly as (20) prints them, which encodes $A^\top y\le c$, the dual of (17). Vectors live in `EuclideanSpace`; $A$ acts through `Matrix.toEuclideanLin`. The row index of (20) is the sum type of the five row blocks.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, pp. 13–14, (17)–(20), proof of Lemma 4 (v, F(z))

import Mathlib
import Definitions.Def_RestartPD_LPSharp_PrimalDual

namespace RestartPD.LPSharp

open scoped InnerProductSpace Matrix

variable {n m : ℕ}

/-- The Lagrangian (19) of the standard-form LP (17): `L(x, y) = cᵀx + yᵀb − yᵀAx`. -/
noncomputable def lpL (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ⟪c, x⟫_ℝ + ⟪y, b⟫_ℝ - ⟪y, Matrix.toEuclideanLin A x⟫_ℝ

/-- The primal feasible region of (19): `X = {x ∈ ℝⁿ | x ≥ 0}` (and `Y = ℝᵐ`). -/
def lpX : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, 0 ≤ x i}

/-- `F(z) = (∇ₓL(x, y), −∇_yL(x, y)) = (c − Aᵀy, Ax − b)` for the Lagrangian (19). -/
noncomputable def lpF (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) : PDSpace n m :=
  (c - Matrix.toEuclideanLin Aᵀ z.2, Matrix.toEuclideanLin A z.1 - b)

/-- Row index of the KKT system (20): the five row blocks of `K` and `h`, in order. -/
abbrev KRow (n m : ℕ) := Fin n ⊕ Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit

/-- `Kz` for the matrix `K` of (20). -/
noncomputable def Kz (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) : KRow n m → ℝ
  | Sum.inl i => z.1 i                                                      -- row block ( I    0  )
  | Sum.inr (Sum.inl j) => -(Matrix.toEuclideanLin A z.1) j                 -- row block ( −A   0  )
  | Sum.inr (Sum.inr (Sum.inl j)) => (Matrix.toEuclideanLin A z.1) j        -- row block ( A    0  )
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => -(Matrix.toEuclideanLin Aᵀ z.2) i  -- ( 0  −Aᵀ )
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => -⟪c, z.1⟫_ℝ + ⟪b, z.2⟫_ℝ     -- row block ( −cᵀ  bᵀ )

/-- The right-hand side `h` of (20). -/
def hvec (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) : KRow n m → ℝ
  | Sum.inl _ => 0                                        -- block 0
  | Sum.inr (Sum.inl j) => -b j                           -- block −b
  | Sum.inr (Sum.inr (Sum.inl j)) => b j                  -- block b
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => -c i       -- block −c
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0          -- block 0

/-- The KKT residual `‖(h − Kz)⁺‖`: the Euclidean norm, over all `2n + 2m + 1` rows of (20), of the
componentwise positive part of `h − Kz`. -/
noncomputable def kktRes (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => max (hvec b c i - Kz A b c z i) 0) : EuclideanSpace ℝ (KRow n m))‖

/-- The vector `v = ((−c + Aᵀy)⁺, b − Ax)` of the proof of Lemma 4 (p. 14). -/
noncomputable def vvec (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) : PDSpace n m :=
  (WithLp.toLp 2 (fun i => max ((Matrix.toEuclideanLin Aᵀ z.2) i - c i) 0),
    b - Matrix.toEuclideanLin A z.1)

end RestartPD.LPSharp


