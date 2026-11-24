-- Prove2me | Definitions.Def_SelfDualLP_Regularity_Supplement_HLD
-- name    : SelfDualLP_Regularity_Supplement_HLD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:17:09.732193+00:00
-- url     : https://prove2.me/theorems/90d31472-fb34-4849-80de-95523b1ac638
-- title:
--   (HLP) as a general-form linear program and its linear-programming dual (HLD)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and initial vectors $x^0,s^0\in\mathbb R^n$, $y^0\in\mathbb R^m$. With $\bar b=b-Ax^0$, $\bar c=c-A^Ty^0-s^0$, $\bar z=c^Tx^0+1-b^Ty^0$ and $M=(x^0)^Ts^0+1$, the homogeneous program (HLP) is a linear program in $v=(y,x,\tau,\theta)\in\mathbb R^{m+n+2}$:
--   $$
--   \min\ M\theta\quad\text{s.t.}\quad K v\ \begin{matrix}=\\ \ge\\ \ge\\ =\end{matrix}\ \begin{pmatrix}0\\0\\0\\-M\end{pmatrix},\qquad
--   K=\begin{pmatrix}0&A&-b&\bar b\\-A^T&0&c&-\bar c\\ b^T&-c^T&0&\bar z\\-\bar b^T&\bar c^T&-\bar z&0\end{pmatrix},
--   $$
--   where the four block rows are the constraints (1)–(4), $y$ and $\theta$ are free, and $x\ge0$, $\tau\ge0$.
--
--   1. **The encoding of (HLP).** This program is recorded as a general-form linear program (constraint matrix, right-hand side, cost, a relation $=$ or $\ge$ for each row, a sign condition for each variable).
--   2. **(HLD).** The dual of (HLP) is computed from these data by the general LP duality rule (dual multipliers $y',x',\tau',\theta'$ for the constraints (1), (2), (3), (4); a free multiplier for each equality row, a nonnegative multiplier for each $\ge$ row; a dual equality for each free variable, a dual inequality for each nonnegative variable). The raw dual maximizes $p^T(0,0,0,-M)=-M\theta'$; it is stored in the equivalent minimization form, obtained by negating the objective and the dual constraints.
--   3. **Reading a vector as a point of (HLP).** A vector $v$ is read as the point $(y,x,\tau,\theta,s,\kappa)$ whose slacks $s$ and $\kappa$ are the values of the left-hand sides of constraints (2) and (3) at $v$.
--
--   These objects make Theorem 2 (i), "(HLD) is (HLP) with $(y,x,\tau,\theta)$ replaced by $(y',x',\tau',\theta')$", a statement about the dual actually computed from (HLP), rather than about a program written down to look like it.
--
--   **Formalization Note** The variable and row index is $\mathrm{Fin}(m+n+2)$, identified with the blocks $((y,x),(\tau,\theta))$ in this order through a fixed equivalence. The dual is the published operator `LinearOptimization.dualLP` (Bertsimas–Tsitsiklis, Table 4.1), whose feasible set is the textbook dual feasible set and whose objective $\min(-b)^Tp$ is the negative of the dual's $\max p^Tb$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 56, (HLP), (5) and the definition of (HLD) with multipliers y′, x′, τ′, θ′; DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix

namespace SelfDualLP.Regularity.Supplement

open SelfDualLP.Regularity LinearOptimization

/-- The block index `((y, x), (τ, θ))` of (HLP), in the paper's order: the variables
`(y, x, τ, θ)` for the columns and the constraints `(1), (2), (3), (4)` for the rows,
flattened to `Fin (m + n + 2)`. -/
def hlpIdx (m n : ℕ) : (Fin m ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1) ≃ Fin (m + n + 2) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- The constraint matrix of rows (1)--(4) of (HLP) (p. 56), columns `(y, x, τ, θ)`:
```
(1)  (   0,    A,  −b,   b̄ )
(2)  ( −Aᵀ,    0,   c,  −c̄ )
(3)  (  bᵀ,  −cᵀ,   0,   z̄ )
(4)  ( −b̄ᵀ,  c̄ᵀ,  −z̄,   0 )
``` -/
def hlpMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) :
    Matrix (Fin (m + n + 2)) (Fin (m + n + 2)) ℝ :=
  Matrix.reindex (hlpIdx m n) (hlpIdx m n) <|
    Matrix.fromBlocks
      (Matrix.fromBlocks 0 A (-Aᵀ) 0)
      (Matrix.fromBlocks
        (Matrix.of fun i (_ : Fin 1) => -b i)
        (Matrix.of fun i (_ : Fin 1) => bBar A b x₀ i)
        (Matrix.of fun j (_ : Fin 1) => c j)
        (Matrix.of fun j (_ : Fin 1) => -cBar A c y₀ s₀ j))
      (Matrix.fromBlocks
        (Matrix.of fun (_ : Fin 1) i => b i)
        (Matrix.of fun (_ : Fin 1) j => -c j)
        (Matrix.of fun (_ : Fin 1) i => -bBar A b x₀ i)
        (Matrix.of fun (_ : Fin 1) j => cBar A c y₀ s₀ j))
      (Matrix.fromBlocks 0
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => zBar b c x₀ y₀)
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => -zBar b c x₀ y₀) 0)

/-- (HLP) of p. 56 as a general-form linear program `min cᵀv` over `v = (y, x, τ, θ)`:
rows (1) and (4) are equalities, rows (2) and (3) are `≥ 0`; `y` and `θ` are free,
`x` and `τ` are nonnegative; the right-hand side is `(0, 0, 0, −(x⁰)ᵀs⁰ − 1)` and the
cost is `(0, 0, 0, (x⁰)ᵀs⁰ + 1)`. -/
def hlpLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) : GeneralFormLP (m + n + 2) (m + n + 2) where
  A := hlpMatrix A b c x₀ y₀ s₀
  b := fun r => Sum.elim (Sum.elim (fun _ => 0) (fun _ => 0))
    (Sum.elim (fun _ => 0) (fun _ => -(x₀ ⬝ᵥ s₀) - 1)) ((hlpIdx m n).symm r)
  c := fun r => Sum.elim (Sum.elim (fun _ => 0) (fun _ => 0))
    (Sum.elim (fun _ => 0) (fun _ => x₀ ⬝ᵥ s₀ + 1)) ((hlpIdx m n).symm r)
  rowRel := fun r => Sum.elim (Sum.elim (fun _ => ConstraintRel.eq) (fun _ => ConstraintRel.ge))
    (Sum.elim (fun _ => ConstraintRel.ge) (fun _ => ConstraintRel.eq)) ((hlpIdx m n).symm r)
  colSign := fun r => Sum.elim (Sum.elim (fun _ => VarSign.free) (fun _ => VarSign.nonneg))
    (Sum.elim (fun _ => VarSign.nonneg) (fun _ => VarSign.free)) ((hlpIdx m n).symm r)

/-- **(HLD)** (p. 56): the linear-programming dual of (HLP), computed by the general
dual operator `LinearOptimization.dualLP` (Table 4.1 of Bertsimas–Tsitsiklis), whose
variables are the multipliers `(y′, x′, τ′, θ′)` of the constraints (1)--(4). The raw dual
maximizes `p ⬝ᵥ (hlpLP …).b` over `generalFeasibleSet (HLD …)`; `dualLP` records it in
the equivalent minimization form `min (HLD …).c ⬝ᵥ p` with `(HLD …).c = −(hlpLP …).b`. -/
def HLD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) : GeneralFormLP (m + n + 2) (m + n + 2) :=
  dualLP (hlpLP A b c x₀ y₀ s₀)

/-- Read a flat vector `v = (y, x, τ, θ)` as a point `(y, x, τ, θ, s, κ)` of (HLP): the
four blocks are read off, and the slacks `s` and `κ` are the left-hand sides of the
constraints (2) and (3), i.e. the corresponding rows of `hlpMatrix` applied to `v`. -/
def toHLPPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) (v : Fin (m + n + 2) → ℝ) :
    HLPPoint m n where
  y := fun i => v (hlpIdx m n (Sum.inl (Sum.inl i)))
  x := fun j => v (hlpIdx m n (Sum.inl (Sum.inr j)))
  τ := v (hlpIdx m n (Sum.inr (Sum.inl 0)))
  θ := v (hlpIdx m n (Sum.inr (Sum.inr 0)))
  s := fun j => (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inl (Sum.inr j)))
  κ := (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inr (Sum.inl 0)))

end SelfDualLP.Regularity.Supplement


