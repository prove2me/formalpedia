-- Prove2me | Definitions.Def_SelfDualLP_Complexity_Termination
-- name    : SelfDualLP_Complexity_Termination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:10.605697+00:00
-- url     : https://prove2.me/theorems/b9acc6ad-3f54-47f6-ae18-0d5a9b8a59ee
-- title:
--   The least-squares termination projection and its rescaling
-- statement:
--   Let $z=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)$ be an iterate. Let $\sigma^k=\{j: x^k_j\ge s^k_j\}$, let $B$ be the columns of $A$ indexed by $\sigma^k$ and $N$ the remaining columns. A point $u=(y^*,x^*,\tau^*,\theta^*,s^*,\kappa^*)$ is a **termination output** at $z$ if $\theta^*=0$, $x^*_N=0$, $s^*_B=0$ and
--
--   1. **Case 1** ($\tau^k\ge\kappa^k$): $(y^*,x^*_B,\tau^*)$ minimizes $\|y^k-y\|^2+\|x^k_B-x_B\|^2+(\tau^k-\tau)^2$ subject to $Bx_B-b\tau=0$, $-B^Ty+c_B\tau=0$, $b^Ty-c_B^Tx_B=0$; and $s^*_N=c_N\tau^*-N^Ty^*$, $\kappa^*=0$;
--   2. **Case 2** ($\tau^k<\kappa^k$): $(y^*,x^*_B,\kappa^*)$ minimizes $\|y^k-y\|^2+\|x^k_B-x_B\|^2+(\kappa^k-\kappa)^2$ subject to $Bx_B=0$, $-B^Ty=0$, $b^Ty-c_B^Tx_B-\kappa=0$; and $s^*_N=-N^Ty^*$, $\tau^*=0$.
--
--   The projection imposes only homogeneous constraints, so its output is rescaled to the normalization (9) $e^Tx+e^Ts+\tau+\kappa-(n+1)\theta=n+1$: the **rescaled output** is $\lambda u$ with $\lambda=(n+1)/(e^Tx^*+e^Ts^*+\tau^*+\kappa^*)$.
--
--   **Formalization Note** Vectors keep full length $n$; $x_B$ is represented by an $x$ vanishing off $\sigma^k$. The minimizer exists and is unique (a strictly convex quadratic over a nonempty subspace), but the definition is relational ("$u$ is built from a minimizer") and does not choose it. Ties $x_j^k=s_j^k$ go to $B$, as in the paper.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 61, Termination (Cases 1 and 2); normalization (9) on p. 58

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- `σᵏ = {j : x_jᵏ ≥ s_jᵏ}`; `B` is the set of columns of `A` indexed by `σᵏ`, `N` the rest. -/
noncomputable def sigmaSet {m n : ℕ} (z : HLPPoint m n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => z.s j ≤ z.x j)

/-- Feasible set of the Case 1 projection (p. 61), for full-length `x` vanishing off `σ`
(so `Bx_B = Ax`, `c_Bᵀx_B = cᵀx`): `Bx_B − bτ = 0`, `−Bᵀy + c_Bτ = 0`, `bᵀy − c_Bᵀx_B = 0`. -/
def Case1Feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (σ : Finset (Fin n)) (y : Fin m → ℝ) (x : Fin n → ℝ) (τ : ℝ) : Prop :=
  (∀ j, j ∉ σ → x j = 0) ∧
  A *ᵥ x - τ • b = 0 ∧
  (∀ j ∈ σ, -(Aᵀ *ᵥ y) j + c j * τ = 0) ∧
  b ⬝ᵥ y - c ⬝ᵥ x = 0

/-- Feasible set of the Case 2 projection (p. 61), for full-length `x` vanishing off `σ`:
`Bx_B = 0`, `−Bᵀy = 0`, `bᵀy − c_Bᵀx_B − κ = 0`. -/
def Case2Feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (σ : Finset (Fin n)) (y : Fin m → ℝ) (x : Fin n → ℝ) (κ : ℝ) : Prop :=
  (∀ j, j ∉ σ → x j = 0) ∧
  A *ᵥ x = 0 ∧
  (∀ j ∈ σ, -(Aᵀ *ᵥ y) j = 0) ∧
  b ⬝ᵥ y - c ⬝ᵥ x - κ = 0

/-- The least-squares distance `‖yᵏ − y‖² + ‖x_Bᵏ − x_B‖² + (tᵏ − t)²` (the last coordinate is
`τ` in Case 1 and `κ` in Case 2). -/
def projDist {m n : ℕ} (σ : Finset (Fin n)) (yk : Fin m → ℝ) (xk : Fin n → ℝ) (tk : ℝ)
    (y : Fin m → ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, (yk i - y i) ^ 2) + (∑ j ∈ σ, (xk j - x j) ^ 2) + (tk - t) ^ 2

/-- `u` is the output of the termination technique (least-squares projection, p. 61) applied to
the iterate `z = (yᵏ, xᵏ, τᵏ, θᵏ, sᵏ, κᵏ)`, with `σ = σᵏ`:
* **Case 1** (`τᵏ ≥ κᵏ`): `(u.y, u.x_B, u.τ)` minimizes `‖yᵏ − y‖² + ‖x_Bᵏ − x_B‖² + (τᵏ − τ)²`
  subject to `Bx_B − bτ = 0`, `−Bᵀy + c_Bτ = 0`, `bᵀy − c_Bᵀx_B = 0`; and `x_N = 0`,
  `s_B = 0`, `s_N = c_Nτ − Nᵀy`, `θ = 0`, `κ = 0`.
* **Case 2** (`τᵏ < κᵏ`): `(u.y, u.x_B, u.κ)` minimizes `‖yᵏ − y‖² + ‖x_Bᵏ − x_B‖² + (κᵏ − κ)²`
  subject to `Bx_B = 0`, `−Bᵀy = 0`, `bᵀy − c_Bᵀx_B − κ = 0`; and `x_N = 0`, `s_B = 0`,
  `s_N = −Nᵀy`, `θ = 0`, `τ = 0`.
The output is not rescaled: it satisfies only the homogeneous rows; see `rescaleOutput`. -/
def IsTerminationOutput {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z u : HLPPoint m n) : Prop :=
  let σ := sigmaSet z
  u.θ = 0 ∧ (∀ j ∈ σ, u.s j = 0) ∧
  ((z.κ ≤ z.τ ∧ u.κ = 0 ∧
      (∀ j, j ∉ σ → u.s j = c j * u.τ - (Aᵀ *ᵥ u.y) j) ∧
      Case1Feasible A b c σ u.y u.x u.τ ∧
      ∀ y x τ, Case1Feasible A b c σ y x τ →
        projDist σ z.y z.x z.τ u.y u.x u.τ ≤ projDist σ z.y z.x z.τ y x τ) ∨
   (z.τ < z.κ ∧ u.τ = 0 ∧
      (∀ j, j ∉ σ → u.s j = -(Aᵀ *ᵥ u.y) j) ∧
      Case2Feasible A b c σ u.y u.x u.κ ∧
      ∀ y x κ, Case2Feasible A b c σ y x κ →
        projDist σ z.y z.x z.κ u.y u.x u.κ ≤ projDist σ z.y z.x z.κ y x κ))

/-- The rescaling of a termination output `u` to the normalization (9) with `θ = 0`:
`λ u` with `λ = (n + 1)/(eᵀx + eᵀs + τ + κ)`. -/
noncomputable def rescaleOutput {m n : ℕ} (u : HLPPoint m n) : HLPPoint m n :=
  HLPPoint.smul (((n : ℝ) + 1) / ((∑ j, u.x j) + (∑ j, u.s j) + u.τ + u.κ)) u

end SelfDualLP.Complexity


