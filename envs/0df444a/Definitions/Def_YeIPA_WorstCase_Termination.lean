-- Prove2me | Definitions.Def_YeIPA_WorstCase_Termination
-- name    : YeIPA_WorstCase_Termination
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:51.696984+00:00
-- url     : https://prove2.me/theorems/20bdb666-d6af-4ecc-a66d-d0182d6f5599
-- title:
--   Standard-form LP, the strict complementarity partition $(P^*,Z^*)$, the optimal faces $\Omega_p,\Omega_d$, the condition number $\xi(A,b,c)$ (5.3), $\sigma^k$ and property (5.7)
-- statement:
--   Fix a real $m\times n$ matrix $A$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$, and consider the standard-form pair
--   $$(\mathrm{LP})\ \min\{c^Tx: Ax=b,\ x\ge0\},\qquad (\mathrm{LD})\ \max\{b^Ty: A^Ty+s=c,\ s\ge0\}.$$
--   Vector inequalities are componentwise. This module defines the objects of Section 5.2 of Ye's *Interior Point Algorithms*:
--
--   1. **Feasibility and optimality.** $x$ is primal feasible if $Ax=b$, $x\ge0$; $(y,s)$ is dual feasible if $A^Ty+s=c$, $s\ge0$; $(x,y,s)$ is an **interior point** if moreover $x>0$ and $s>0$. A primal feasible $x$ is optimal if $c^Tx\le c^Tx'$ for every primal feasible $x'$; a dual feasible $(y,s)$ is optimal if $b^Ty'\le b^Ty$ for every dual feasible $(y',s')$.
--   2. **The strict complementarity partition** (Theorem 1.14, p. 20): $P^*=\{j: x_j>0$ for some optimal $x\}$ and $Z^*=\{j: s_j>0$ for some optimal $(y,s)\}$.
--   3. **The optimal faces** (p. 153): $\Omega_p=\{x: Ax=b,\ x\ge0,\ x_{Z^*}=0\}$ and $\Omega_d=\{(y,s): A^Ty+s=c,\ s\ge0,\ s_{P^*}=0\}$.
--   4. **The condition number** (5.3):
--   $$\xi_p(A,b,c)=\min_{j\in P^*}\max_{x\in\Omega_p}x_j,\qquad \xi_d(A,b,c)=\min_{j\in Z^*}\max_{(y,s)\in\Omega_d}s_j,\qquad \xi(A,b,c)=\min\{\xi_p(A,b,c),\xi_d(A,b,c)\}.$$
--   5. **The index set** $\sigma(x,s)=\{j: x_j\ge s_j\}$ (p. 154).
--   6. **Property (5.7)** of a positive pair $(x,s)$ with constant $\eta$: $\min(Xs)/(x^Ts)>n^{-\eta}$, where $X=\operatorname{diag}(x)$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$; matrices are `Matrix (Fin m) (Fin n) ℝ`. The partition is defined by supports of optimal solutions, which is the book's $(P^*,Z^*)$ whenever optimal solutions exist (Theorem 1.14); no definition assumes that they do. The faces are written on full vectors: $\Omega_p$ as feasible $x$ vanishing on $Z^*$, $\Omega_d$ with the full slack $s=c-A^Ty$ vanishing on $P^*$. Each $\max$ is Lean's `sSup` of the coordinate over the face; it is a genuine maximum when the face is nonempty and bounded, which holds whenever (LP) and (LD) have an interior point (the hypothesis of every theorem), and `sSup` is $0$ otherwise. $\xi$ is written as one minimum over all indices $j$, taking $\max_{\Omega_p}x_j$ when $j\in P^*$ and $\max_{\Omega_d}s_j$ otherwise; since $Z^*$ is the complement of $P^*$ (Theorem 1.14) this is the book's $\min\{\xi_p,\xi_d\}$, with an empty $P^*$ or $Z^*$ contributing nothing; for $n=0$ it is $0$, and every theorem assumes $n\ge1$. Property (5.7) is written coordinatewise, $x_js_j/(x^Ts)>n^{-\eta}$ for all $j$, which is equivalent for $n\ge1$; $n^{-\eta}$ is the real power.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 18–19 ((LP), (LD)), p. 20 (Theorem 1.14, (P*, Z*)), p. 153 (Ω_p, Ω_d, (5.3)), p. 154 (σ^k, (5.7))

import Mathlib

open Matrix

namespace YeIPA.WorstCase

/-!
# Standard-form LP, the strict complementarity partition, the optimal faces and the condition
number `ξ(A, b, c)` of Chapter 5, §5.2

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997: the standard-form pair
(LP) `min cᵀx s.t. Ax = b, x ≥ 0` and (LD) `max bᵀy s.t. Aᵀy + s = c, s ≥ 0` (pp. 18–19);
the strict complementarity partition `(P*, Z*)` (Theorem 1.14, p. 20); the optimal faces
`Ω_p`, `Ω_d` and the numbers `ξ_p`, `ξ_d`, `ξ` of (5.3) (p. 153); the support-type index set
`σᵏ = {j : x_jᵏ ≥ s_jᵏ}` (p. 154); property (5.7) (p. 154).

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's indices
`1, …, n` are `0, …, n-1` here. Vector inequalities are componentwise.
-/

variable {m n : ℕ}

/-- `x` is feasible for (LP): `Ax = b`, `x ≥ 0`. -/
def PrimalFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- `(y, s)` is feasible for (LD): `Aᵀy + s = c`, `s ≥ 0`. -/
def DualFeasible (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 ≤ s j

/-- `(x, y, s)` is an interior (strictly feasible) primal-dual point:
`Ax = b`, `x > 0`, `Aᵀy + s = c`, `s > 0`. -/
def IsInterior (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ (∀ j, 0 < x j) ∧ Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 < s j

/-- `x` is an optimal solution of (LP): feasible, and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def PrimalOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(y, s)` is an optimal solution of (LD): feasible, and `bᵀy' ≤ bᵀy` for every feasible
`(y', s')`. -/
def DualOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  DualFeasible A c y s ∧ ∀ y' s', DualFeasible A c y' s' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- `P*`, the primal part of the strict complementarity partition (Theorem 1.14, p. 20): the
indices `j` with `x_j > 0` for some optimal solution `x` of (LP). -/
def Pstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set (Fin n) :=
  {j | ∃ x, PrimalOptimal A b c x ∧ 0 < x j}

/-- `Z*`, the dual part of the strict complementarity partition (Theorem 1.14, p. 20): the
indices `j` with `s_j > 0` for some optimal solution `(y, s)` of (LD). -/
def Zstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set (Fin n) :=
  {j | ∃ y s, DualOptimal A b c y s ∧ 0 < s j}

/-- The primal optimal face `Ω_p = {x : A_{P*} x_{P*} = b, x_{P*} ≥ 0, x_{Z*} = 0}` (p. 153),
written on the full vector `x ∈ ℝⁿ`. -/
def OmegaP (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | PrimalFeasible A b x ∧ ∀ j ∈ Zstar A b c, x j = 0}

/-- The dual optimal face
`Ω_d = {(y, s) : A_{P*}ᵀ y = c_{P*}, s_{Z*} = c_{Z*} − A_{Z*}ᵀ y ≥ 0}` (p. 153), written with
the full slack vector `s = c − Aᵀy` (so `s_{P*} = 0`). -/
def OmegaD (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | DualFeasible A c p.1 p.2 ∧ ∀ j ∈ Pstar A b c, p.2 j = 0}

/-- `max_{x ∈ Ω_p} x_j` (p. 153), as the supremum of the coordinate over `Ω_p`. -/
noncomputable def maxPrimalCoord (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n) : ℝ :=
  sSup ((fun x : Fin n → ℝ => x j) '' OmegaP A b c)

/-- `max_{(y, s) ∈ Ω_d} s_j` (p. 153), as the supremum of the coordinate over `Ω_d`. -/
noncomputable def maxDualCoord (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n) : ℝ :=
  sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 j) '' OmegaD A b c)

/-- The condition number of (5.3) (p. 153):
`ξ(A, b, c) = min {ξ_p(A, b, c), ξ_d(A, b, c)}` with
`ξ_p = min_{j ∈ P*} max_{x ∈ Ω_p} x_j` and `ξ_d = min_{j ∈ Z*} max_{(y,s) ∈ Ω_d} s_j`.
It is written as one minimum over all indices `j`, taking the primal maximum for `j ∈ P*` and
the dual maximum otherwise (`Z*` is the complement of `P*` by Theorem 1.14); this is the
book's `min {ξ_p, ξ_d}`, with an empty `P*` or `Z*` contributing nothing. -/
noncomputable def xi (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : ℝ :=
  ⨅ j : Fin n, haveI := Classical.propDecidable (j ∈ Pstar A b c)
    if j ∈ Pstar A b c then maxPrimalCoord A b c j else maxDualCoord A b c j

/-- `σ = {j : x_j ≥ s_j}` (p. 154). -/
def sigma (x s : Fin n → ℝ) : Set (Fin n) :=
  {j | s j ≤ x j}

/-- Property (5.7) (p. 154) of a positive pair `(x, s)` with constant `η`:
`min(Xs) / (xᵀs) > n^{-η}`, written coordinatewise as `x_j s_j / (xᵀs) > n^{-η}` for every `j`. -/
def Property57 (η : ℝ) (x s : Fin n → ℝ) : Prop :=
  ∀ j, (n : ℝ) ^ (-η) < x j * s j / (x ⬝ᵥ s)

end YeIPA.WorstCase


