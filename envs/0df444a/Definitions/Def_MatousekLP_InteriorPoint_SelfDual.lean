-- Prove2me | Definitions.Def_MatousekLP_InteriorPoint_SelfDual
-- name    : MatousekLP_InteriorPoint_SelfDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:29:14.937373+00:00
-- url     : https://prove2.me/theorems/68c05083-f97e-4d6d-8d65-fb183fb4b7ac
-- title:
--   §7.2 — the LP (7.7), the Goldman–Tucker system (GTS) and the self-dual program (SD)
-- statement:
--   This module fixes the objects of the initialization part of §7.2 of Matoušek & Gärtner. Let $A$ be a real $m\times n$ matrix, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$.
--
--   1. The **linear program (7.7)** is: maximize $c^{T}x$ subject to $Ax\le b$, $x\ge 0$. An **optimal solution** is a feasible $x$ with $c^{T}x'\le c^{T}x$ for every feasible $x'$; (7.7) is **unbounded** if for every real $M$ some feasible $x$ has $c^{T}x>M$. Its **dual** is: minimize $b^{T}y$ subject to $A^{T}y\ge c$, $y\ge 0$, with optimal solutions defined analogously.
--   2. The **Goldman–Tucker system** (GTS) in the unknowns $x\in\mathbb{R}^n$, $y\in\mathbb{R}^m$, $\tau\in\mathbb{R}$ is
--   $$Ax-\tau b\le 0,\qquad -A^{T}y+\tau c\le 0,\qquad b^{T}y-c^{T}x\le 0,\qquad x,y\ge 0,\ \tau\ge 0,$$
--   and $\rho=\rho(x,y)=c^{T}x-b^{T}y$ is the slack in its last inequality.
--   3. With $u=(y,x,\tau)\in\mathbb{R}^k$, $k=n+m+1$, the skew-symmetric block matrix
--   $$M_0=\begin{pmatrix}0 & A & -b\\ -A^{T} & 0 & c\\ b^{T} & -c^{T} & 0\end{pmatrix}$$
--   writes (GTS) as $M_0u\le 0$, $u\ge 0$. Put $r=\mathbf 1+M_0\mathbf 1\in\mathbb{R}^k$,
--   $$M=\begin{pmatrix}M_0 & -r\\ r^{T} & 0\end{pmatrix}\in\mathbb{R}^{(k+1)\times(k+1)},\qquad q=(0,\dots,0,k+1)\in\mathbb{R}^{k+1}.$$
--   4. The **self-dual program** (SD), in the variable $v=(u,\vartheta)\in\mathbb{R}^{k+1}$, is: maximize $-q^{T}v$ subject to $Mv\le q$, $v\ge 0$. For $v$ feasible the **slacks** are $z=z(v)=q-Mv$, and a feasible $v$ is **strictly complementary** if for every $j=1,\dots,k+1$ we have $v_j>0$ or $z_j>0$.
--
--   (SD) is the auxiliary program of the self-dual embedding: it always has an explicit interior point on its central path, and its strictly complementary optimal solutions solve or certify infeasibility/unboundedness of (7.7).
--
--   **Formalization Note** $u$ is indexed by `Fin m ⊕ Fin n ⊕ Unit` (the $m$ coordinates of $y$, then the $n$ coordinates of $x$, then $\tau$) and $v$ by `(Fin m ⊕ Fin n ⊕ Unit) ⊕ Unit` (the last coordinate is $\vartheta$); the projections `uY`, `uX`, `uTau`, `vU`, `vTheta` extract the parts. Optimality and boundedness are stated against every feasible point; no supremum is used. The last entry of $q$ is $k+1=n+m+2$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 126 (eq. (7.7), system (GTS), ρ), p. 127 (M_0, u, k, r, M), p. 128 (q, (SD), slacks z, strict complementarity); dual of (7.7) as in §6.1, p. 82

import Mathlib

namespace MatousekLP.InteriorPoint

/-!
# The Goldman–Tucker system and the self-dual embedding

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007, §7.2,
pp. 126–128: the linear program (7.7) `maximize cᵀx subject to Ax ≤ b, x ≥ 0`, its dual
`minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0` (§6.1), the Goldman–Tucker system (GTS) with the slack
`ρ(x, y) = cᵀx − bᵀy`, the skew-symmetric matrix `M₀`, the vector `r = 𝟏 + M₀𝟏`, the matrix `M`,
the vector `q = (0, …, 0, k+1)` with `k = n + m + 1`, the linear program
(SD) `maximize −qᵀv subject to Mv ≤ q, v ≥ 0`, its slacks `z(v) = q − Mv`, and strictly
complementary feasible solutions.

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's vector
`u = (y, x, τ) ∈ ℝᵏ` is indexed by `Fin m ⊕ Fin n ⊕ Unit` (first the `m` coordinates of `y`,
then the `n` coordinates of `x`, then `τ`), and `v = (u, ϑ) ∈ ℝ^{k+1}` by
`(Fin m ⊕ Fin n ⊕ Unit) ⊕ Unit` (the last coordinate is `ϑ`).
-/

open Matrix

variable {m n : ℕ}

/-- `x` is a feasible solution of (7.7): `Ax ≤ b` and `x ≥ 0` (p. 126). -/
def IsIneqFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x ≤ b ∧ 0 ≤ x

/-- `x` is an optimal solution of (7.7): feasible, and `cᵀx' ≤ cᵀx` for every feasible `x'`. -/
def IsIneqOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsIneqFeasible A b x ∧ ∀ x', IsIneqFeasible A b x' → c ⬝ᵥ x' ≤ c ⬝ᵥ x

/-- (7.7) is unbounded: for every real `M` some feasible `x` has `cᵀx > M`. -/
def IsIneqUnbounded (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x, IsIneqFeasible A b x ∧ M < c ⬝ᵥ x

/-- `y` is a feasible solution of the dual of (7.7): `Aᵀy ≥ c` and `y ≥ 0` (§6.1, p. 82). -/
def IsIneqDualFeasible (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  c ≤ Aᵀ *ᵥ y ∧ 0 ≤ y

/-- `y` is an optimal solution of the dual of (7.7), `minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0`:
dual feasible, and `bᵀy ≤ bᵀy'` for every dual feasible `y'`. -/
def IsIneqDualOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  IsIneqDualFeasible A c y ∧ ∀ y', IsIneqDualFeasible A c y' → b ⬝ᵥ y ≤ b ⬝ᵥ y'

/-- `(x, y, τ)` is a solution of the Goldman–Tucker system (GTS) (p. 126):
`Ax − τb ≤ 0`, `−Aᵀy + τc ≤ 0`, `bᵀy − cᵀx ≤ 0`, `x, y ≥ 0`, `τ ≥ 0`. -/
def IsGTSSolution (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ) : Prop :=
  A *ᵥ x - τ • b ≤ 0 ∧ -(Aᵀ *ᵥ y) + τ • c ≤ 0 ∧ b ⬝ᵥ y - c ⬝ᵥ x ≤ 0 ∧
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ τ

/-- The slack in the last inequality of (GTS), `ρ(x, y) = cᵀx − bᵀy` (p. 126). -/
def gtsSlack (b : Fin m → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x - b ⬝ᵥ y

/-- Index type of `u = (y, x, τ) ∈ ℝᵏ`, `k = n + m + 1`. -/
abbrev UIdx (m n : ℕ) := Fin m ⊕ Fin n ⊕ Unit

/-- Index type of `v = (u, ϑ) ∈ ℝ^{k+1}`. -/
abbrev VIdx (m n : ℕ) := UIdx m n ⊕ Unit

/-- The `y`-part of `u = (y, x, τ)`. -/
def uY (u : UIdx m n → ℝ) : Fin m → ℝ := fun i => u (Sum.inl i)

/-- The `x`-part of `u = (y, x, τ)`. -/
def uX (u : UIdx m n → ℝ) : Fin n → ℝ := fun j => u (Sum.inr (Sum.inl j))

/-- The `τ`-coordinate of `u = (y, x, τ)`. -/
def uTau (u : UIdx m n → ℝ) : ℝ := u (Sum.inr (Sum.inr ()))

/-- The `u`-part of `v = (u, ϑ)`. -/
def vU (v : VIdx m n → ℝ) : UIdx m n → ℝ := fun i => v (Sum.inl i)

/-- The last coordinate `ϑ` of `v = (u, ϑ)`. -/
def vTheta (v : VIdx m n → ℝ) : ℝ := v (Sum.inr ())

/-- The `k × k` block matrix (p. 127)
```
M₀ = (  0    A   −b )
     ( −Aᵀ   0    c )
     (  bᵀ  −cᵀ   0 )
```
acting on `u = (y, x, τ)`, so that (GTS) reads `M₀u ≤ 0`, `u ≥ 0`. -/
def M0 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Matrix (UIdx m n) (UIdx m n) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl i, Sum.inr (Sum.inl j) => A i j
    | Sum.inl i, Sum.inr (Sum.inr _) => -b i
    | Sum.inr (Sum.inl j), Sum.inl i => -A i j
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inl j), Sum.inr (Sum.inr _) => c j
    | Sum.inr (Sum.inr _), Sum.inl i => b i
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inl j) => -c j
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 0

/-- The vector `r = 𝟏 + M₀𝟏 ∈ ℝᵏ` (p. 127). -/
def rVec (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : UIdx m n → ℝ :=
  (fun _ => 1) + M0 A b c *ᵥ (fun _ => 1)

/-- The `(k+1) × (k+1)` matrix (p. 127)
```
M = ( M₀  −r )
    ( rᵀ   0 )
``` -/
def Mmat (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Matrix (VIdx m n) (VIdx m n) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => M0 A b c i j
    | Sum.inl i, Sum.inr _ => -rVec A b c i
    | Sum.inr _, Sum.inl j => rVec A b c j
    | Sum.inr _, Sum.inr _ => 0

/-- The vector `q = (0, 0, …, 0, k+1) ∈ ℝ^{k+1}` with `k = n + m + 1` (p. 128). -/
def qVec (m n : ℕ) : VIdx m n → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => ((n + m + 1 : ℕ) : ℝ) + 1

/-- `v` is a feasible solution of (SD) `maximize −qᵀv subject to Mv ≤ q, v ≥ 0` (p. 128). -/
def IsSDFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (v : VIdx m n → ℝ) : Prop :=
  Mmat A b c *ᵥ v ≤ qVec m n ∧ 0 ≤ v

/-- `v` is an optimal solution of (SD): feasible, and `−qᵀv' ≤ −qᵀv` for every feasible `v'`. -/
def IsSDOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (v : VIdx m n → ℝ) : Prop :=
  IsSDFeasible A b c v ∧ ∀ v', IsSDFeasible A b c v' → -(qVec m n ⬝ᵥ v') ≤ -(qVec m n ⬝ᵥ v)

/-- The objective `−qᵀv` of (SD) is bounded from above on its feasible set. -/
def IsSDBoundedAbove (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ B : ℝ, ∀ v, IsSDFeasible A b c v → -(qVec m n ⬝ᵥ v) ≤ B

/-- The slacks `z = z(v) = q − Mv` of (SD) (p. 128). -/
def sdSlack (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (v : VIdx m n → ℝ) : VIdx m n → ℝ :=
  qVec m n - Mmat A b c *ᵥ v

/-- A feasible solution `v` of (SD) is strictly complementary if for every coordinate `j` we
have `vⱼ > 0` or `zⱼ > 0` (p. 128). -/
def IsStrictlyComplementary (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (v : VIdx m n → ℝ) : Prop :=
  IsSDFeasible A b c v ∧ ∀ j, 0 < v j ∨ 0 < sdSlack A b c v j

end MatousekLP.InteriorPoint


