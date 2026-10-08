-- Prove2me | Definitions.Def_GomoryGroup_Rel_Setting
-- name    : GomoryGroup_Rel_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:13:23.380299+00:00
-- url     : https://prove2.me/theorems/8e6b79c3-00ad-470d-bce1-d28b91f284ec
-- title:
--   pp. 260–262 — P1, P2, the partition A = (B, N), relative costs c*, the cones K^B and K^B(d), l, D, and the group problem (4)
-- statement:
--   This file fixes the objects of R. E. Gomory's 1965 paper on integer and noninteger solutions of linear programs.
--
--   **Data.** There are $m$ rows. The integer $m\times(m+n)$ matrix $A$ has been rearranged as $A=(B,N)$, where the **basis** $B=(\alpha_1,\dots,\alpha_m)$ is an integer $m\times m$ matrix and $N=(\alpha_{m+1},\dots,\alpha_{m+n})$ is the integer $m\times n$ matrix of nonbasic columns. Column $j$ of $N$ ($j=0,\dots,n-1$) is the paper's $\alpha_{m+1+j}$. The cost vector $c=(c_B,c_N)$ is real, and the right-hand side $b$ is an integer $m$-vector.
--
--   1. **Unit columns.** $A$ has the form $(A',I)$: after the rearrangement, every unit vector $e_i$ of $\mathbb Z^m$ is a column of $B$ or of $N$.
--   2. **P1** (1): maximize $c_Bx_B+c_Nx_N$ subject to $Bx_B+Nx_N=\beta$, $x_B\ge0$, $x_N\ge0$, $x$ real. The set of objective values of its feasible points is recorded.
--   3. **P2**: the same problem with $x$ integer and nonnegative, i.e. $x_B\in\mathbb N^m$, $x_N\in\mathbb N^n$, $Bx_B+Nx_N=b$. A point is **optimal** for P2 if it is feasible and no feasible point has a larger cost.
--   4. **Relative costs.** For a nonsingular $B$,
--   $$c^*_{m+1+j}=c_{m+1+j}-c_BB^{-1}\alpha_{m+1+j}.$$
--   5. **The group problem (4).** Let $M(I)=\mathbb Z^m$ and let $M(B)=\mathfrak L_B=B\mathbb Z^m$ be the lattice of integer combinations of $\alpha_1,\dots,\alpha_m$. A vector $y\in\mathbb N^n$ is feasible for (4) with right-hand side $b$ when
--   $$\sum_{i=1}^{n}\bar\alpha_{i+m}y_i=\bar b\ \text{ in } M(I)/M(B),\qquad\text{equivalently}\qquad b-Ny\in\mathfrak L_B,$$
--   and its objective is $\sum_{i=1}^n c^*_{i+m}y_i$. Optimal solutions and the set of objective values of (4) are defined as for P2.
--   6. **Cones.** $K^B=\{\beta\in\mathbb R^m: B^{-1}\beta\ge0\}$, and the **reduced cone** $K^B(d)$ is the set of $\beta$ whose closed Euclidean ball of radius $d$ lies in $K^B$.
--   7. **Constants.** $l=\max_{i=m+1,\dots,m+n}\|\alpha_i\|$ (Euclidean norm) and $D=|\det B|$.
--
--   These are the objects in which THEOREMS 1, 2 and 4 and the LEMMA are stated.
--
--   **Formalization Note** The group $M(I)/M(B)$ is not built explicitly: feasibility of (4) is written as $b-Ny=Bk$ for some $k\in\mathbb Z^m$, which is the same as $\sum\bar\alpha_{i+m}y_i=\bar b$ because the map $f$ of the paper is the quotient map. $B^{-1}$ is the inverse of the real cast of $B$ (Lean's matrix inverse returns $0$ for a singular matrix, so every theorem using it assumes $\det B\neq0$). The norm is the Euclidean norm $\sqrt{\sum_i v_i^2}$, not Lean's default sup norm. $l$ is a supremum over the finite set of nonbasic columns and equals $0$ when $n=0$. $K^B(d)$ uses closed balls: "removing all points within a distance $d$ of its boundary" is read as keeping the points at distance at least $d$. Optimal values are never defined as suprema; theorems speak of the greatest element of the set of values.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), pp. 260–262, (1), THEOREM 1 and (4)

import Mathlib

namespace GomoryGroup.Rel

open Matrix

variable {m n : ℕ}

/-- The basis `B` (the columns `α₁, …, α_m` of `A`), cast to a real matrix. -/
def Br (B : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℝ :=
  B.map (fun z : ℤ => (z : ℝ))

/-- The nonbasic part `N` (the columns `α_{m+1}, …, α_{m+n}` of `A`), cast to a real matrix.
Column `j : Fin n` of `N` is the paper's `α_{m+1+j}`. -/
def Nr (N : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℝ :=
  N.map (fun z : ℤ => (z : ℝ))

/-- The Euclidean norm `‖v‖ = (∑ i, v i ^ 2)^{1/2}` of a real `m`-vector. -/
noncomputable def euclNorm (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- `A = (A′, I)`: after the rearrangement `A = (B, N)`, every unit vector `e_i` of `ℤ^m`
is a column of `B` or a column of `N`. -/
def HasUnitColumns (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i : Fin m,
    (∃ j : Fin m, ∀ r : Fin m, B r j = if r = i then 1 else 0) ∨
    (∃ j : Fin n, ∀ r : Fin m, N r j = if r = i then 1 else 0)

/-- Feasibility for P1 (1) with right-hand side `β`: `B x_B + N x_N = β`, `x_B ≥ 0`, `x_N ≥ 0`,
with real `x`. -/
def IsLPFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (β : Fin m → ℝ) (xB : Fin m → ℝ) (xN : Fin n → ℝ) : Prop :=
  Br B *ᵥ xB + Nr N *ᵥ xN = β ∧ 0 ≤ xB ∧ 0 ≤ xN

/-- The set of costs `c_B x_B + c_N x_N` of the feasible points of P1 with right-hand side `β`. -/
def lpValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (β : Fin m → ℝ) : Set ℝ :=
  {z | ∃ (xB : Fin m → ℝ) (xN : Fin n → ℝ), IsLPFeasible B N β xB xN ∧ z = cB ⬝ᵥ xB + cN ⬝ᵥ xN}

/-- Feasibility for P2: `x` integer and nonnegative (`ℕ`-valued) with `B x_B + N x_N = b`. -/
def IsIPFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : Prop :=
  B *ᵥ (fun i => (xB i : ℤ)) + N *ᵥ (fun j => (xN j : ℤ)) = b

/-- The cost `c_B x_B + c_N x_N` of an integer point. -/
def ipCost (cB : Fin m → ℝ) (cN : Fin n → ℝ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : ℝ :=
  cB ⬝ᵥ (fun i => (xB i : ℝ)) + cN ⬝ᵥ (fun j => (xN j : ℝ))

/-- The set of costs of the feasible points of P2 with right-hand side `b`. -/
def ipValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) : Set ℝ :=
  {z | ∃ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN ∧ z = ipCost cB cN xB xN}

/-- `(x_B, x_N)` is an optimal solution of P2: feasible, and no feasible point costs more. -/
def IsIPOptimal (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : Prop :=
  IsIPFeasible B N b xB xN ∧
    ∀ (xB' : Fin m → ℕ) (xN' : Fin n → ℕ), IsIPFeasible B N b xB' xN' →
      ipCost cB cN xB' xN' ≤ ipCost cB cN xB xN

/-- The relative cost `c*_{m+1+j} = c_{m+1+j} − c_B B⁻¹ α_{m+1+j}` of the nonbasic column `j`. -/
noncomputable def reducedCost (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) : Fin n → ℝ :=
  fun j => cN j - cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun r => (N r j : ℝ)))

/-- Feasibility for the group problem (4): `y ∈ ℕ^n` with `Σ ᾱ_{i+m} y_i = b̄` in `M(I)/M(B)`,
i.e. `b − N y` lies in the lattice `𝔏_B = M(B) = B ℤ^m`. -/
def IsGroupFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (y : Fin n → ℕ) : Prop :=
  ∃ k : Fin m → ℤ, b - N *ᵥ (fun j => (y j : ℤ)) = B *ᵥ k

/-- The objective `Σ_j c*_{m+1+j} y_j` of the group problem (4). -/
noncomputable def groupObj (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (y : Fin n → ℕ) : ℝ :=
  ∑ j, reducedCost B N cB cN j * (y j : ℝ)

/-- The set of objective values of the feasible points of the group problem (4) for `b`. -/
noncomputable def groupValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) : Set ℝ :=
  {z | ∃ y : Fin n → ℕ, IsGroupFeasible B N b y ∧ z = groupObj B N cB cN y}

/-- `y` is an optimal solution of the group problem (4) for `b`. -/
def IsGroupOptimal (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (y : Fin n → ℕ) : Prop :=
  IsGroupFeasible B N b y ∧
    ∀ y' : Fin n → ℕ, IsGroupFeasible B N b y' → groupObj B N cB cN y' ≤ groupObj B N cB cN y

/-- The cone `K^B = {β ∈ ℝ^m : B⁻¹ β ≥ 0}` of right-hand sides for which `B` is a feasible basis. -/
noncomputable def basisCone (B : Matrix (Fin m) (Fin m) ℤ) : Set (Fin m → ℝ) :=
  {β | 0 ≤ (Br B)⁻¹ *ᵥ β}

/-- The reduced cone `K^B(d)`: the points `β` whose closed Euclidean ball of radius `d`
lies inside `K^B`. -/
noncomputable def reducedCone (B : Matrix (Fin m) (Fin m) ℤ) (d : ℝ) : Set (Fin m → ℝ) :=
  {β | ∀ v : Fin m → ℝ, euclNorm (v - β) ≤ d → v ∈ basisCone B}

/-- `l = max_j ‖α_{m+1+j}‖`, the largest Euclidean length of a nonbasic column
(`0` when `n = 0`). -/
noncomputable def ell (N : Matrix (Fin m) (Fin n) ℤ) : ℝ :=
  ⨆ j : Fin n, euclNorm (fun r => (N r j : ℝ))

/-- `D = |det B|`. -/
def detD (B : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  B.det.natAbs

end GomoryGroup.Rel


