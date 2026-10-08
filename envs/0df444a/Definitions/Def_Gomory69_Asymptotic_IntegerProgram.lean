-- Prove2me | Definitions.Def_Gomory69_Asymptotic_IntegerProgram
-- name    : Gomory69_Asymptotic_IntegerProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:47:10.47089+00:00
-- url     : https://prove2.me/theorems/74bbeb39-92a6-4573-9315-83093eb36173
-- title:
--   The integer program (2), the group M(I)/M(B), relative prices, problem (8), corresponding vertices and the cones K_B(d) (pp. 452–462)
-- statement:
--   This file fixes the integer-programming side of Gomory's asymptotic theory.
--
--   1. **The integer program (2).** $A=(B,N)$ is an integer $m\times(m+n)$ matrix whose first $m$ columns form the $m\times m$ matrix $B$ and whose remaining $n$ columns $N_1,\dots,N_n$ form $N$; $b\in\mathbb Z^m$ and $c\in\mathbb R^{m+n}$, split as $c=(c_B,c_N)$. Problem (2) is
--   $$\max\ c\cdot x\quad\text{subject to}\quad Ax=b,\ x\ge 0,\ x\ \text{integer}.$$
--   A vector $x$ is **feasible** if it satisfies the constraints and **optimal** if it is feasible and $c\cdot y\le c\cdot x$ for every feasible $y$. The standing assumption of p. 452, that $A$ contains an $m\times m$ unit matrix, says that each unit vector $e_k$ of $\mathbb Z^m$ is a column of $A$.
--   2. **Relative prices.** With $B^{-1}$ computed over $\mathbb R$, $c_N^*=-c_N+c_BB^{-1}N$, with components $c^*_{m+i}$. $B$ is an **optimal linear programming basis** when $B^{-1}b\ge 0$ and $c^*_{m+i}\ge 0$ for all $i$.
--   3. **The group.** $M(I)=\mathbb Z^m$, $M(B)$ is the lattice of integer combinations of the columns of $B$, $\mathcal G=M(I)/M(B)$ and $f$ is the quotient map. Write $g_i=fN_i$ and $g_0=fb$; $\mathcal N$ is the set of **nonzero** elements among $fN_1,\dots,fN_n$.
--   4. **Problem (8).** For $g\in\mathcal N$, $c^*(g)=\min_{i:\,fN_i=g}c^*_{m+i}$. A **minimizing vertex** $t^*$ of (8) is an extreme point of $P(\mathcal G,\mathcal N,fb)$ such that $\sum_{g}c^*(g)t^*(g)\le\sum_g c^*(g)t(g)$ for every nonnegative integer solution $t$ of the group equation $\sum_g t(g)\cdot g=fb$.
--   5. **Corresponding vertices** (Remark 1). A nonnegative integer $x_N$ lies over the point $t$ of $T$-space when (i) $t(g)=\sum_{i:\,fN_i=g}x_{m+i}$ for every $g\in\mathcal N$; (ii) whenever $fN_i=fN_j$ with $i\ne j$, $x_{m+i}=0$ or $x_{m+j}=0$; (iii) $x_{m+i}=0$ whenever $fN_i=\bar 0$. It **uses only least cost columns** when $x_{m+i}>0$ only if $c^*_{m+i}=c^*(fN_i)$. The basic part is $x_B=B^{-1}(b-Nx_N)$.
--   6. **The cones.** $K_B=\{y\in\mathbb R^m: B^{-1}y\ge 0\}$, and $K_B(d)$ is the set of $y\in K_B$ whose Euclidean distance to every point of the frontier of $K_B$ is at least $d$. $D=|\det B|$ and $l_{\max}$ is the largest Euclidean length of a nonbasic column $N_i$.
--
--   These objects let THEOREMS 3 and 4 be stated: a minimizing vertex of the corner polyhedron yields an optimal solution of (2) when $b$ lies deep in $K_B$.
--
--   **Formalization Note** The basis is the first $m$ columns (the paper's "without loss of generality"), so variables are indexed by `Fin m ⊕ Fin n`. Remark 1, which the paper calls "easily verified", is used as the definition of a vertex of $P_x(B,N,b)$ over $t$. "$x_{m+i}>0$ only if $c^*_{m+i}=c^*(fN_i)$" is written as: $c^*_{m+i}\le c^*_{m+j}$ for every $j$ with $fN_j=fN_i$ (equivalent, since $fN_i\in\mathcal N$ by (iii)). The optimal LP basis is read as primal feasibility plus nonnegative relative prices, the two facts p. 461 and p. 463 use. Distances are Euclidean, written explicitly as $\sqrt{\sum_k v_k^2}$; the frontier is taken in the usual topology of $\mathbb R^m$, so $K_B(0)=K_B$. $l_{\max}=0$ when $n=0$. The inverse $B^{-1}$ is Lean's matrix inverse, which is $0$ for a singular matrix; every theorem assumes $\det B\ne 0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 452 (problem (2)), pp. 454–458 ((2a), (3)–(5), F, Remark 1), pp. 460–462 ((6)–(8), c*(g), K_B, K_B(d), D, l_max)

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-! Gomory (1969), pp. 452, 454–462: the integer program (2) with `A = (B, N)`, the factor
group `𝒢 = M(I)/M(B)` and the map `f`, the set `𝒩` of nonzero group columns, the relative
prices `c*`, the group costs `c*(g)`, problem (8) and its minimizing vertices, the
corresponding vertices of Remark 1, and the cones `K_B`, `K_B(d)` with `D` and `l_max`.
The basis `B` is taken to be the first `m` columns of `A` (p. 454, "without loss of
generality"), so the variables are indexed by `Fin m ⊕ Fin n`. -/

open Matrix

variable {m n : ℕ}

/-- The constraint matrix `A = (B, N)` of (2), (2a). -/
def fullMatrix (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin m ⊕ Fin n) ℤ :=
  Matrix.fromCols B N

/-- The standing assumption of p. 452: `A` contains an `m × m` unit matrix, i.e. every unit
vector `e_k` of `ℤ^m` is a column of `A`. -/
def ContainsUnitMatrix (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ k : Fin m, ∃ j : Fin m ⊕ Fin n, ∀ i : Fin m, fullMatrix B N i j = if i = k then 1 else 0

/-- Feasibility for the integer program (2): `x` is an integer vector, `x ≥ 0`, `Ax = b`. -/
def IsFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : Fin m ⊕ Fin n → ℤ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ fullMatrix B N *ᵥ x = b

/-- The objective `c · x` of (2). -/
def objective (c : Fin m ⊕ Fin n → ℝ) (x : Fin m ⊕ Fin n → ℤ) : ℝ :=
  ∑ j, c j * (x j : ℝ)

/-- `x` is an optimal solution of (2), `max c · x` s.t. `Ax = b, x ≥ 0, x` integer: it is
feasible and no feasible integer vector has a larger objective value. -/
def IsOptimal (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (x : Fin m ⊕ Fin n → ℤ) : Prop :=
  IsFeasible B N b x ∧ ∀ y, IsFeasible B N b y → objective c y ≤ objective c x

/-- `B` as a real matrix (its inverse is taken over `ℝ`). -/
def realMatrix (B : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℝ :=
  B.map (fun z : ℤ => (z : ℝ))

/-- An integer vector viewed as a real vector. -/
def realVec (v : Fin m → ℤ) : Fin m → ℝ := fun k => (v k : ℝ)

/-- The relative prices `c_N* = − c_N + c_B B⁻¹ N` (pp. 460–461); component `i` is
`c*_{m+i}`. -/
noncomputable def relativePrice (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (i : Fin n) : ℝ :=
  - c (Sum.inr i) +
    ∑ k : Fin m, c (Sum.inl k) * ((realMatrix B)⁻¹ * N.map (fun z : ℤ => (z : ℝ))) k i

/-- `B` is an optimal basis of the linear programming relaxation of (2) (p. 460): it is
primal feasible, `B⁻¹ b ≥ 0`, and all relative prices are nonnegative, `c*_{m+i} ≥ 0`
(p. 461). -/
def IsOptimalLPBasis (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ) : Prop :=
  (∀ k, 0 ≤ ((realMatrix B)⁻¹ *ᵥ realVec b) k) ∧ ∀ i, 0 ≤ relativePrice B N c i

/-- `M(B)` (p. 456): the lattice of all integer combinations of the columns of `B`. -/
def basisLattice (B : Matrix (Fin m) (Fin m) ℤ) : AddSubgroup (Fin m → ℤ) :=
  AddSubgroup.closure (Set.range fun j : Fin m => fun i : Fin m => B i j)

/-- The factor group `𝒢 = M(I)/M(B)`, `M(I) = ℤ^m` (p. 456). -/
abbrev FactorGroup (B : Matrix (Fin m) (Fin m) ℤ) : Type :=
  (Fin m → ℤ) ⧸ basisLattice B

/-- The homomorphism `f : M(I) → 𝒢` (p. 456). -/
def toGroup (B : Matrix (Fin m) (Fin m) ℤ) : (Fin m → ℤ) →+ FactorGroup B :=
  QuotientAddGroup.mk' (basisLattice B)

/-- `g_i = f N_i`, the image of the `i`-th nonbasic column (p. 456). -/
def groupColumn (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (i : Fin n) :
    FactorGroup B :=
  toGroup B (fun k => N k i)

open Classical in
/-- `𝒩` (p. 457): the set of nonzero group elements `f N_i`, `i = 1, …, n`. -/
noncomputable def groupColumnSet (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) :
    Finset (FactorGroup B) :=
  (Finset.univ.image (groupColumn B N)).filter (fun g => g ≠ 0)

open Classical in
/-- The columns `i` with `f N_i = g`. -/
noncomputable def columnsOf (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (g : FactorGroup B) : Finset (Fin n) :=
  Finset.univ.filter (fun i => groupColumn B N i = g)

/-- For `g ∈ 𝒩` some column is mapped onto `g`. -/
theorem columnsOf_nonempty (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (g : ↥(groupColumnSet B N)) : (columnsOf B N (g : FactorGroup B)).Nonempty := by
  classical
  obtain ⟨hmem, -⟩ := Finset.mem_filter.1 g.2
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
  exact ⟨i, by simp [columnsOf, hi]⟩

/-- The group cost `c*(g) = min_{i : f N_i = g} c*_{m+i}`, `g ∈ 𝒩` (p. 461), a minimum over a
nonempty finite set. -/
noncomputable def groupCost (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (g : ↥(groupColumnSet B N)) : ℝ :=
  (columnsOf B N (g : FactorGroup B)).inf' (columnsOf_nonempty B N g) (relativePrice B N c)

/-- `t*` is a vertex of `P(𝒢, 𝒩, g₀)` minimizing (8) (p. 461), with `g₀ = f b`: an extreme
point of `P(𝒢, 𝒩, f b)` with `∑ c*(g) t*(g) ≤ ∑ c*(g) t(g)` for every nonnegative integer
solution `t` of the group equation. -/
def IsMinimizingVertex (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ) (tstar : ↥(groupColumnSet B N) → ℝ) : Prop :=
  tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)) ∧
    ∀ t ∈ groupSolutions (groupColumnSet B N) (toGroup B b),
      ∑ g, groupCost B N c g * tstar g ≤ ∑ g, groupCost B N c g * (t g : ℝ)

/-- Remark 1 (p. 458), used as the definition: the nonnegative integer vector `x_N` is the
nonbasic part of a vertex of `P_x(B, N, b)` over the point `t` of `T`-space when
(i) `F x = t`, i.e. `t(g) = ∑_{i : f N_i = g} x_{m+i}` for `g ∈ 𝒩`;
(ii) whenever `f N_i = f N_j`, `i ≠ j`, one of `x_{m+i}, x_{m+j}` is `0`;
(iii) whenever `f N_i = 0̄`, `x_{m+i} = 0`. -/
def IsVertexLift (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (t : ↥(groupColumnSet B N) → ℝ) (xN : Fin n → ℕ) : Prop :=
  (∀ g : ↥(groupColumnSet B N),
      ((∑ i ∈ columnsOf B N (g : FactorGroup B), xN i : ℕ) : ℝ) = t g) ∧
    (∀ i j, i ≠ j → groupColumn B N i = groupColumn B N j → xN i = 0 ∨ xN j = 0) ∧
    (∀ i, groupColumn B N i = 0 → xN i = 0)

/-- A corresponding vertex using only least cost columns (pp. 461, THEOREM 3): a vertex lift
of `t` with `x_{m+i} > 0` only if `c*_{m+i} = c*(f N_i)`, i.e. only if `c*_{m+i}` is minimal
among the columns `j` with `f N_j = f N_i`. -/
def IsCorrespondingVertex (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (t : ↥(groupColumnSet B N) → ℝ) (xN : Fin n → ℕ) : Prop :=
  IsVertexLift B N t xN ∧
    ∀ i, 0 < xN i → ∀ j, groupColumn B N j = groupColumn B N i →
      relativePrice B N c i ≤ relativePrice B N c j

/-- The basic part `x_B = B⁻¹(b − N x_N)` determined by (2a) (p. 455), as a real vector. -/
noncomputable def basicPart (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (xN : Fin n → ℕ) : Fin m → ℝ :=
  (realMatrix B)⁻¹ *ᵥ (fun k => (b k : ℝ) - ∑ i, (N k i : ℝ) * (xN i : ℝ))

/-- The Euclidean length `‖v‖ = (∑ v_k²)^{1/2}` of a real `m`-vector. -/
noncomputable def euclNorm (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ k, v k ^ 2)

/-- The cone `K_B = {y ∈ ℝ^m : B⁻¹ y ≥ 0}` (p. 462). -/
def basisCone (B : Matrix (Fin m) (Fin m) ℤ) : Set (Fin m → ℝ) :=
  {y | ∀ k, 0 ≤ ((realMatrix B)⁻¹ *ᵥ y) k}

/-- `K_B(d)` (p. 462): the points of `K_B` at Euclidean distance `d` or more from every point
of the frontier of `K_B`. -/
def deepCone (B : Matrix (Fin m) (Fin m) ℤ) (d : ℝ) : Set (Fin m → ℝ) :=
  {y | y ∈ basisCone B ∧ ∀ z ∈ frontier (basisCone B), d ≤ euclNorm (y - z)}

/-- `l_max` (p. 462): the largest Euclidean length of a nonbasic column `N_i` (`0` when
`n = 0`). -/
noncomputable def lmax (N : Matrix (Fin m) (Fin n) ℤ) : ℝ :=
  ⨆ i : Fin n, euclNorm (fun k => (N k i : ℝ))

/-- `D = |det B|` (p. 462). -/
def detAbs (B : Matrix (Fin m) (Fin m) ℤ) : ℕ := B.det.natAbs

end Gomory69.Asymptotic


