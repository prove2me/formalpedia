-- Prove2me | Definitions.Def_ModLatSVP_lam1
-- name    : ModLatSVP_lam1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:31.620222+00:00
-- url     : https://prove2.me/theorems/4280f5d7-fbac-4ad0-9308-5492bd666922
-- title:
--   Lattices by Gram matrix — minimum $\lambda_1$, dual lattice $L^*$, covering radius $\mu$, determinant
-- statement:
--   A lattice $L=B_L\mathbb Z^m$ is given by its positive definite Gram matrix $G=B_L^{T}B_L$; a lattice vector $B_Lx$ is represented by its integer coefficient vector $x\in\mathbb Z^m$, and a point $B_Lc$ of the span $\mathrm{span}_{\mathbb R}(L)$ by a real coefficient vector $c$. Squared lengths are $\|B_Lc\|^2=c^{T}Gc$. In these coordinates:
--
--   1. the **minimum** is $\lambda_1(L)=\min_{x\in\mathbb Z^m\setminus\{0\}}\sqrt{x^{T}Gx}$;
--   2. the **dual lattice** is $L^*=\{y\in\mathrm{span}_{\mathbb R}(L):\langle x,y\rangle\in\mathbb Z\ \forall x\in L\}$, that is, the coefficient vectors $c$ with $x^{T}Gc\in\mathbb Z$ for every $x\in\mathbb Z^m$, and $\lambda_1(L^*)$ is its minimum;
--   3. the **covering radius** is $\mu(L)=\sup_{t\in\mathrm{span}_{\mathbb R}(L)}\mathrm{dist}(t,L)$, with $\mathrm{dist}(t,L)^2=\min_{x\in\mathbb Z^m}(x-t)^{T}G(x-t)$;
--   4. the **determinant** is $\det(L)=\sqrt{\det G}$, the volume of the fundamental parallelepiped.
--
--   These are the lattice quantities of Minkowski's and Banaszczyk's bounds, of Lemma 2.1 and of the packing bound.
--
--   **Formalization Note** The Gram matrix is real, so every Euclidean lattice is covered (the algorithmic statements use rational Gram matrices). The minima are infima, attained for positive definite $G$; for the zero-dimensional lattice the minimum is $\inf\emptyset=0$, and statements that need $\lambda_1>0$ assume $m\ge1$. The supremum defining $\mu$ is finite for positive definite $G$.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2, p.11 (PDF p.11); §2.1, p.11

import Mathlib

open Matrix

namespace ModLatSVP

/-- The squared length `xᵀ G x` of the coefficient vector `x` in the lattice with Gram matrix `G`.
Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*,
STOC 2027 submission (manuscript sha256 e7151fad…), §2.1, p.11 (PDF p.11): "a lattice is represented by
the positive definite rational Gram matrix G = B_Lᵀ B_L … ∥B_L x∥² = xᵀGx". -/
def qf {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (G *ᵥ x)

/-- An integer coefficient vector, read in `ℝ^ι`. -/
def intVec {ι : Type*} (x : ι → ℤ) : ι → ℝ :=
  fun i => (x i : ℝ)

/-- The minimum `λ₁(L)` of the lattice `L = B_L ℤ^ι` with Gram matrix `G = B_Lᵀ B_L` (§2, p.11:
"λ₁(L) denote[s] the length of a shortest nonzero vector of L"; §2.1: `min_{x ∈ ℤ^m∖{0}} ∥B_L x∥`).

**Formalization Note.** A lattice is given by its Gram matrix (the paper's input model, §2.1), here
with real entries so that every Euclidean lattice is covered. The infimum is attained for positive
definite `G`; for the empty index type it is `sInf ∅ = 0`, and statements that need `λ₁ > 0` assume a
nonempty index type. -/
noncomputable def lam1 {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  sInf {s : ℝ | ∃ x : ι → ℤ, x ≠ 0 ∧ s = Real.sqrt (qf G (intVec x))}

/-- The Euclidean dual `L* = {y ∈ span_ℝ(L) : ⟨x, y⟩ ∈ ℤ for all x ∈ L}` (§2, p.11), in coefficients:
a point `y = B_L c` of the span (`c ∈ ℝ^ι`) lies in `L*` iff `⟨B_L x, B_L c⟩ = xᵀ G c` is an integer for
every `x ∈ ℤ^ι`. Its length is `√(cᵀ G c)`. -/
def dualLat {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : Set (ι → ℝ) :=
  {c | ∀ x : ι → ℤ, ∃ z : ℤ, intVec x ⬝ᵥ (G *ᵥ c) = z}

/-- The minimum `λ₁(L*)` of the dual lattice. -/
noncomputable def lam1Dual {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  sInf {s : ℝ | ∃ c ∈ dualLat G, c ≠ 0 ∧ s = Real.sqrt (qf G c)}

/-- The squared distance `dist(t, L)²` from the point `B_L t` of the span to the lattice. -/
noncomputable def distSq {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (t : ι → ℝ) : ℝ :=
  ⨅ x : ι → ℤ, qf G (intVec x - t)

/-- The covering radius `µ(L) = sup_{t ∈ span_ℝ(L)} dist(t, L)` (§2, p.11).

**Formalization Note.** For positive definite `G` the distances are bounded below by `0` and above
(by half the sum of the basis lengths), so the real infimum and supremum are the true values. -/
noncomputable def covRad {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  ⨆ t : ι → ℝ, Real.sqrt (distSq G t)

/-- The determinant `det(L)` of the lattice: the volume of its fundamental parallelepiped, whose square
is the determinant of the Gram matrix (§2, p.11: "The determinant of the Gram matrix is the square of
this volume"). -/
noncomputable def latDet {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt G.det

end ModLatSVP


