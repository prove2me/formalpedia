-- Prove2me | Definitions.Def_ProxFlatIP_Polyhedra
-- name    : ProxFlatIP_Polyhedra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:26.547609+00:00
-- url     : https://prove2.me/theorems/7d35f033-5a17-45e4-b27e-027b7aab0727
-- title:
--   $P(A,b)$, LP and IP optimality, full column rank, slices $P_I(A,b)$, and dimension
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$ and $c\in\mathbb Q^n$. This definition fixes the objects of the paper's linear and integer programs.
--
--   1. The **polyhedron** is $P(A,b):=\{x\in\mathbb R^n: Ax\le b\}$, with the inequality read componentwise.
--   2. A point $x$ is **integral** if $x\in\mathbb Z^n$.
--   3. $A$ has **full column rank** if $x\mapsto Ax$ is injective on $\mathbb R^n$.
--   4. A point $x$ is an **optimal vertex** of $\mathrm{LP}(A,b,c):=\max\{c^\top x: x\in P(A,b)\}$ if it is a vertex of $P(A,b)$ that maximizes $c^\top x$ over $P(A,b)$.
--   5. $\mathrm{IP}(A,b,c):=\max\{c^\top x: x\in P(A,b)\cap\mathbb Z^n\}$ is **feasible** if $P(A,b)\cap\mathbb Z^n\neq\emptyset$, and $z$ is an **optimal solution** if it lies in $P(A,b)\cap\mathbb Z^n$ and maximizes $c^\top x$ there.
--   6. For $I\subseteq[m]$, $\ker A_I$ is the set of $x$ annihilated by the rows indexed by $I$, with $\ker A_\emptyset=\mathbb R^n$, and $\operatorname{rank}A_I$ is the rank of those rows.
--   7. An index set $I$ is **admissible** if $|I|\le n-1$ and $\operatorname{rank}A_I=|I|$. For such $I$ the **slice** is $P_I(A,b):=P(A,b)\cap\ker A_I$, so that $P_\emptyset(A,b)=P(A,b)$.
--   8. The **dimension** of $Q\subseteq\mathbb R^n$ is the dimension of the linear span of $Q$.
--
--   These are the objects in which the goal theorem and all its milestones are stated. Slices through the origin are how the paper passes from low-dimensional bounds to high-dimensional ones.
--
--   **Formalization Note** Points are `Fin n → ℝ`, and the integral and rational data are cast to `ℝ`. Vertices use the published `LinearOptimization.IsVertex`: a point of the set that is the unique minimizer of some linear cost. The condition $|I|\le n-1$ is written $|I|+1\le n$, so that no index set is admissible when $n=0$.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, §1, p.1 (P(A,b), LP, IP, full column rank); §2, pp.4–5 (rows, dim, P_I, ker A_∅)

import Mathlib
import Definitions.Def_Vertex

open Matrix

namespace ProxFlatIP

/-! # Polyhedra, LP and IP optimality, and slices through the origin

Celaya–Kuhlmann–Paat–Weismantel, *Proximity and flatness bounds for linear integer optimization*,
arXiv:2211.14941v1 (preprint): §1, p.1 and §2, pp.4–5.

**Formalization Note.** Points are `Fin n → ℝ`. The data `A`, `b`, `α` are integral and `c` is
rational; all of them are cast to `ℝ`. Rows are indexed by `Fin m`, and an index set `I ⊆ [m]` is a
`Finset (Fin m)`. "Vertex" is the published `LinearOptimization.IsVertex`. -/

variable {m n : ℕ}

/-- The integral matrix `A`, read over `ℝ`. -/
def realMat (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

/-- An integral vector, read over `ℝ`. -/
def castVec {k : ℕ} (v : Fin k → ℤ) : Fin k → ℝ := fun i => (v i : ℝ)

/-- A rational vector, read over `ℝ`. -/
def ratVec {k : ℕ} (v : Fin k → ℚ) : Fin k → ℝ := fun i => (v i : ℝ)

/-- `P(A,b) := {x ∈ ℝⁿ : Ax ≤ b}` (arXiv:2211.14941v1, §1, p.1). The inequality is componentwise. -/
def Poly (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Set (Fin n → ℝ) :=
  {x | ∀ i, (realMat A *ᵥ x) i ≤ (b i : ℝ)}

/-- `x ∈ ℤⁿ`. -/
def IsIntegralPt (x : Fin n → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = k

/-- `A` has full column rank (p.1): `x ↦ Ax` is injective on `ℝⁿ`, which is `rank A = n`. -/
def FullColRank (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  Function.Injective (realMat A).mulVec

/-- `x` is an optimal vertex of `LP(A,b,c) := max{c⊤x : x ∈ P(A,b)}` (p.1). -/
def IsLPOptimalVertex (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℚ)
    (x : Fin n → ℝ) : Prop :=
  LinearOptimization.IsVertex (Poly A b) x ∧ ∀ y ∈ Poly A b, ratVec c ⬝ᵥ y ≤ ratVec c ⬝ᵥ x

/-- `IP(A,b,c)` is feasible: `P(A,b) ∩ ℤⁿ ≠ ∅` (p.2; standing in §2, p.4). -/
def IsIPFeasible (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Prop :=
  ∃ z ∈ Poly A b, IsIntegralPt z

/-- `z` is an optimal solution of `IP(A,b,c) := max{c⊤x : x ∈ P(A,b) ∩ ℤⁿ}` (p.1). -/
def IsIPOptimal (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℚ)
    (z : Fin n → ℝ) : Prop :=
  IsIntegralPt z ∧ z ∈ Poly A b ∧
    ∀ w ∈ Poly A b, IsIntegralPt w → ratVec c ⬝ᵥ w ≤ ratVec c ⬝ᵥ z

/-- `ker A_I`, the set of `x` annihilated by the rows indexed by `I` (p.4). `ker A_∅ = ℝⁿ` (p.5). -/
def kerRows (A : Matrix (Fin m) (Fin n) ℤ) (I : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x | ∀ i ∈ I, (realMat A *ᵥ x) i = 0}

/-- `rank A_I`, the rank over `ℝ` of the submatrix of rows indexed by `I` (p.4). -/
noncomputable def rowRank (A : Matrix (Fin m) (Fin n) ℤ) (I : Finset (Fin m)) : ℕ :=
  ((realMat A).submatrix (Subtype.val : {i // i ∈ I} → Fin m) id).rank

/-- The index sets for which the paper defines the slice `P_I`: `|I| ≤ n − 1` and
`rank A_I = |I|` (p.4).

**Formalization Note.** `|I| ≤ n − 1` is written `|I| + 1 ≤ n`, so that no index set is admissible
when `n = 0` (truncated subtraction would admit `I = ∅`). -/
def Admissible (A : Matrix (Fin m) (Fin n) ℤ) (I : Finset (Fin m)) : Prop :=
  I.card + 1 ≤ n ∧ rowRank A I = I.card

/-- `P_I(A,b) := P(A,b) ∩ ker A_I` (p.4); `P_∅(A,b) = P(A,b)` (p.5). The paper uses it for
admissible `I`; see `Admissible`. -/
def PI (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (I : Finset (Fin m)) : Set (Fin n → ℝ) :=
  Poly A b ∩ kerRows A I

/-- `dim Q`: the dimension of the **linear** span of `Q` (p.4). -/
noncomputable def dimLin (Q : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ Q)

end ProxFlatIP


