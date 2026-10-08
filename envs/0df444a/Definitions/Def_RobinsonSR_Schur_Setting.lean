-- Prove2me | Definitions.Def_RobinsonSR_Schur_Setting
-- name    : RobinsonSR_Schur_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:51.158467+00:00
-- url     : https://prove2.me/theorems/cfcc667b-389a-438b-8948-29fc92b8a055
-- title:
--   Normal cone, Schur complement, P-matrix, and Lipschitz inverse for Theorem 3.1
-- statement:
--   Let $E=\mathbb R^I$ have its Euclidean inner product. For $C\subseteq E$, the normal cone $N_C(x)$ consists of vectors $v$ satisfying $x\in C$ and $\langle v,c-x\rangle\leq 0$ for every $c\in C$; it is empty when $x\notin C$.
--
--   For a block matrix $A$ with nonsingular upper-left block $A_{11}$, its **Schur complement** is
--
--   $$
--   A/A_{11}=A_{22}-A_{21}A_{11}^{-1}A_{12}.
--   $$
--
--   A matrix is **positive definite** here when $w^\top Mw>0$ for every nonzero $w$, without a symmetry requirement. It is a **P-matrix** when every nonempty principal minor is positive. The definitions also give the upper and lower blocks of a vector in $\mathbb R^{r+s}$, the set $\mathbb R^r\times K$, the nonnegative orthant, and polyhedral sets as finite intersections of closed half-spaces.
--
--   Finally, $\operatorname{InvIsLipschitzFunction}(A,D)$ means the inverse of $w\mapsto Aw+N_D(w)$ has exactly one value at every $y\in E$ and obeys one global Lipschitz bound. These definitions fix the common model for the theorem and its milestones.
--
--   **Formalization Note** The matrix inverse in the Schur complement is used in results only under $\det A_{11}\ne0$; the normal cone includes the domain condition $x\in C$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), pp. 43, 50–52, (1.1), Schur-complement definition p. 51, Theorem 3.1 and (3.8)

import Mathlib

namespace RobinsonSR.Schur

open scoped RealInnerProductSpace Matrix

/-- The normal cone of a convex set is empty outside the set. -/
def normalCone {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) : Set (EuclideanSpace ℝ ι) :=
  {y | x ∈ C ∧ (∀ c ∈ C, inner ℝ y (c - x) ≤ 0)}

/-- Positive definiteness without a symmetry requirement. -/
def PosDefNS {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (M *ᵥ w)

/-- Every nonempty principal minor is strictly positive. -/
def IsPMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∀ J : Finset ι, J.Nonempty →
    0 < (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).det

/-- Robinson's Schur complement, used when `A₁₁` is nonsingular. -/
noncomputable def schur {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂

/-- The first block of a vector in `ℝʳ⁺ˢ`. -/
def upperBlock {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun i => w (Sum.inl i))

/-- The second block of a vector in `ℝʳ⁺ˢ`. -/
def lowerBlock {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 (fun j => w (Sum.inr j))

/-- The Cartesian product `ℝʳ × K` in Euclidean sum coordinates. -/
def prodSet {r s : ℕ} (K : Set (EuclideanSpace ℝ (Fin s))) :
    Set (EuclideanSpace ℝ (Fin r ⊕ Fin s)) :=
  {w | lowerBlock w ∈ K}

/-- The nonnegative orthant `ℝˢ₊`. -/
def nonnegOrthant (s : ℕ) : Set (EuclideanSpace ℝ (Fin s)) :=
  {w | ∀ j, 0 ≤ w j}

/-- A finite intersection of closed half-spaces. -/
def IsPolyhedral {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ ι) (b : Fin m → ℝ),
    C = {x | ∀ i, inner ℝ (a i) x ≤ b i}

/-- The inverse of `w ↦ Aw + normalCone D w` is an everywhere-defined,
single-valued, globally Lipschitz function. -/
def InvIsLipschitzFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (D : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∃ L : ℝ, ∃ σ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
    (∀ y, y - A.toEuclideanLin (σ y) ∈ normalCone D (σ y) ∧
      ∀ w, y - A.toEuclideanLin w ∈ normalCone D w → w = σ y) ∧
    ∀ y₁ y₂, ‖σ y₁ - σ y₂‖ ≤ L * ‖y₁ - y₂‖

end RobinsonSR.Schur


