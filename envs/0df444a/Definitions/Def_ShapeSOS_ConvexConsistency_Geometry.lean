-- Prove2me | Definitions.Def_ShapeSOS_ConvexConsistency_Geometry
-- name    : ShapeSOS_ConvexConsistency_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:21:29.446618+00:00
-- url     : https://prove2.me/theorems/67e1560e-5573-4c6a-9e14-cfd4809a3ba3
-- title:
--   Real boxes, derivatives, uniform error, and attained minima
-- statement:
--   Let $n$ be a finite dimension. Vectors are real coordinate functions and polynomials are elements of $\mathbb R[x_1,\ldots,x_n]$. A box has real endpoints $l_i<u_i$ and carrier $B=\prod_i[l_i,u_i]$. Its inset is $B_\eta=\prod_i[l_i+\eta,u_i-\eta]$. An interior region is closed, has nonempty interior, lies in $B$, and is disjoint from its boundary. Distances use $\|x\|_2=(\sum_i x_i^2)^{1/2}$.
--
--   The uniform error is $\sup_{x\in S}|f(x)-g(x)|$. Mission uses have nonempty compact $S$ and continuous functions. Coordinate derivatives are derivatives within the specified box. Derivative bounds have ordered extended-real endpoints; only finite endpoints constrain derivatives, exactly as Definition 2 specifies. The optional one-sided predicate says no coordinate has two finite endpoints.
--
--   For any feasible set $F$ and real loss $L$, an attained minimizer $p$ belongs to $F$ and satisfies $L(p)\le L(q)$ for every $q\in F$. For polynomials a fixed classical choice selects such a minimizer whenever one exists, returning zero otherwise. That default entails no optimality. A quadratic function is explicitly $x^TAx+b^Tx+c$, allowing every real quadratic.
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, pp. 3–4, Definitions 1–4; pp. 13–14; pp. 27 and 31, (19) and Theorem B.8

import Mathlib

set_option autoImplicit false
open scoped BigOperators Topology Classical

namespace ShapeSOS.ConvexConsistency
noncomputable section

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ
abbrev PMat (n : ℕ) := Matrix (Fin n) (Fin n) (Poly n)

def value {n : ℕ} (p : Poly n) (x : Vec n) : ℝ := MvPolynomial.eval x p

/-- Euclidean, rather than the default maximum norm on coordinate functions. -/
def norm₂ {n : ℕ} (x : Vec n) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Equation (1): arbitrary real, nondegenerate coordinate intervals. -/
structure Box (n : ℕ) where
  lower : Vec n
  upper : Vec n
  proper : ∀ i, lower i < upper i

def Box.carrier {n : ℕ} (B : Box n) : Set (Vec n) :=
  {x | ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i}

def Box.inner {n : ℕ} (B : Box n) (η : ℝ) : Set (Vec n) :=
  {x | ∀ i, B.lower i + η ≤ x i ∧ x i ≤ B.upper i - η}

def Box.validInset {n : ℕ} (B : Box n) (η : ℝ) : Prop :=
  0 < η ∧ ∀ i, η < (B.upper i - B.lower i) / 2

def InteriorRegion {n : ℕ} (B : Box n) (C : Set (Vec n)) : Prop :=
  IsClosed C ∧ (interior C).Nonempty ∧ C ⊆ B.carrier ∧
    Disjoint C (frontier B.carrier)

def cube (n : ℕ) (a b : ℝ) : Set (Vec n) := {x | ∀ i, a ≤ x i ∧ x i ≤ b}

/-- All uses in the mission are on nonempty compact sets with continuous arguments. -/
def uniformError {n : ℕ} (S : Set (Vec n)) (f g : Vec n → ℝ) : ℝ :=
  sSup ((fun x => |f x - g x|) '' S)

/-- Coordinate derivative taken within the stated domain, including its boundary. -/
def partialWithin {n : ℕ} (S : Set (Vec n)) (f : Vec n → ℝ) (i : Fin n)
    (x : Vec n) : ℝ :=
  fderivWithin ℝ f S x (Pi.single i 1)

/-- Definition 2: infinite endpoints impose no constraint unless finite. -/
structure DerivativeBounds (n : ℕ) where
  lower : Fin n → EReal
  upper : Fin n → EReal
  ordered : ∀ i, lower i ≤ upper i

def DerivativeBounds.oneSided {n : ℕ} (K : DerivativeBounds n) : Prop :=
  ∀ i, ¬ ((∃ a : ℝ, K.lower i = a) ∧ (∃ b : ℝ, K.upper i = b))

def HasBoundedDerivatives {n : ℕ} (B : Box n) (K : DerivativeBounds n)
    (f : Vec n → ℝ) : Prop :=
  ContDiffOn ℝ 1 f B.carrier ∧ ∀ x ∈ B.carrier, ∀ i,
    (∀ a : ℝ, K.lower i = a → a ≤ partialWithin B.carrier f i x) ∧
    (∀ b : ℝ, K.upper i = b → partialWithin B.carrier f i x ≤ b)

/-- Genuine global attained minimum over a specified feasible set. -/
def Minimizes {α : Type*} (F : Set α) (L : α → ℝ) (p : α) : Prop :=
  p ∈ F ∧ ∀ q ∈ F, L p ≤ L q

/-- A fixed deterministic tie choice; zero only when there is no attained minimizer. -/
def selectMin {n : ℕ} (F : Set (Poly n)) (L : Poly n → ℝ) : Poly n :=
  if h : ∃ p, Minimizes F L p then Classical.choose h else 0

/-- General quadratic function, including affine and constant terms. -/
def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (c : ℝ)
    (x : Vec n) : ℝ := (∑ i, ∑ j, x i * A i j * x j) + (∑ i, b i * x i) + c

end
end ShapeSOS.ConvexConsistency


