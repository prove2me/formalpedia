-- Prove2me | Definitions.Def_CrouzeixHilbert
-- name    : CrouzeixHilbert
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.516996+00:00
-- url     : https://prove2.me/theorems/3d436070-1270-4356-b33d-99b100d7424c
-- statement:
--   For a bounded complex-linear operator A on a complex inner-product space H, W(A) consists of ⟨x,Ax⟩ for unit vectors x, and K(A) is its closure. The supremum norm of F on S is the real supremum of {0} together with {‖F(z)‖ : z∈S}; matrix norms are Euclidean operator norms. Amplification uses the completion of H⊗ℂ ℂᵐ, with A⊗B extended continuously. For matrix coefficients B₀,…,B_d, P(z)=ΣₖzᵏBₖ and P(A)=ΣₖAᵏ⊗Bₖ. A smooth contour is a continuously differentiable path γ:ℝ→ℂ with γ(0)=γ(1); its index is (2πi)⁻¹∫₀¹γ′(t)/(γ(t)−z)dt. A calculus contour for K⊆U is required to stay in U∖K on [0,1], have index one on K, and index zero outside U. Scalar contour evaluation is (2πi)⁻¹∫₀¹γ′(t)f(γ(t))(γ(t)I−A)⁻¹dt, using the ring inverse; holomorphic evaluation selects one calculus contour for K(A),U when one exists and is zero otherwise. Matrix holomorphic evaluation combines these entrywise operators with matrix units. Entrywise holomorphic means each entry is complex differentiable on U. A rational matrix has poles outside K when every entry's denominator is nonzero on K; scalar evaluation substitutes A into numerator and denominator and multiplies by the denominator's ring inverse, and matrix evaluation again uses matrix units. NonzeroConclusion(A) is the defined proposition that K(A) is compact, real-convex, and contains the spectrum, together with the following assertions for every positive matrix size m: all matrix polynomials satisfy ‖P(A)‖≤2 sup_W(A)‖P‖, the suprema on W(A) and K(A) agree, and the latter is attained; every entrywise holomorphic F on an open U containing K(A) admits a calculus contour, all such contours give the selected scalar evaluations entrywise, and ‖F(A)‖≤2 sup_K(A)‖F‖ with attained supremum; and every rational matrix with poles outside K(A) has invertible evaluated denominators, satisfies the same factor-two bound with attained supremum, and agrees with holomorphic evaluation on some open neighborhood of K(A) where its entries are holomorphic. The definition itself assumes neither completeness nor that H is nonzero. ZeroConclusion(A) instead asserts W(A)=∅ and, for every matrix size, every polynomial, every function F and set U, and every rational matrix, the respective operator evaluations and suprema over W(A) vanish and satisfy the factor-two inequalities. SharpConstant is the defined proposition that some operator on ℂ² and scalar polynomial of degree at most one have supremum norm one on W(A) and amplified evaluation norm two; these propositions are definitions, not proved results in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CrouzeixHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CrouzeixHilbert.lean; bytes 16..6277
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! The sharp complete inequality for bounded operators on complex Hilbert spaces. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace
open Set

namespace CrouzeixHilbert

universe u

abbrev Operator (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H
abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : Operator H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z}

def numericalClosure (A : Operator H) : Set ℂ := closure (numericalRange A)

def supNorm {E : Type*} [NormedAddCommGroup E] (S : Set ℂ) (F : ℂ → E) : ℝ :=
  sSup (insert 0 ((fun z => ‖F z‖) '' S))

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] EuclideanSpace ℂ (Fin m))

def tensorOperator (A : Operator H) {m : ℕ} (B : Coeff m) :
    Operator (Amplification H m) :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def polynomialEval (A : Operator H) {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Operator (Amplification H m) :=
  ∑ k : Fin (d + 1), tensorOperator (A ^ (k : ℕ)) (B k)

structure SmoothContour where
  path : ℝ → ℂ
  smooth : ContDiff ℝ 1 path
  closed : path 0 = path 1

def SmoothContour.index (Γ : SmoothContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)

structure CalculusContour (K U : Set ℂ) extends SmoothContour where
  avoids : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ U \ K
  index_inside : ∀ z ∈ K, toSmoothContour.index z = 1
  index_outside : ∀ z ∉ U, toSmoothContour.index z = 0

def contourEval (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) : Operator H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, (deriv Γ.path t * f (Γ.path t)) •
      Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)

def holomorphicEval (A : Operator H) (U : Set ℂ) (f : ℂ → ℂ) : Operator H := by
  classical
  exact if h : Nonempty (CalculusContour (numericalClosure A) U) then
    contourEval A (Classical.choice h).toSmoothContour f
  else 0

def matrixHolomorphicEval (A : Operator H) {m : ℕ} (U : Set ℂ)
    (F : ℂ → Coeff m) : Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (holomorphicEval A U (fun z => F z i j))
    (Matrix.single i j 1)

def EntrywiseHolomorphic {m : ℕ} (U : Set ℂ) (F : ℂ → Coeff m) : Prop :=
  ∀ i j, DifferentiableOn ℂ (fun z => F z i j) U

abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def PolesOutside {m : ℕ} (K : Set ℂ) (R : RationalMatrix m) : Prop :=
  ∀ i j z, z ∈ K → (R i j).denom.eval z ≠ 0

def matrixRationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalEval (A : Operator H) (r : RatFunc ℂ) : Operator H :=
  (Polynomial.aeval A r.num) * Ring.inverse (Polynomial.aeval A r.denom)

def matrixRationalEval (A : Operator H) {m : ℕ} (R : RationalMatrix m) :
    Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (rationalEval A (R i j)) (Matrix.single i j 1)

def NonzeroConclusion (A : Operator H) : Prop :=
  IsCompact (numericalClosure A) ∧
  Convex ℝ (numericalClosure A) ∧
  spectrum ℂ A ⊆ numericalClosure A ∧
  (∀ (m : ℕ), 0 < m → ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) ∧
    supNorm (numericalRange A) (matrixPolynomial B) =
      supNorm (numericalClosure A) (matrixPolynomial B) ∧
    ∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixPolynomial B) = ‖matrixPolynomial B z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (U : Set ℂ) (F : ℂ → Coeff m),
    IsOpen U → numericalClosure A ⊆ U → EntrywiseHolomorphic U F →
    Nonempty (CalculusContour (numericalClosure A) U) ∧
    (∀ Γ : CalculusContour (numericalClosure A) U, ∀ i j,
      holomorphicEval A U (fun z => F z i j) =
        contourEval A Γ.toSmoothContour (fun z => F z i j)) ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F ∧
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (R : RationalMatrix m),
    PolesOutside (numericalClosure A) R →
    (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalClosure A) (matrixRationalFunction R) ∧
    (∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixRationalFunction R) =
        ‖matrixRationalFunction R z‖) ∧
    ∃ U : Set ℂ, IsOpen U ∧ numericalClosure A ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      matrixRationalEval A R = matrixHolomorphicEval A U (matrixRationalFunction R))

def ZeroConclusion (A : Operator H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m d : ℕ) (B : Fin (d + 1) → Coeff m),
    polynomialEval A B = 0 ∧
    supNorm (numericalRange A) (matrixPolynomial B) = 0 ∧
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)) ∧
  (∀ (m : ℕ) (U : Set ℂ) (F : ℂ → Coeff m),
    matrixHolomorphicEval A U F = 0 ∧
    supNorm (numericalRange A) F = 0 ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalRange A) F) ∧
  (∀ (m : ℕ) (R : RationalMatrix m),
    matrixRationalEval A R = 0 ∧
    supNorm (numericalRange A) (matrixRationalFunction R) = 0 ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalRange A) (matrixRationalFunction R))

def SharpConstant : Prop :=
  ∃ (A : Operator (EuclideanSpace ℂ (Fin 2))) (B : Fin 2 → Coeff 1),
    supNorm (numericalRange A) (matrixPolynomial (d := 1) B) = 1 ∧
    ‖polynomialEval A (d := 1) B‖ = 2

end CrouzeixHilbert

namespace CrouzeixHilbert

universe u



end CrouzeixHilbert
end
end OAI


