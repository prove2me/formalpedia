-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_Calculus
-- name    : QMatVecLB_ConvexOpt_Calculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:35.963989+00:00
-- url     : https://prove2.me/theorems/b552b8cf-1db7-460d-864a-6bf2647dae44
-- title:
--   Coordinate differential operators and the plus-sign Fourier transform
-- statement:
--   The coordinate derivative is the real directional derivative along a matrix unit. Iterated coordinate derivatives define polynomial differential operators and the signed permutation sum defining the Cayley operator and its minors. Fourier transformation uses $e^{+2\pi i\langle X,M\rangle}$ and product Lebesgue measure. The Gaussian density, the differential definition $q(X)=e^{\langle X,X\rangle/2}\det(\partial_X)^2e^{-\langle X,X\rangle/2}$, polynomial Cayley operator, rising product and right-invariant operators are concrete definitions. These provide the common analytic interface for Sections 3, 5 and 6.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 7 (printed p. 6).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_GridOracle

noncomputable section

namespace QMatVecLB.ConvexOpt
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

/-- Coordinate direction E_ij. -/
def matrixUnit {n : ℕ} (ij : Fin n × Fin n) : RMat n :=
  fun i j => if (i, j) = ij then 1 else 0

def coordDerivative {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ij : Fin n × Fin n) (F : RMat n → E) : RMat n → E :=
  fun X => lineDeriv ℝ F X (matrixUnit ij)

/-- A fixed coordinate order; order is immaterial on smooth functions. -/
def mixedPartial {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : (Fin n × Fin n) →₀ ℕ) (F : RMat n → E) : RMat n → E := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).toList.flatMap
    (fun ij => List.replicate (a ij) ij)).foldr (fun ij G => coordDerivative ij G) F

/-- Equation (17), with real signs acting also on complex-valued functions. -/
def cayley {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : RMat n → E) : RMat n → E := by
  classical
  exact fun X => ∑ σ : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign σ : ℤ) : ℝ) •
      ((List.finRange n).foldr (fun i G => coordDerivative (i, σ i) G) F) X)

/-- Ordered r by r minor of the differential operator, with coefficient c. -/
def minorCayley {n r : ℕ} (rows cols : Fin r → Fin n) (c : ℂ)
    (F : RMat n → ℂ) : RMat n → ℂ := by
  classical
  exact fun X => c ^ r * ∑ σ : Equiv.Perm (Fin r),
    (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((List.finRange r).foldr (fun i G => coordDerivative (rows i, cols (σ i)) G) F) X)

/-- P(∂), with P in the complex polynomial ring of matrix coordinates. -/
def polynomialDiff {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℂ)
    (F : RMat n → ℂ) : RMat n → ℂ :=
  fun X => ∑ a ∈ P.support, P.coeff a * mixedPartial a F X

def matrixLebesgue (n : ℕ) : Measure (RMat n) :=
  Measure.pi (fun _ => Measure.pi (fun _ => (volume : Measure ℝ)))

/-- Equation (18): the plus-sign Fourier transform. -/
def fourierPlus {n : ℕ} (F : RMat n → ℂ) (M : RMat n) : ℂ :=
  ∫ X, phaseExp (matrixPair X M) * F X ∂matrixLebesgue n

/-- Equation (46), before and after normalization. -/
def gaussianKernel {n : ℕ} (X : RMat n) : ℝ := Real.exp (-matrixPair X X / 2)
def gamma {n : ℕ} (X : RMat n) : ℝ :=
  (2 * Real.pi) ^ (-((n * n : ℕ) : ℝ) / 2) * gaussianKernel X
/-- Equation (56), retaining the actual differential construction. -/
def q {n : ℕ} (X : RMat n) : ℝ :=
  Real.exp (matrixPair X X / 2) * cayley (cayley gaussianKernel) X

/-- Polynomial determinant and polynomial Cayley operator for Lemma 5.3. -/
def detPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) ℝ :=
  Matrix.det (fun i j => MvPolynomial.X (i,j))
def polynomialCayley {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℝ) :
    MvPolynomial (Fin n × Fin n) ℝ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n),
    MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℝ)) *
      (List.finRange n).foldr (fun i G => MvPolynomial.pderiv (i, σ i) G) P

def rising (z n : ℕ) : ℝ := ∏ j ∈ Finset.range n, ((z + j : ℕ) : ℝ)

/-- Equation (94): the right-invariant first-order operator. -/
def rightDerivative {n : ℕ} (ij : Fin n × Fin n) (F : RMat n → ℝ) : RMat n → ℝ :=
  fun B => deriv (fun t : ℝ => F (B * (1 + t • matrixUnit ij))) 0

def rightComposite {n : ℕ} (indices : List (Fin n × Fin n))
    (F : RMat n → ℝ) : RMat n → ℝ :=
  indices.foldr (fun ij G => rightDerivative ij G) F

def invertibles (n : ℕ) : Set (RMat n) := {B | B.det ≠ 0}
def boundedOn {X : Type*} (F : X → ℝ) (S : Set X) : Prop :=
  ∃ C : ℝ, ∀ x ∈ S, |F x| ≤ C

end QMatVecLB.ConvexOpt
end


