-- Prove2me | Definitions.Def_QAlgorithms_Defs_ApproximateMatrixMultiplicationContracts
-- name    : QAlgorithms_Defs_ApproximateMatrixMultiplicationContracts
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:12.549107+00:00
-- url     : https://prove2.me/theorems/c2c75565-0d40-4368-8127-72894f52fccf
-- title:
--   ApproximateMatrixMultiplicationContracts
-- statement:
--   ApproximateMatrixMultiplicationContracts
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ApproximateMatrixMultiplicationContracts.lean

import Definitions.Def_QAlgorithms_Defs_MultipleMatrixSketches
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
namespace QAlgorithms.MatrixApprox

variable {n k : ℕ}

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.1. -/
def frobeniusNorm (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, A i j^2)

/-- Event real Frobenius norm(Ctilde-orderedProduct(A))<=eps on actual classical matrix-output law. All inputs including zero factors. Source: arxiv-2510.08509v1 PDF p.1; arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2510.08509v1 PDF p.21; arxiv-2510.08509v1 PDF p.22. -/
def frobeniusSuccess (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) (eps : ℝ)
    (estimate : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  0 < eps ∧ frobeniusNorm (estimate-(List.ofFn A).prod) ≤ eps

/-- Event entrywise maximum norm(Ctilde-orderedProduct(A))<=eps on actual classical matrix-output law. Same input/accuracy domain as source. Source: arxiv-2510.08509v1 PDF p.1; arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2510.08509v1 PDF p.21; arxiv-2510.08509v1 PDF p.22. -/
def maxSuccess (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) (eps : ℝ)
    (estimate : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  0 < eps ∧ ∀ i j, |estimate i j-(List.ofFn A).prod i j| ≤ eps

/-- Success events on execution-induced classical matrix laws: Frobenius or entrywise max error≤ε, each probability≥1−δ for every input. Separate preprocessing Õ(kn²) and printed online scales n²(3^kF²/ε²)^(ω−2),n²3^kF/ε. Quantify positive constants, fixed logarithmic exponents, thresholds before varying n,k,A,ε,δ, after fixed multiplication implementation. Keep formal confidence logs and use max 1 logarithms only for boundary totalization; large-scale asymptotic contract plus explicit direct behavior at small/zero scales. No nonzero input assumption or weaker unconstrained-estimator goal. Source: arxiv-2510.08509v1 PDF p.1; arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2510.08509v1 PDF p.21; arxiv-2510.08509v1 PDF p.22. -/
def SoftTimeContract {Input : Type*} (preprocessing online : Input → ℕ)
    (n k : Input → ℕ) (eps delta scale : Input → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ input, 0 < n input → 0 < k input → 0 < eps input → 0 < delta input → delta input < 1 →
    threshold ≤ scale input →
      (preprocessing input : ℝ) ≤ C*k input*n input^2*
        max 1 (Real.log (2+n input+k input+(delta input)⁻¹))^p ∧
      (online input : ℝ) ≤ C*scale input*
        max 1 (Real.log (2+n input+k input+(delta input)⁻¹+scale input))^p

example : frobeniusNorm (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by simp [frobeniusNorm]

end QAlgorithms.MatrixApprox


