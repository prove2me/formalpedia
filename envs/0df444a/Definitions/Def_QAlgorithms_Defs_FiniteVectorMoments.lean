-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteVectorMoments
-- name    : QAlgorithms_Defs_FiniteVectorMoments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:19.893863+00:00
-- url     : https://prove2.me/theorems/07c20494-9ed2-4b1b-a501-10387c154eff
-- title:
--   FiniteVectorMoments
-- statement:
--   FiniteVectorMoments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FiniteVectorMoments.lean

import Definitions.Def_QAlgorithms_Defs_Learning
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.FiniteVectorMoments

variable {Omega : Type*} [Fintype Omega] {d : ℕ}

/-- Computed mu=sum_w P(w)X(w). Finite normalized nonnegative P satisfies frozen Learning.IsDistribution; X is EuclideanSpace Real (Fin d). Finite support makes all moments integrable; no variance bound is a field. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2607.25492v2 PDF p.23; arxiv-2510.08509v1 PDF p.14; arxiv-2510.08509v1 PDF p.20. -/
def mean (P : Omega → ℝ) (_hP : Learning.IsDistribution P)
    (X : Omega → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := ∑ w, P w • X w

/-- Computed Sigma_ij=sum_w P(w)(X_i-mu_i)(X_j-mu_j). Finite normalized nonnegative P satisfies frozen Learning.IsDistribution; X is EuclideanSpace Real (Fin d). Finite support makes all moments integrable; no variance bound is a field. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2607.25492v2 PDF p.23; arxiv-2510.08509v1 PDF p.14; arxiv-2510.08509v1 PDF p.20. -/
def covariance (P : Omega → ℝ) (hP : Learning.IsDistribution P)
    (X : Omega → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ w, P w * (X w i - mean P hP X i) * (X w j - mean P hP X j)

/-- Computed sum_w P(w)||X(w)-mu||_2^2; its equality to covariance trace is a sanity theorem. Finite normalized nonnegative P satisfies frozen Learning.IsDistribution; X is EuclideanSpace Real (Fin d). Finite support makes all moments integrable; no variance bound is a field. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2510.08509v1 PDF p.7; arxiv-2607.25492v2 PDF p.23; arxiv-2510.08509v1 PDF p.14; arxiv-2510.08509v1 PDF p.20. -/
def traceCovariance (P : Omega → ℝ) (hP : Learning.IsDistribution P)
    (X : Omega → EuclideanSpace ℝ (Fin d)) : ℝ := ∑ w, P w * ‖X w - mean P hP X‖ ^ 2

example (P : Omega → ℝ) (hP : Learning.IsDistribution P) : mean (d:=d) P hP (fun _ => 0) = 0 := by
  simp [mean]

example (P : Omega → ℝ) (hP : Learning.IsDistribution P)
    (X : Omega → EuclideanSpace ℝ (Fin d)) : (covariance P hP X).trace = traceCovariance P hP X := by
  simp only [covariance, Matrix.trace, Matrix.diag, Matrix.of_apply, traceCovariance,
    EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  ring

end QAlgorithms.FiniteVectorMoments


