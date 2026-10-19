-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixDistances
-- name    : QAlgorithms_Defs_MatrixDistances
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:15:54.875512+00:00
-- url     : https://prove2.me/theorems/6421c11f-50fc-483e-9d2b-7b7ed7ea5111
-- title:
--   MatrixDistances
-- statement:
--   MatrixDistances
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixDistances.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- For an arbitrary square complex matrix M, traceNorm M = Re Tr(cfc Real.sqrt (M.conjTranspose * M)). Source: arxiv-2405.06051v6 PDF p.4; arxiv-1804.05058v1 PDF p.5; arxiv-1804.05058v1 PDF p.14. -/
def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.sqrt (Mᴴ * M)).trace.re

/-- For a density matrix rho, lambdaMinPositive rho is the minimum over its STRICTLY POSITIVE eigenvalues, with multiplicity irrelevant; use a finite nonempty spectral-support subtype. Source: arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.24. -/
def minPositiveEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ :=
  let s := Finset.univ.filter fun k => 0 < ascEigenvalues M k
  if h : s.Nonempty then s.inf' h (ascEigenvalues M) else 0

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.24. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] : traceNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [traceNorm, cfc_zero]

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.24. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] : traceNorm (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  simp [traceNorm, cfc_one]

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.24. -/
example (M : Matrix (Fin 0) (Fin 0) ℂ) : minPositiveEigenvalue M = 0 := by
  have h : ¬ (Finset.univ.filter fun k => 0 < ascEigenvalues M k).Nonempty := by
    rintro ⟨k, hk⟩
    exact Fin.elim0 k
  simp only [minPositiveEigenvalue, dif_neg h]

/-- The minimum positive eigenvalue excludes zero eigenvalues of a rank-deficient state.
Source: arxiv-2405.06051v6 PDF pp.12,24. -/
example : minPositiveEigenvalue (Matrix.diagonal ![(1 : ℂ), 0]) = 1 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  have hA : A.IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    fin_cases i <;> simp [A]
  have hc : A.charpoly = (Polynomial.X - Polynomial.C (1 : ℂ)) * Polynomial.X := by
    simp [A, Matrix.charpoly_diagonal, Fin.prod_univ_two]
  have hs : List.ofFn hA.eigenvalues₀ = [1, 0] := by
    rw [← hA.sort_roots_charpoly_eq_eigenvalues₀, hc,
      Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℂ)) Polynomial.X_ne_zero),
      Polynomial.roots_X_sub_C, Polynomial.roots_X]
    norm_num [Multiset.sort_cons]
  have hv : hA.eigenvalues₀ = (![1, 0] : Fin 2 → ℝ) := by
    apply List.ofFn_inj.mp
    rw [hs]
    rfl
  have ha : ascEigenvalues A = (![0, 1] : Fin 2 → ℝ) := by
    funext k
    simp only [ascEigenvalues, dif_pos hA, hv]
    fin_cases k <;> rfl
  have hf : (Finset.univ : Finset (Fin 2)).filter (fun k => 0 < ascEigenvalues A k) = {1} := by
    ext k
    constructor
    · intro hk
      have hp := (Finset.mem_filter.mp hk).2
      rw [ha] at hp
      fin_cases k
      · change (0 : ℝ) < 0 at hp
        exact False.elim ((lt_irrefl 0) hp)
      · exact Finset.mem_singleton.mpr rfl
    · intro hk
      have he : k = 1 := Finset.mem_singleton.mp hk
      subst k
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ha]
      change (0 : ℝ) < 1
      norm_num
  change minPositiveEigenvalue A = 1
  unfold minPositiveEigenvalue
  change (if h : ((Finset.univ : Finset (Fin 2)).filter fun k => 0 < ascEigenvalues A k).Nonempty
    then ((Finset.univ : Finset (Fin 2)).filter fun k => 0 < ascEigenvalues A k).inf' h
      (ascEigenvalues A) else 0) = 1
  rw [hf]
  simp [ha]

end QAlgorithms


