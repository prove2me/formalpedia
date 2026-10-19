-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13
-- name    : QAlgorithms_Papers_Independent_Frontier30_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:16:32.543526+00:00
-- url     : https://prove2.me/theorems/4b216676-1a2e-4c1b-9b2c-ff9ab4ec4998
-- title:
--   Definitions for The characterization of Gaussian operations and Distillation of Gaussian States
-- statement:
--   The objects the formalized statements of *The characterization of Gaussian operations and Distillation of Gaussian States* (arXiv:quant-ph/0204085) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ModeQuadrature`: Section II, PDF p.2: X and P coordinates for each mode.
--   - `BipPhase`: Section IV, PDF p.4: all A coordinates precede all B coordinates.
--   - `phaseJ`: Section II, PDF p.2, Eq.(3): J_XP = -1 and J_PX = 1.
--   - `bipJ`: Section IV, PDF p.4: canonical form for the A|B partition.
--   - `feasibleScale`: Section IVB, PDF p.5; Appendix A, PDF p.6, Eq.(A1): feasible scale. Nonnegative scales preserve the maximum because finite physical covariances have a strictly positive feasible scale. Witnesses are physical local CMs.
--   - `valueV`: Appendix A, PDF p.6, Eq.(A1): supremum of feasible scales. Attainment and strict positivity are conclusions of `valueDomain`. Its totalized value outside the finite physical domain is never used.
--   - `reversal`: Section II, PDF p.2, Eq.(5): momentum reversal.
--   - `partialTransposeCM`: Appendix A, PDF pp.6–7: partial transpose on A in covariance coordinates. This positive definite matrix need not satisfy the uncertainty inequality.
--   - `symplecticSpectrum`: Appendix A, PDF pp.6–7: for real positive definite G, its positive symplectic eigenvalues are the positive roots of det(G-i t J). No uncertainty inequality is required of G.
--   - `lambdaMin`: Appendix A, PDF pp.6–7: smallest symplectic eigenvalue after partial transpose. Used only on nonempty finite physical bipartitions, for which the positive spectrum is nonempty and finite and has an attained minimum. The total real infimum outside this domain is not used as an eigenvalue.
--   - `squeezedCM`: Section II, PDF p.2, Eqs.(4)–(5): finite EPR covariance family. The source r is twice the frequently used squeezing parameter.
--   - `familyIndex`: Appendix A, PDF p.6, Eq.(A2): regroup all A modes before all B modes, retaining the family label and within-party quadrature coordinate.
--   - `familyCM`: Appendix A, PDF p.6, Eq.(A2): finite tensor-product covariance, permuted from (A1 B1 A2 B2 ...) to (A1 A2 ... | B1 B2 ...). Distinct family blocks are zero; factors may have different finite local mode counts.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, https://arxiv.org/abs/quant-ph/0204085v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
Finite covariance results of Giedke and Cirac, arXiv:quant-ph/0204085v4.
Entrywise complexification and the physical covariance predicate are imported
from the accepted library; the remaining definitions are paper-local.
Quadratures are interleaved: false means X,
true means P; vacuum covariance is I. Matrices here are covariance data, not
surrogate density operators or instruments. Operational deferrals are in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)
open scoped ComplexOrder

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Section II, PDF p.2: X and P coordinates for each mode. -/
abbrev ModeQuadrature (A : Type*) := A × Bool

/-- Section IV, PDF p.4: all A coordinates precede all B coordinates. -/
abbrev BipPhase (A B : Type*) := ModeQuadrature A ⊕ ModeQuadrature B

/-- Section II, PDF p.2, Eq.(3): J_XP = -1 and J_PX = 1. -/
def phaseJ (A : Type*) : Matrix (ModeQuadrature A) (ModeQuadrature A) ℝ :=
  fun i j => if i.1 = j.1 then
    if i.2 = j.2 then 0 else if i.2 then 1 else -1
  else 0

/-- Section IV, PDF p.4: canonical form for the A|B partition. -/
def bipJ (A B : Type*) : Matrix (BipPhase A B) (BipPhase A B) ℝ :=
  Matrix.fromBlocks (phaseJ A) 0 0 (phaseJ B)

/-- Section IVB, PDF p.5; Appendix A, PDF p.6, Eq.(A1): feasible scale.
Nonnegative scales preserve the maximum because finite physical covariances
have a strictly positive feasible scale. Witnesses are physical local CMs. -/
def feasibleScale {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
  ∃ GA : Matrix (ModeQuadrature A) (ModeQuadrature A) ℝ,
  ∃ GB : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ,
    physicalCovariance GA (phaseJ A) ∧ physicalCovariance GB (phaseJ B) ∧
    (G - p • Matrix.fromBlocks GA 0 0 GB).PosSemidef

/-- Appendix A, PDF p.6, Eq.(A1): supremum of feasible scales.
Attainment and strict positivity are conclusions of `valueDomain`.
Its totalized value outside the finite physical domain is never used. -/
def valueV {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) : ℝ :=
  sSup {p | feasibleScale G p}

/-- Section II, PDF p.2, Eq.(5): momentum reversal. -/
def reversal (A : Type*) : Matrix (ModeQuadrature A) (ModeQuadrature A) ℝ :=
  Matrix.diagonal (fun i => if i.2 then -1 else 1)

/-- Appendix A, PDF pp.6–7: partial transpose on A in covariance coordinates.
This positive definite matrix need not satisfy the uncertainty inequality. -/
def partialTransposeCM {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) :
    Matrix (BipPhase A B) (BipPhase A B) ℝ :=
  let L := Matrix.fromBlocks (reversal A) 0 0 (1 : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ)
  L * G * L

/-- Appendix A, PDF pp.6–7: for real positive definite G, its positive
symplectic eigenvalues are the positive roots of det(G-i t J).
No uncertainty inequality is required of G. -/
def symplecticSpectrum {I : Type*} [Fintype I]
    (G J : Matrix I I ℝ) : Set ℝ :=
  {t | 0 < t ∧ (complexify G - ((t : ℂ) * Complex.I) • complexify J).det = 0}

/-- Appendix A, PDF pp.6–7: smallest symplectic eigenvalue after partial
transpose. Used only on nonempty finite physical bipartitions, for which the
positive spectrum is nonempty and finite and has an attained minimum.
The total real infimum outside this domain is not used as an eigenvalue. -/
def lambdaMin {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) : ℝ :=
  sInf (symplecticSpectrum (partialTransposeCM G) (bipJ A B))

/-- Section II, PDF p.2, Eqs.(4)–(5): finite EPR covariance family.
The source r is twice the frequently used squeezing parameter. -/
def squeezedCM (n : ℕ) (r : ℝ) :
    Matrix (BipPhase (Fin n) (Fin n)) (BipPhase (Fin n) (Fin n)) ℝ :=
  Matrix.fromBlocks
    (Real.cosh r • (1 : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ))
    (Real.sinh r • reversal (Fin n))
    (Real.sinh r • reversal (Fin n))
    (Real.cosh r • (1 : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ))

/-- Appendix A, PDF p.6, Eq.(A2): regroup all A modes before all B modes,
retaining the family label and within-party quadrature coordinate. -/
def familyIndex {K : Type*} (a b : K → ℕ) :
    BipPhase (Σ k, Fin (a k)) (Σ k, Fin (b k)) → Σ k, BipPhase (Fin (a k)) (Fin (b k))
  | Sum.inl (⟨k, j⟩, q) => ⟨k, Sum.inl (j, q)⟩
  | Sum.inr (⟨k, j⟩, q) => ⟨k, Sum.inr (j, q)⟩

/-- Appendix A, PDF p.6, Eq.(A2): finite tensor-product covariance, permuted
from (A1 B1 A2 B2 ...) to (A1 A2 ... | B1 B2 ...). Distinct family blocks
are zero; factors may have different finite local mode counts. -/
def familyCM {K : Type*} (a b : K → ℕ)
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k)))
      (BipPhase (Fin (a k)) (Fin (b k))) ℝ) :
    Matrix (BipPhase (Σ k, Fin (a k)) (Σ k, Fin (b k)))
      (BipPhase (Σ k, Fin (a k)) (Σ k, Fin (b k))) ℝ :=
  fun i j =>
    let u := familyIndex a b i
    let v := familyIndex a b j
    if h : u.1 = v.1 then G u.1 u.2 (h.symm ▸ v.2) else 0

example : phaseJ (Fin 1) (0, false) (0, true) = -1 := by
  simp [phaseJ]

example : phaseJ (Fin 1) (0, true) (0, false) = 1 := by
  simp [phaseJ]

example : reversal (Fin 1) (0, true) (0, true) = -1 := by
  simp [reversal]

example (n : ℕ) : squeezedCM n 0 = 1 := by
  simpa only [squeezedCM, Real.cosh_zero, Real.sinh_zero, one_smul, zero_smul]
    using (Matrix.fromBlocks_one :
      Matrix.fromBlocks (1 : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ)
        0 0 (1 : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ) = 1)

end QAlgorithms.Papers.Independent.Frontier30.P13


