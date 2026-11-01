-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P12
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:47:01.282205+00:00
-- url     : https://prove2.me/theorems/db1ce40a-c364-44a7-8c6c-a2ce26b027d4
-- title:
--   Definitions for Extremal Quantum States in Coupled Systems
-- statement:
--   The objects the formalized statements of *Extremal Quantum States in Coupled Systems* (arXiv:quant-ph/0307182) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteCouplingSet`: PDF p.5: ALL normalized PSD joint operators with the specified partial traces.
--   - `flatMatrix`: PDF pp.4–5: lexicographic coordinates, second index varying fastest.
--   - `rankSplitEquiv`: PDF p.3: concatenate the leading k and trailing n-k coordinates. The guard makes subtraction exact, including k=0 and k=n.
--   - `permuteMatrix`: PDF pp.3,5: sigma M sigma^{-1}, where sigma sends |p(i)> to |i>. Thus inverse conjugation is obtained by replacing p with p.symm.
--   - `rankBlockMatrix`: PDF p.3, (2.1): block completion, with no positivity assumption on its argument.
--   - `rankRow`: PDF p.6: R=[I_k|A] in the same flattened rank coordinates.
--   - `physicalPerturbation`: PDF p.5, (2.10): undo sigma, then restore physical tensor coordinates BEFORE taking either partial trace.
--   - `NoZeroMarginalPerturbation`: PDF pp.5–7: no nonzero Hermitian perturbation with BOTH marginals zero.
--   - `compressedLocalSpace`: PDF pp.6,8: image of the REAL Hermitian local-sum space; no complex span. Printed: column [I;A^t]. Changed: R.conjTranspose=[I;A†]. Why: preceding trace identity (2.11), PDF p.6, has A†; PDF p.11 expands this as AXA†. The correction remains subject to independent moderation.
--   - `omegaFromBasis`: PDF p.9, Theorem 3.1: construct Omega from an actual complex orthonormal basis.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, https://arxiv.org/abs/quant-ph/0307182v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
K. R. Parthasarathy, Extremal Quantum States in Coupled Systems, quant-ph/0307182v1.
All page references are PDF pages. Coordinates are relative to arbitrary chosen
subsystem orthonormal bases. Product indexing j+d2*i is lexicographic.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- PDF p.5: ALL normalized PSD joint operators with the specified partial traces. -/
def finiteCouplingSet {d1 d2 : ℕ} (rho1 : Matrix (Fin d1) (Fin d1) ℂ)
    (rho2 : Matrix (Fin d2) (Fin d2) ℂ) :
    Set (Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ) :=
  {rho | IsDensityMatrix rho ∧ traceRight rho = rho1 ∧ traceLeft rho = rho2}

/-- PDF pp.4–5: lexicographic coordinates, second index varying fastest. -/
def flatMatrix {d1 d2 : ℕ} (M : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ) :
    Matrix (Fin (d1*d2)) (Fin (d1*d2)) ℂ :=
  M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- PDF p.3: concatenate the leading k and trailing n-k coordinates.
The guard makes subtraction exact, including k=0 and k=n. -/
def rankSplitEquiv {n k : ℕ} (h : k ≤ n) : (Fin k ⊕ Fin (n-k)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- PDF pp.3,5: sigma M sigma^{-1}, where sigma sends |p(i)> to |i>.
Thus inverse conjugation is obtained by replacing p with p.symm. -/
def permuteMatrix {n : ℕ} (p : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  M.submatrix p p

/-- PDF p.3, (2.1): block completion, with no positivity assumption on its argument. -/
def rankBlockMatrix {n k : ℕ} (h : k ≤ n) (K : Matrix (Fin k) (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin (n-k)) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.fromBlocks K (K*A) (A.conjTranspose*K)
    (A.conjTranspose*K*A)).submatrix (rankSplitEquiv h).symm (rankSplitEquiv h).symm

/-- PDF p.6: R=[I_k|A] in the same flattened rank coordinates. -/
def rankRow {n k : ℕ} (h : k ≤ n) (A : Matrix (Fin k) (Fin (n-k)) ℂ) :
    Matrix (Fin k) (Fin n) ℂ :=
  fun i j => match (rankSplitEquiv h).symm j with
    | Sum.inl l => if i = l then 1 else 0
    | Sum.inr l => A i l

/-- PDF p.5, (2.10): undo sigma, then restore physical tensor coordinates
BEFORE taking either partial trace. -/
def physicalPerturbation {d1 d2 k : ℕ} (h : k ≤ d1*d2)
    (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) (L : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ :=
  (permuteMatrix p.symm (rankBlockMatrix h L A)).submatrix finProdFinEquiv finProdFinEquiv

/-- PDF pp.5–7: no nonzero Hermitian perturbation with BOTH marginals zero. -/
def NoZeroMarginalPerturbation {d1 d2 k : ℕ} (h : k ≤ d1*d2)
    (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) : Prop :=
  ∀ L : Matrix (Fin k) (Fin k) ℂ, L.IsHermitian →
    traceRight (physicalPerturbation h p A L) = 0 →
    traceLeft (physicalPerturbation h p A L) = 0 → L = 0

/-- PDF pp.6,8: image of the REAL Hermitian local-sum space; no complex span.
Printed: column [I;A^t]. Changed: R.conjTranspose=[I;A†]. Why: preceding
trace identity (2.11), PDF p.6, has A†; PDF p.11 expands this as AXA†.
The correction remains subject to independent moderation. -/
def compressedLocalSpace {d1 d2 k : ℕ} (h : k ≤ d1*d2)
    (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {M | ∃ (X1 : Matrix (Fin d1) (Fin d1) ℂ) (X2 : Matrix (Fin d2) (Fin d2) ℂ),
    X1.IsHermitian ∧ X2.IsHermitian ∧
    M = rankRow h A * permuteMatrix p
      (flatMatrix (Matrix.kronecker X1 (1 : Matrix (Fin d2) (Fin d2) ℂ) +
        Matrix.kronecker (1 : Matrix (Fin d1) (Fin d1) ℂ) X2)) *
      (rankRow h A).conjTranspose}

/-- PDF p.9, Theorem 3.1: construct Omega from an actual complex orthonormal basis. -/
noncomputable def omegaFromBasis
    (psi : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) :
    EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (tensorVec (ket (0 : Fin 2)) (psi 0) + tensorVec (ket (1 : Fin 2)) (psi 1))

/-! Sanity checks of coordinate order and block orientation. -/

example {d1 d2 : ℕ} (rho1 : Matrix (Fin d1) (Fin d1) ℂ)
    (rho2 : Matrix (Fin d2) (Fin d2) ℂ)
    (rho : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ) :
    rho ∈ finiteCouplingSet rho1 rho2 ↔
      IsDensityMatrix rho ∧ traceRight rho = rho1 ∧ traceLeft rho = rho2 := Iff.rfl

example {d1 d2 : ℕ} (M : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ)
    (i j : Fin d1 × Fin d2) :
    flatMatrix M (finProdFinEquiv i) (finProdFinEquiv j) = M i j := by
  change M (finProdFinEquiv.symm (finProdFinEquiv i))
    (finProdFinEquiv.symm (finProdFinEquiv j)) = M i j
  simp only [Equiv.symm_apply_apply]

example {n k : ℕ} (h : k ≤ n) (i : Fin k) :
    (rankSplitEquiv h).symm (rankSplitEquiv h (Sum.inl i)) = Sum.inl i :=
  (rankSplitEquiv h).symm_apply_apply _

example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    permuteMatrix (Equiv.refl _) M = M := rfl

example {n k : ℕ} (h : k ≤ n) (K : Matrix (Fin k) (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin (n-k)) ℂ) (i j : Fin k) :
    rankBlockMatrix h K A (rankSplitEquiv h (Sum.inl i))
      (rankSplitEquiv h (Sum.inl j)) = K i j := by
  simp [rankBlockMatrix, Matrix.submatrix]

example {n k : ℕ} (h : k ≤ n) (A : Matrix (Fin k) (Fin (n-k)) ℂ)
    (i : Fin k) (j : Fin (n-k)) :
    rankRow h A i (rankSplitEquiv h (Sum.inr j)) = A i j := by
  simp [rankRow]

example {d1 d2 k : ℕ} (h : k ≤ d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) (L : Matrix (Fin k) (Fin k) ℂ)
    (i j : Fin d1 × Fin d2) :
    physicalPerturbation h p A L i j = rankBlockMatrix h L A
      (p.symm (finProdFinEquiv i)) (p.symm (finProdFinEquiv j)) := rfl

example {d1 d2 k : ℕ} (h : k ≤ d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) :
    (0 : Matrix (Fin k) (Fin k) ℂ) ∈ compressedLocalSpace h p A := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian]
  · simp [Matrix.IsHermitian]
  · have hzero :
        Matrix.kronecker (0 : Matrix (Fin d1) (Fin d1) ℂ)
          (1 : Matrix (Fin d2) (Fin d2) ℂ) +
        Matrix.kronecker (1 : Matrix (Fin d1) (Fin d1) ℂ)
          (0 : Matrix (Fin d2) (Fin d2) ℂ) = 0 := by
      ext i j
      simp [Matrix.kronecker, Matrix.kroneckerMap]
    rw [hzero]
    change (0 : Matrix (Fin k) (Fin k) ℂ) =
      rankRow h A * (0 : Matrix (Fin (d1*d2)) (Fin (d1*d2)) ℂ) *
        (rankRow h A).conjTranspose
    simp only [Matrix.mul_zero, Matrix.zero_mul]

example {d1 d2 : ℕ} (h : 0 ≤ d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin 0) (Fin (d1*d2-0)) ℂ) :
    NoZeroMarginalPerturbation h p A := by
  intro L _ _ _
  exact Subsingleton.elim _ _

example (psi : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) (j : Fin 2) :
    omegaFromBasis psi (0, j) = ((Real.sqrt 2)⁻¹ : ℂ) * psi 0 j := by
  simp [omegaFromBasis, tensorVec, ket]

end QAlgorithms.Papers.Independent.Intakethird100.P12


