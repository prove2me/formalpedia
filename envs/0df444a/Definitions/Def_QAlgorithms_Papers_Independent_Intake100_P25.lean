-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25
-- name    : QAlgorithms_Papers_Independent_Intake100_P25
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:18:14.318402+00:00
-- url     : https://prove2.me/theorems/1fb800a4-41fc-4a29-ac07-58c452aff0b4
-- title:
--   Definitions for Generalized Conley-Zehnder index
-- statement:
--   The objects the formalized statements of *Generalized Conley-Zehnder index* (arXiv:1307.7239) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `realShift`: Real shift, for the real kernels on PDF pp.4,17.
--   - `realGeneralizedSpace`: The stable real generalized eigenspace; the ambient dimension is 2n, p.17.
--   - `endpointForm`: Formula (19), evaluated on the ambient vectors and restricted below, p.17. The theorem uses k>=1, so k-1 is the ordinary nonnegative exponent.
--   - `endpointSignature`: Signature on ker(A-lambda I)^(2k), including its radical, pp.4,17.
--   - `endpointSignatureSum`: The finite interpretation of the k>=1 sum made explicit on PDF p.23.
--   - `jordanBlock`: Jordan block: diagonal lambda, upper superdiagonal one, pp.17-18.
--   - `normalBlock`: The exact block in Proposition 25, including J inverse in both upper blocks, p.17.
--   - `NormalCoord`: Coordinates for an actual finite symplectic sum, with possibly no blocks, p.17.
--   - `normalAction`: Blockwise action of the displayed normal form, p.17.
--   - `normalOmega`: Symplectic form on the finite sum of normal-form blocks, p.17.
--   - `NormalFormData`: Genuine symplectic basis of the generalized eigenspace in Proposition 25, p.17. No signature identity or eigenspace count is included in this data.
--   - `normalSignSum`: The sum is derived from the actual normal-form data, never a free sign list, pp.17,23.
--   - `EndpointSplitting`: Endpoint splitting into the non-1 part and the real generalized 1-space, pp.4,22-23. The basis is an actual form-preserving linear equivalence with the ambient space.
--   - `InEndpointSplitting`: Equality with starBlock diamond B in the specified endpoint basis, pp.4,23.
--   - `hyperbolicTarget`: Both hyperbolic targets are diag(exp(-1) I, exp(1) I), PDF pp.4,23.
--   - `HasPositiveRealSpectrum`: Every complex eigenvalue is real and strictly positive, pp.4,23. This is vacuous, correctly, on a zero-dimensional block.
--   - `IsProlongation`: All four prolongation clauses of Theorems 3 and 28, PDF pp.4,23. The choices of W sign at the two ends are independent.
--   - `prolongationDegree`: Degree on [-1,2] is computed on the whole translated interval [0,3], pp.4,23.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, https://arxiv.org/abs/1307.7239v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

/-! Jean Gutt, Generalized Conley-Zehnder index, arXiv:1307.7239v1.
Grouped x,y coordinates and the positive winding convention are imported from
the pinned accepted library. The arbitrary-reference Grassmannian nodes are
explicitly deferred in the unit artifacts; no matrix-only replacement is made.
Compilation is pending under the batch compilation handoff.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Real shift, for the real kernels on PDF pp.4,17. -/
def realShift {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) :
    Module.End ℝ (Coord n → ℝ) :=
  Matrix.toLin' (A - (lambda : ℝ) • (1 : GroupedRealMatrix n))

/-- The stable real generalized eigenspace; the ambient dimension is 2n, p.17. -/
def realGeneralizedSpace {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) :
    Submodule ℝ (Coord n → ℝ) := LinearMap.ker (realShift A lambda ^ (2*n))

/-- Formula (19), evaluated on the ambient vectors and restricted below, p.17.
The theorem uses k>=1, so k-1 is the ordinary nonnegative exponent. -/
def endpointForm {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) (k : ℕ)
    (v w : Coord n → ℝ) : ℝ :=
  omegaR ((realShift A lambda ^ k) v) ((realShift A lambda ^ (k-1)) w)

/-- Signature on ker(A-lambda I)^(2k), including its radical, pp.4,17. -/
def endpointSignature {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) (k : ℕ) : ℤ :=
  formSignature (LinearMap.ker (realShift A lambda ^ (2*k)))
    (fun v => endpointForm A lambda k v v)

/-- The finite interpretation of the k>=1 sum made explicit on PDF p.23. -/
def endpointSignatureSum {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 (2*n), endpointSignature A lambda k

/-- Jordan block: diagonal lambda, upper superdiagonal one, pp.17-18. -/
def jordanBlock (lambda : ℤ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if i = j then (lambda : ℝ) else if j.val = i.val+1 then 1 else 0

/-- The exact block in Proposition 25, including J inverse in both upper blocks, p.17. -/
def normalBlock (lambda : ℤ) (r : ℕ) (d : ℤ) : GroupedRealMatrix r :=
  let J := jordanBlock lambda r
  Matrix.fromBlocks J⁻¹
    (J⁻¹ * Matrix.diagonal (fun i : Fin r => if i.val+1 = r then (d : ℝ) else 0))
    0 J.transpose

/-- Coordinates for an actual finite symplectic sum, with possibly no blocks, p.17. -/
abbrev NormalCoord {b : ℕ} (r : Fin b → ℕ) := (j : Fin b) × Coord (r j)

/-- Blockwise action of the displayed normal form, p.17. -/
def normalAction {b : ℕ} (lambda : ℤ) (r : Fin b → ℕ) (d : Fin b → ℤ)
    (v : NormalCoord r → ℝ) : NormalCoord r → ℝ :=
  fun ji => (normalBlock lambda (r ji.1) (d ji.1)).mulVec
    (fun i => v ⟨ji.1,i⟩) ji.2

/-- Symplectic form on the finite sum of normal-form blocks, p.17. -/
def normalOmega {b : ℕ} (r : Fin b → ℕ) (v w : NormalCoord r → ℝ) : ℝ :=
  ∑ j, omegaR (fun i => v ⟨j,i⟩) (fun i => w ⟨j,i⟩)

/-- Genuine symplectic basis of the generalized eigenspace in Proposition 25, p.17.
No signature identity or eigenspace count is included in this data. -/
structure NormalFormData {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) where
  blockCount : ℕ
  size : Fin blockCount → ℕ
  size_pos : ∀ j, 0 < size j
  sign : Fin blockCount → ℤ
  sign_values : ∀ j, sign j = 0 ∨ sign j = 1 ∨ sign j = -1
  zero_odd : ∀ j, sign j = 0 → Odd (size j)
  embedding : (NormalCoord size → ℝ) →ₗ[ℝ] (Coord n → ℝ)
  embedding_injective : Function.Injective embedding
  embedding_range : LinearMap.range embedding = realGeneralizedSpace A lambda
  symplectic_basis : ∀ v w, omegaR (embedding v) (embedding w) = normalOmega size v w
  intertwines : ∀ v, A.mulVec (embedding v) = embedding (normalAction lambda size sign v)

/-- The sum is derived from the actual normal-form data, never a free sign list, pp.17,23. -/
def normalSignSum {n : ℕ} {A : GroupedRealMatrix n} {lambda : ℤ}
    (N : NormalFormData A lambda) : ℤ := ∑ j, N.sign j

/-- Endpoint splitting into the non-1 part and the real generalized 1-space, pp.4,22-23.
The basis is an actual form-preserving linear equivalence with the ambient space. -/
structure EndpointSplitting {n : ℕ} (A : GroupedRealMatrix n) where
  starDim : ℕ
  oneDim : ℕ
  starBlock : GroupedRealMatrix starDim
  oneBlock : GroupedRealMatrix oneDim
  star_symplectic : IsSymplectic starBlock
  one_symplectic : IsSymplectic oneBlock
  star_nonfixed : (starBlock-1).det ≠ 0
  basisMap : ((Coord starDim → ℝ) × (Coord oneDim → ℝ)) ≃ₗ[ℝ] (Coord n → ℝ)
  preserves_form : ∀ v w, omegaR (basisMap v) (basisMap w) =
    omegaR v.1 w.1 + omegaR v.2 w.2
  one_range : (realGeneralizedSpace A 1 : Set (Coord n → ℝ)) =
    {w | ∃ v : Coord oneDim → ℝ, basisMap (0,v) = w}
  action : ∀ v, A.mulVec (basisMap v) =
    basisMap (starBlock.mulVec v.1, oneBlock.mulVec v.2)

/-- Equality with starBlock diamond B in the specified endpoint basis, pp.4,23. -/
def InEndpointSplitting {n : ℕ} {A : GroupedRealMatrix n} (D : EndpointSplitting A)
    (C : GroupedRealMatrix n) (B : GroupedRealMatrix D.oneDim) : Prop :=
  ∀ v, C.mulVec (D.basisMap v) = D.basisMap (D.starBlock.mulVec v.1, B.mulVec v.2)

/-- Both hyperbolic targets are diag(exp(-1) I, exp(1) I), PDF pp.4,23. -/
def hyperbolicTarget (m : ℕ) : GroupedRealMatrix m :=
  Matrix.fromBlocks (Real.exp (-1) • 1) 0 0 (Real.exp 1 • 1)

/-- Every complex eigenvalue is real and strictly positive, pp.4,23.
This is vacuous, correctly, on a zero-dimensional block. -/
def HasPositiveRealSpectrum {m : ℕ} (A : GroupedRealMatrix m) : Prop :=
  ∀ z ∈ eigenvalues A, z.im = 0 ∧ 0 < z.re

/-- All four prolongation clauses of Theorems 3 and 28, PDF pp.4,23.
The choices of W sign at the two ends are independent. -/
def IsProlongation {n : ℕ} (p e : ℝ → GroupedRealMatrix n)
    (D0 : EndpointSplitting (p 0)) (D1 : EndpointSplitting (p 1)) : Prop :=
  ContinuousOn e (Set.Icc (-1 : ℝ) 2) ∧
  (∀ t ∈ Set.Icc (-1 : ℝ) 2, IsSymplectic (e t)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, e t = p t) ∧
  InEndpointSplitting D0 (e (-1/2)) (hyperbolicTarget D0.oneDim) ∧
  (∃ phi : ℝ → GroupedRealMatrix D0.oneDim,
    ContinuousOn phi (Set.Icc (-1/2 : ℝ) 0) ∧
    ∀ t ∈ Set.Icc (-1/2 : ℝ) 0,
      InEndpointSplitting D0 (e t) (phi t) ∧ IsSymplectic (phi t) ∧
        HasPositiveRealSpectrum (phi t)) ∧
  InEndpointSplitting D1 (e (3/2)) (hyperbolicTarget D1.oneDim) ∧
  (∃ phi : ℝ → GroupedRealMatrix D1.oneDim,
    ContinuousOn phi (Set.Icc (1 : ℝ) (3/2)) ∧
    ∀ t ∈ Set.Icc (1 : ℝ) (3/2),
      InEndpointSplitting D1 (e t) (phi t) ∧ IsSymplectic (phi t) ∧
        HasPositiveRealSpectrum (phi t)) ∧
  (e (-1) = wPlus n ∨ e (-1) = wMinus n) ∧
  (e 2 = wPlus n ∨ e 2 = wMinus n) ∧
  (∀ t ∈ Set.Icc (-1 : ℝ) (-1/2), (e t-1).det ≠ 0) ∧
  (∀ t ∈ Set.Icc (3/2 : ℝ) 2, (e t-1).det ≠ 0)

/-- Degree on [-1,2] is computed on the whole translated interval [0,3], pp.4,23. -/
def prolongationDegree {n : ℕ} (r : GroupedRealMatrix n → ℂ)
    (e : ℝ → GroupedRealMatrix n) : ℤ :=
  winding (fun t => r (e (t-1))^2) 3

/-- Jordan diagonal sanity in the first plane, p.17. -/
example : jordanBlock (-1) 1 0 0 = -1 := by simp [jordanBlock]

/-- The real shift at lambda=1 is the existing fixed-space kernel operator, pp.4,17. -/
example {n : ℕ} (A : GroupedRealMatrix n) :
    realShift A 1 = Matrix.toLin' (A-1) := by simp [realShift]

/-- Zero vectors contribute zero to the endpoint form, p.17. -/
example {n : ℕ} (A : GroupedRealMatrix n) (lambda : ℤ) (k : ℕ)
    (w : Coord n → ℝ) : endpointForm A lambda k 0 w = 0 := by
  simp [endpointForm, omegaR]

/-- Endpoint splitting uses the original matrix when its original 1-block is inserted. -/
example {n : ℕ} {A : GroupedRealMatrix n} (D : EndpointSplitting A) :
    InEndpointSplitting D A D.oneBlock := D.action

/-- Block action sends the zero vector to zero, p.17. -/
example {b : ℕ} (lambda : ℤ) (r : Fin b → ℕ) (d : Fin b → ℤ) :
    normalAction lambda r d 0 = 0 := by
  funext ji
  simp [normalAction, Matrix.mulVec, dotProduct]

/-- Direct-sum symplectic form vanishes on the zero second vector, p.17. -/
example {b : ℕ} (r : Fin b → ℕ) (v : NormalCoord r → ℝ) : normalOmega r v 0 = 0 := by
  simp [normalOmega, omegaR]

/-- The empty ambient space has an empty endpoint signature sum, p.23. -/
example (A : GroupedRealMatrix 0) (lambda : ℤ) : endpointSignatureSum A lambda = 0 := by
  simp [endpointSignatureSum]

/-- The first hyperbolic x coordinate has exp(-1), pp.4,23. -/
example : hyperbolicTarget 1 (Sum.inl 0) (Sum.inl 0) = Real.exp (-1) := by
  simp [hyperbolicTarget]

/-- The prolongation retains the initial endpoint of the original path, pp.4,23. -/
example {n : ℕ} {p e : ℝ → GroupedRealMatrix n}
    {D0 : EndpointSplitting (p 0)} {D1 : EndpointSplitting (p 1)}
    (he : IsProlongation p e D0 D1) : e 0 = p 0 :=
  he.2.2.1 0 (by norm_num)

end QAlgorithms.Papers.Independent.Intake100.P25


