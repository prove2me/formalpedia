-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39
-- name    : QAlgorithms_Papers_Independent_Intake100_P39
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:01:12.221254+00:00
-- url     : https://prove2.me/theorems/993f483a-cf7d-404f-a186-26c4f3b18ff7
-- title:
--   Definitions for Normal Forms for Symplectic Matrices
-- statement:
--   The objects the formalized statements of *Normal Forms for Symplectic Matrices* (arXiv:1307.2403) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RVec`
--   - `CVec`
--   - `realEmbed`: PDF p.2: actual inclusion of real vectors into the complexification.
--   - `realShift`: PDF p.17: shifted real endomorphism.
--   - `eigenOrbit`: PDF p.3, (1): a SET of eigenvalues, so coincidences are never repeated.
--   - `primaryComplex`: PDF p.7, (7): the constructed primary space over C; joins deduplicate.
--   - `primaryReal`: PDF pp.7–8: the REAL primary space, pulled back from (7).
--   - `cyclicC`: PDF pp.11–25: cyclic subspace constructed from the vector, not an input space.
--   - `cyclicR`
--   - `realPart`: Real form of a conjugation-stable complex space, PDF pp.12,20,25.
--   - `VectorHeight`: PDF p.9: height of ONE vector, including nonzeroness.
--   - `OrthogonalC`: PDF p.7: symmetric orthogonality in the bilinear complex form.
--   - `chainT`: PDF p.10, (15): conjugate lambda and conjugate vector occur in slot two.
--   - `realQ`: PDF p.17, (21): real kernel-form expression; its domain is ker N^(2k).
--   - `unitQ`: PDF p.26, Definition 16: complex-linear first and conjugate-linear second.
--   - `definiteIndex`: Finite dimensional positive index; dimension is over the specified field. PDF pp.17,26. The finite range contains every possible subspace dimension.
--   - `realInertia`: Positive and negative inertia; zero eigenvalues do not contribute.
--   - `unitInertia`: PDF p.26: COMPLEX dimensions of Hermitian positive/negative subspaces.
--   - `rankSignature`
--   - `jordan`: PDF pp.4,13: elementary upper Jordan matrix with superdiagonal ONE.
--   - `lastDiagonal`: PDF p.3: D(m,s), with only the LAST diagonal entry nonzero.
--   - `realMultiplicationBlock`: PDF p.13, (20): R(z)=[[Re z,-Im z],[Im z,Re z]].
--   - `realJordan`: PDF p.13, (20): JR(z,2k), indexed by interleaved two-coordinate blocks.
--   - `signedBlock`: PDF pp.4,17: signed Jordan symplectic block. Ordinary transpose.
--   - `offComplexBlock`: PDF pp.4,14: nonreal off-circle real block; argument is bar(lambda).
--   - `vColumns`: PDF p.26, (31): the stacked two-column matrix V, top exponent k.
--   - `uColumns`: PDF p.26, (32): U=V R(lambda).
--   - `unitEvenBlock`: PDF pp.20,25: the 4k by 4k odd-height block (k>=1 at use).
--   - `unitOddBlock`: PDF p.25: all four sectors of the (4k+2)-dimensional even-height block. For k=0 this is [[Re z,s Im z],[-s Im z,Re z]].
--   - `unitBlock`: PDF pp.25–26: one sign and one positive complex chain length m per block.
--   - `HalfIndex`: PDF p.2: variable-length sum with ALL e-coordinates before ALL f-coordinates.
--   - `SymplecticSumIndex`
--   - `sumSector`: PDF p.2: one sector of the dependent symplectic direct sum.
--   - `symplecticBlockSum`: PDF p.2: the actual symplectic direct sum, including the empty family.
--   - `groupedOmega`: PDF p.1: standard bilinear symplectic pairing for arbitrary grouped indices.
--   - `RepresentsR`: PDF pp.1,7: an ACTUAL symplectic basis of W, representing the ambient A. The matrix action equation also asserts invariance of W.
--   - `BasisRepresentsC`: PDF pp.3,20,24: a specific complex symplectic basis and its action matrix.
--   - `RepresentsC`: PDF p.3: complex version, with ordinary bilinear symplectic basis.
--   - `RealNormal`: PDF p.17: one real signed-block family with its genuine primary-space basis.
--   - `UnitNormal`: PDF pp.25–26: both unit-circle block families, encoded by parity of m.
--   - `OffNormal`: PDF pp.13–14: off-circle Jordan decomposition, with positive ordered lengths.
--   - `kernelDim`: Kernel dimensions are computed from A, PDF pp.6,18,26.
--   - `SameInvariants`: PDF p.6: redundant all-eigenvalue data, equivalent to consistent orbit representatives.
--   - `SymplecticallyConjugate`: PDF p.6: symplectic conjugacy in the SAME ambient coordinates.
--   - `SameBlocks`: PDF pp.18,26: equality of unordered signed block data is literal permutation.
--   - `PrimaryDecomposition`: PDF p.7: real-primary conclusions including complexification and direct sum.
--   - `RealKernelCount`: PDF pp.5,17: exact eigenspace count, including TWO for every zero sign.
--   - `RealSignCounts`: PDF pp.5,17: the positive AND negative sign counts at every block size.
--   - `UnitSignCounts`: PDF pp.6,26: each real 2m block contributes its sign to Q_m.
--   - `SameRealData`: PDF p.18: primary invariants, with no assumption that the forms are nondegenerate.
--   - `SameUnitData`: PDF p.26: the chosen eigenvalue z is held FIXED in comparisons.
--   - `OffClassification`: PDF pp.4,13–14: existence, maximal chain length, and determination by kernel data.
--   - `RealClassification`: PDF pp.5,17–18: all real-primary clauses of Theorem 1, including uniqueness.
--   - `UnitClassification`: PDF pp.5–6,25–26: both families, eigenspace count, inertia, and uniqueness.
--   - `sectorDiagonal`: PDF pp.20,24: ordinary block diagonal, used inside a symplectic sector.
--   - `complexEvenBlock`: PDF p.20, (23): the paired COMPLEX signed block.
--   - `rectangularS`: PDF p.24, (28): rectangular S; all entries, including the penultimate one.
--   - `complexOddBlock`: PDF p.24, (27): the unequal-sector COMPLEX signed block; ordinary transpose.
--   - `PairedEvenRepresentation`: PDF pp.19–20: conjugate-paired basis in (23), retaining the real structure.
--   - `PairedOddRepresentation`: PDF pp.23–24: conjugate-paired basis in (27); the central pair has factor -i*s.
--   - `CatalogueBlock`: PDF p.3: the three explicitly displayed catalogue families.
--   - `catalogueSize`
--   - `catalogueMatrix`
--   - `CatalogueValid`: PDF pp.3–6: the catalogue is restricted to the source's spectral regimes.
--   - `catalogueSign`: PDF p.3: the integer carried by a catalogue block.
--   - `signCharacteristic`: PDF p.3: sign characteristic is the multiset of NONZERO signs.
--   - `symplecticDiamond`: PDF p.2: fixed two-summand coordinate permutation.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, https://arxiv.org/abs/1307.2403v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

/-! Jean Gutt, Normal Forms for Symplectic Matrices, arXiv:1307.2403v2.
The ambient space is expressed in an arbitrary symplectic coordinate system;
this models every finite dimensional real symplectic space, including dimension zero.
The symplectic substrate reuses the pinned accepted library; new interfaces stay paper local.
Complex omega is BILINEAR.
Compilation is pending the batch mechanical check. -/

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

abbrev RVec (n : ℕ) := Coord n → ℝ

abbrev CVec (n : ℕ) := Coord n → ℂ

/-- PDF p.2: actual inclusion of real vectors into the complexification. -/
def realEmbed (n : ℕ) : RVec n →ₗ[ℝ] CVec n where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

/-- PDF p.17: shifted real endomorphism. -/
def realShift {n : ℕ} (A : GroupedRealMatrix n) (a : ℝ) : Module.End ℝ (RVec n) :=
  Matrix.toLin' A - a • 1

/-- PDF p.3, (1): a SET of eigenvalues, so coincidences are never repeated. -/
def eigenOrbit (z : ℂ) : Finset ℂ := {z, z⁻¹, star z, (star z)⁻¹}

/-- PDF p.7, (7): the constructed primary space over C; joins deduplicate. -/
def primaryComplex {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Submodule ℂ (CVec n) :=
  ⨆ t ∈ eigenOrbit z, generalizedSpace A t

/-- PDF pp.7–8: the REAL primary space, pulled back from (7). -/
def primaryReal {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Submodule ℝ (RVec n) :=
  ((primaryComplex A z).restrictScalars ℝ).comap (realEmbed n)

/-- PDF pp.11–25: cyclic subspace constructed from the vector, not an input space. -/
def cyclicC {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : CVec n) : Submodule ℂ (CVec n) :=
  Submodule.span ℂ (Set.range fun j : ℕ => (shifted A z ^ j) v)

def cyclicR {n : ℕ} (A : GroupedRealMatrix n) (a : ℝ) (v : RVec n) : Submodule ℝ (RVec n) :=
  Submodule.span ℝ (Set.range fun j : ℕ => (realShift A a ^ j) v)

/-- Real form of a conjugation-stable complex space, PDF pp.12,20,25. -/
def realPart {n : ℕ} (W : Submodule ℂ (CVec n)) : Submodule ℝ (RVec n) :=
  (W.restrictScalars ℝ).comap (realEmbed n)

/-- PDF p.9: height of ONE vector, including nonzeroness. -/
def VectorHeight {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : CVec n) (p : ℕ) : Prop :=
  (shifted A z ^ p) v ≠ 0 ∧ (shifted A z ^ (p + 1)) v = 0

/-- PDF p.7: symmetric orthogonality in the bilinear complex form. -/
def OrthogonalC {n : ℕ} (W : Submodule ℂ (CVec n)) (v : CVec n) : Prop :=
  ∀ w ∈ W, omegaC v w = 0

/-- PDF p.10, (15): conjugate lambda and conjugate vector occur in slot two. -/
def chainT {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : CVec n) (i j : ℕ) : ℂ :=
  (z ^ i * (star z) ^ j)⁻¹ *
    omegaC ((shifted A z ^ i) v) ((shifted A (star z) ^ j) (star v))

/-- PDF p.17, (21): real kernel-form expression; its domain is ker N^(2k). -/
def realQ {n : ℕ} (A : GroupedRealMatrix n) (a : ℝ) (k : ℕ) (v w : RVec n) : ℝ :=
  a * omegaR ((realShift A a ^ k) v) ((realShift A a ^ (k - 1)) w)

/-- PDF p.26, Definition 16: complex-linear first and conjugate-linear second. -/
def unitQ {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (m : ℕ) (v w : CVec n) : ℂ :=
  if m % 2 = 0 then
    z⁻¹ * omegaC ((shifted A z ^ (m / 2)) v)
      ((shifted A (star z) ^ (m / 2 - 1)) (star w))
  else Complex.I * omegaC ((shifted A z ^ (m / 2)) v)
      ((shifted A (star z) ^ (m / 2)) (star w))

/-- Finite dimensional positive index; dimension is over the specified field.
PDF pp.17,26. The finite range contains every possible subspace dimension. -/
def definiteIndex (K : Type*) [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (W : Submodule K E) (q : E → ℝ) : ℕ :=
  ((Finset.range (Module.finrank K E + 1)).filter fun d =>
    ∃ L : Submodule K E, L ≤ W ∧ Module.finrank K L = d ∧
      ∀ v ∈ L, v ≠ 0 → 0 < q v).sup id

/-- Positive and negative inertia; zero eigenvalues do not contribute. -/
def realInertia {n : ℕ} (A : GroupedRealMatrix n) (a : ℝ) (k : ℕ) : ℕ × ℕ :=
  let W := LinearMap.ker (realShift A a ^ (2 * k))
  (definiteIndex ℝ W (fun v => realQ A a k v v),
   definiteIndex ℝ W (fun v => -realQ A a k v v))

/-- PDF p.26: COMPLEX dimensions of Hermitian positive/negative subspaces. -/
def unitInertia {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (m : ℕ) : ℕ × ℕ :=
  let W := LinearMap.ker (shifted A z ^ m)
  (definiteIndex ℂ W (fun v => (unitQ A z m v v).re),
   definiteIndex ℂ W (fun v => -(unitQ A z m v v).re))

def rankSignature (pq : ℕ × ℕ) : ℕ × ℤ := (pq.1 + pq.2, (pq.1 : ℤ) - pq.2)

/-- PDF pp.4,13: elementary upper Jordan matrix with superdiagonal ONE. -/
def jordan {K : Type*} [Field K] (z : K) (m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun i j => if i = j then z else if i.val + 1 = j.val then 1 else 0

/-- PDF p.3: D(m,s), with only the LAST diagonal entry nonzero. -/
def lastDiagonal {K : Type*} [Field K] (m : ℕ) (s : K) : Matrix (Fin m) (Fin m) K :=
  Matrix.diagonal fun i => if i.val + 1 = m then s else 0

/-- PDF p.13, (20): R(z)=[[Re z,-Im z],[Im z,Re z]]. -/
def realMultiplicationBlock (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re, -z.im; z.im, z.re]

/-- PDF p.13, (20): JR(z,2k), indexed by interleaved two-coordinate blocks. -/
def realJordan (z : ℂ) (k : ℕ) : Matrix (Fin (2 * k)) (Fin (2 * k)) ℝ :=
  fun i j => if i.val / 2 = j.val / 2 then
    realMultiplicationBlock z ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩ ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩
  else if i.val / 2 + 1 = j.val / 2 ∧ i.val % 2 = j.val % 2 then 1 else 0

/-- PDF pp.4,17: signed Jordan symplectic block. Ordinary transpose. -/
def signedBlock {K : Type*} [Field K] [DecidableEq K] (z : K) (m : ℕ) (s : K) :
    Matrix (Coord m) (Coord m) K :=
  Matrix.fromBlocks (jordan z m)⁻¹ ((jordan z m)⁻¹ * lastDiagonal m s) 0 (jordan z m).transpose

/-- PDF pp.4,14: nonreal off-circle real block; argument is bar(lambda). -/
def offComplexBlock (z : ℂ) (m : ℕ) : GroupedRealMatrix (2 * m) :=
  Matrix.fromBlocks (realJordan (star z) m)⁻¹ 0 0 (realJordan (star z) m).transpose

/-- PDF p.26, (31): the stacked two-column matrix V, top exponent k. -/
def vColumns (z : ℂ) (k : ℕ) : Matrix (Fin (2 * k)) (Fin 2) ℝ :=
  fun i j => (-1 : ℝ) ^ (k - i.val / 2 - 1) *
    realMultiplicationBlock (z ^ (k - i.val / 2)) ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩ j

/-- PDF p.26, (32): U=V R(lambda). -/
def uColumns (z : ℂ) (k : ℕ) : Matrix (Fin (2 * k)) (Fin 2) ℝ :=
  vColumns z k * realMultiplicationBlock z

/-- PDF pp.20,25: the 4k by 4k odd-height block (k>=1 at use). -/
def unitEvenBlock (z : ℂ) (k : ℕ) (s : ℝ) : GroupedRealMatrix (2 * k) :=
  Matrix.fromBlocks (realJordan (star z) k)⁻¹
    (fun i j => if j.val + 2 ≥ 2 * k then
      s * vColumns z k i ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩ else 0)
    0 (realJordan (star z) k).transpose

/-- PDF p.25: all four sectors of the (4k+2)-dimensional even-height block.
For k=0 this is [[Re z,s Im z],[-s Im z,Re z]]. -/
def unitOddBlock (z : ℂ) (k : ℕ) (s : ℝ) : GroupedRealMatrix (2 * k + 1) :=
  let J := realJordan (star z) k
  let V := vColumns z k
  let U := uColumns z k
  Matrix.fromBlocks
    (fun i j => if hi : i.val < 2 * k then
      if hj : j.val < 2 * k then J⁻¹ ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else s * U ⟨i.val, hi⟩ 1
      else if j.val < 2 * k then 0 else z.re)
    (fun i j => if hi : i.val < 2 * k then
      if j.val < 2 * k then
        if j.val + 2 ≥ 2 * k then
          if j.val % 2 = 0 then s / 2 * V ⟨i.val, hi⟩ 1
          else -s / 2 * V ⟨i.val, hi⟩ 0
        else 0
      else U ⟨i.val, hi⟩ 0
      else if j.val < 2 * k then (if j.val + 2 = 2 * k then 1 else 0)
      else s * z.im)
    (fun i j => if i.val = 2 * k ∧ j.val = 2 * k then -s * z.im else 0)
    (fun i j => if hi : i.val < 2 * k then
      if hj : j.val < 2 * k then J.transpose ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if j.val < 2 * k then (if j.val + 1 = 2 * k then -s else 0)
      else z.re)

/-- PDF pp.25–26: one sign and one positive complex chain length m per block. -/
def unitBlock (z : ℂ) (m : ℕ) (s : ℝ) : GroupedRealMatrix m :=
  if h : m % 2 = 0 then
    Matrix.reindex (Equiv.sumCongr (finCongr (by omega : 2 * (m / 2) = m))
      (finCongr (by omega : 2 * (m / 2) = m)))
      (Equiv.sumCongr (finCongr (by omega : 2 * (m / 2) = m))
      (finCongr (by omega : 2 * (m / 2) = m))) (unitEvenBlock z (m / 2) s)
  else
    Matrix.reindex (Equiv.sumCongr (finCongr (by omega : 2 * (m / 2) + 1 = m))
      (finCongr (by omega : 2 * (m / 2) + 1 = m)))
      (Equiv.sumCongr (finCongr (by omega : 2 * (m / 2) + 1 = m))
      (finCongr (by omega : 2 * (m / 2) + 1 = m))) (unitOddBlock z (m / 2) s)

/-- PDF p.2: variable-length sum with ALL e-coordinates before ALL f-coordinates. -/
abbrev HalfIndex {L : ℕ} (r : Fin L → ℕ) := (j : Fin L) × Fin (r j)

abbrev SymplecticSumIndex {L : ℕ} (r : Fin L → ℕ) := HalfIndex r ⊕ HalfIndex r

/-- PDF p.2: one sector of the dependent symplectic direct sum. -/
def sumSector {K : Type*} [Zero K] {L : ℕ} (r : Fin L → ℕ)
    (M : (j : Fin L) → Matrix (Coord (r j)) (Coord (r j)) K)
    (a b : Bool) (i j : HalfIndex r) : K :=
  if h : i.1 = j.1 then
    M i.1 (if a then Sum.inr i.2 else Sum.inl i.2)
      (if b then Sum.inr (Fin.cast (congrArg r h.symm) j.2)
      else Sum.inl (Fin.cast (congrArg r h.symm) j.2))
  else 0

/-- PDF p.2: the actual symplectic direct sum, including the empty family. -/
def symplecticBlockSum {K : Type*} [Zero K] {L : ℕ} (r : Fin L → ℕ)
    (M : (j : Fin L) → Matrix (Coord (r j)) (Coord (r j)) K) :
    Matrix (SymplecticSumIndex r) (SymplecticSumIndex r) K :=
  Matrix.fromBlocks (sumSector r M false false) (sumSector r M false true)
    (sumSector r M true false) (sumSector r M true true)

/-- PDF p.1: standard bilinear symplectic pairing for arbitrary grouped indices. -/
def groupedOmega {K : Type*} [CommRing K] {H : Type*} [Fintype H]
    (v w : H ⊕ H → K) : K :=
  ∑ i, (v (Sum.inl i) * w (Sum.inr i) - v (Sum.inr i) * w (Sum.inl i))

/-- PDF pp.1,7: an ACTUAL symplectic basis of W, representing the ambient A.
The matrix action equation also asserts invariance of W. -/
def RepresentsR {n : ℕ} (A : GroupedRealMatrix n) (W : Submodule ℝ (RVec n))
    {H : Type*} [Fintype H] [DecidableEq H]
    (M : Matrix (H ⊕ H) (H ⊕ H) ℝ) : Prop :=
  ∃ b : Module.Basis (H ⊕ H) ℝ W,
    (∀ i j, omegaR (b i).val (b j).val =
      groupedOmega (Pi.single i 1) (Pi.single j 1)) ∧
    ∀ j, A.mulVec (b j).val = ∑ i, M i j • (b i).val

/-- PDF pp.3,20,24: a specific complex symplectic basis and its action matrix. -/
def BasisRepresentsC {n : ℕ} (A : GroupedRealMatrix n) (W : Submodule ℂ (CVec n))
    {H : Type*} [Fintype H] [DecidableEq H] (b : Module.Basis (H ⊕ H) ℂ W)
    (M : Matrix (H ⊕ H) (H ⊕ H) ℂ) : Prop :=
  (∀ i j, omegaC (b i).val (b j).val =
    groupedOmega (Pi.single i 1) (Pi.single j 1)) ∧
  ∀ j, (complexify A).mulVec (b j).val = ∑ i, M i j • (b i).val

/-- PDF p.3: complex version, with ordinary bilinear symplectic basis. -/
def RepresentsC {n : ℕ} (A : GroupedRealMatrix n) (W : Submodule ℂ (CVec n))
    {H : Type*} [Fintype H] [DecidableEq H]
    (M : Matrix (H ⊕ H) (H ⊕ H) ℂ) : Prop :=
  ∃ b : Module.Basis (H ⊕ H) ℂ W, BasisRepresentsC A W b M

/-- PDF p.17: one real signed-block family with its genuine primary-space basis. -/
def RealNormal {n L : ℕ} (A : GroupedRealMatrix n) (a : ℝ) (r : Fin L → ℕ) (s : Fin L → ℤ) : Prop :=
  (∀ j, 0 < r j ∧ (s j = 0 ∨ s j = 1 ∨ s j = -1) ∧
    (s j = 0 → Odd (r j))) ∧
  RepresentsR A (primaryReal A (a : ℂ)) (symplecticBlockSum r fun j => signedBlock a (r j) (s j : ℝ))

/-- PDF pp.25–26: both unit-circle block families, encoded by parity of m. -/
def UnitNormal {n L : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (m : Fin L → ℕ) (s : Fin L → ℤ) : Prop :=
  (∀ j, 0 < m j ∧ (s j = 1 ∨ s j = -1)) ∧
  RepresentsR A (primaryReal A z) (symplecticBlockSum m fun j => unitBlock z (m j) (s j : ℝ))

/-- PDF pp.13–14: off-circle Jordan decomposition, with positive ordered lengths. -/
def OffNormal {n L : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (q : Fin L → ℕ) : Prop :=
  (∀ j, 0 < q j) ∧ Antitone q ∧
  if z.im = 0 then
    RepresentsR A (primaryReal A z) (symplecticBlockSum q fun j => signedBlock z.re (q j) 0)
  else RepresentsR A (primaryReal A z)
    (symplecticBlockSum (fun j => 2 * q j) fun j => offComplexBlock z (q j))

/-- Kernel dimensions are computed from A, PDF pp.6,18,26. -/
def kernelDim {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (r : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (shifted A z ^ r))

/-- PDF p.6: redundant all-eigenvalue data, equivalent to consistent orbit representatives. -/
def SameInvariants {n : ℕ} (A B : GroupedRealMatrix n) : Prop :=
  (∀ z, IsEigenvalue A z ↔ IsEigenvalue B z) ∧
  (∀ z, ∀ r ≥ 1, kernelDim A z r = kernelDim B z r) ∧
  (∀ a : ℝ, (a = 1 ∨ a = -1) → ∀ k ≥ 1,
    rankSignature (realInertia A a k) = rankSignature (realInertia B a k)) ∧
  (∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → z ≠ -1 → ∀ m ≥ 1,
    rankSignature (unitInertia A z m) = rankSignature (unitInertia B z m))

/-- PDF p.6: symplectic conjugacy in the SAME ambient coordinates. -/
def SymplecticallyConjugate {n : ℕ} (A B : GroupedRealMatrix n) : Prop :=
  ∃ P : GroupedRealMatrix n, IsSymplectic P ∧ B * P = P * A

/-- PDF pp.18,26: equality of unordered signed block data is literal permutation. -/
def SameBlocks {L K : ℕ} (r : Fin L → ℕ) (s : Fin L → ℤ)
    (t : Fin K → ℕ) (u : Fin K → ℤ) : Prop :=
  ∃ e : Fin L ≃ Fin K, ∀ j, r j = t (e j) ∧ s j = u (e j)

/-- PDF p.7: real-primary conclusions including complexification and direct sum. -/
def PrimaryDecomposition {n : ℕ} (A : GroupedRealMatrix n) : Prop :=
  (∀ z, Submodule.span ℂ (realEmbed n '' (primaryReal A z : Set (RVec n))) =
    primaryComplex A z) ∧
  (∀ z, ∀ v ∈ primaryReal A z, A.mulVec v ∈ primaryReal A z) ∧
  (∀ z, ∀ v ∈ primaryReal A z,
    (∀ w ∈ primaryReal A z, omegaR v w = 0) → v = 0) ∧
  ∃ S : Finset ℂ,
    (∀ z ∈ S, IsEigenvalue A z) ∧
    (∀ z, IsEigenvalue A z → ∃ t ∈ S, z ∈ eigenOrbit t) ∧
    (∀ z ∈ S, ∀ t ∈ S, z ≠ t → Disjoint (eigenOrbit z) (eigenOrbit t)) ∧
    (⨆ z ∈ S, primaryReal A z) = ⊤ ∧
    (∀ z ∈ S, Disjoint (primaryReal A z) (⨆ t ∈ S.erase z, primaryReal A t)) ∧
    ∀ z ∈ S, ∀ t ∈ S, z ≠ t → ∀ v ∈ primaryReal A z,
      ∀ w ∈ primaryReal A t, omegaR v w = 0

/-- Sanity: the Jordan convention has superdiagonal +1, PDF p.13. -/
example (a : ℝ) : jordan a 2 0 1 = 1 := by simp [jordan]

/-- Sanity: the two-dimensional signed block is [[1,s],[0,1]], PDF p.17. -/
example (s : ℝ) : lastDiagonal 1 s 0 0 = s := by simp [lastDiagonal]

/-- Sanity: the realification convention has upper-right -Im z, PDF p.13. -/
example (z : ℂ) : realMultiplicationBlock z 0 1 = -z.im := rfl

/-- Sanity: odd-size unit block at k=0 is the signed planar rotation, PDF p.25. -/
example (z : ℂ) (s : ℝ) :
    unitOddBlock z 0 s (Sum.inl 0) (Sum.inr 0) = s * z.im := by
  simp [unitOddBlock, Matrix.fromBlocks]

/-- PDF pp.5,17: exact eigenspace count, including TWO for every zero sign. -/
def RealKernelCount {n L : ℕ} (A : GroupedRealMatrix n) (a : ℝ) (s : Fin L → ℤ) : Prop :=
  kernelDim A (a : ℂ) 1 =
    2 * (Finset.univ.filter fun j => s j = 0).card +
      (Finset.univ.filter fun j => s j ≠ 0).card

/-- PDF pp.5,17: the positive AND negative sign counts at every block size. -/
def RealSignCounts {n L : ℕ} (A : GroupedRealMatrix n) (a : ℝ)
    (r : Fin L → ℕ) (s : Fin L → ℤ) : Prop :=
  ∀ k ≥ 1, (realInertia A a k).1 =
    (Finset.univ.filter fun j => r j = k ∧ s j = 1).card ∧
    (realInertia A a k).2 =
    (Finset.univ.filter fun j => r j = k ∧ s j = -1).card

/-- PDF pp.6,26: each real 2m block contributes its sign to Q_m. -/
def UnitSignCounts {n L : ℕ} (A : GroupedRealMatrix n) (z : ℂ)
    (m : Fin L → ℕ) (s : Fin L → ℤ) : Prop :=
  ∀ t ≥ 1, (unitInertia A z t).1 =
    (Finset.univ.filter fun j => m j = t ∧ s j = 1).card ∧
    (unitInertia A z t).2 =
    (Finset.univ.filter fun j => m j = t ∧ s j = -1).card

/-- PDF p.18: primary invariants, with no assumption that the forms are nondegenerate. -/
def SameRealData {n N : ℕ} (A : GroupedRealMatrix n) (B : GroupedRealMatrix N) (a : ℝ) : Prop :=
  (∀ r ≥ 1, kernelDim A (a : ℂ) r = kernelDim B (a : ℂ) r) ∧
  ∀ k ≥ 1, rankSignature (realInertia A a k) = rankSignature (realInertia B a k)

/-- PDF p.26: the chosen eigenvalue z is held FIXED in comparisons. -/
def SameUnitData {n N : ℕ} (A : GroupedRealMatrix n) (B : GroupedRealMatrix N) (z : ℂ) : Prop :=
  (∀ r ≥ 1, kernelDim A z r = kernelDim B z r) ∧
  ∀ m ≥ 1, rankSignature (unitInertia A z m) = rankSignature (unitInertia B z m)

/-- PDF pp.4,13–14: existence, maximal chain length, and determination by kernel data. -/
def OffClassification {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Prop :=
  ∃ q : Fin (kernelDim A z 1) → ℕ,
    OffNormal A z q ∧
    (∀ p, HasNilpotentHeight A z p → Finset.univ.sup q = p + 1) ∧
    ∀ (N K : ℕ) (B : GroupedRealMatrix N) (t : Fin K → ℕ),
      IsSymplectic B → OffNormal B z t →
      (∀ r ≥ 1, kernelDim A z r = kernelDim B z r) →
      SameBlocks q (fun _ => 0) t (fun _ => 0)

/-- PDF pp.5,17–18: all real-primary clauses of Theorem 1, including uniqueness. -/
def RealClassification {n : ℕ} (A : GroupedRealMatrix n) (a : ℝ) : Prop :=
  ∃ (L : ℕ) (r : Fin L → ℕ) (s : Fin L → ℤ),
    RealNormal A a r s ∧ RealKernelCount A a s ∧ RealSignCounts A a r s ∧
    ∀ (N K : ℕ) (B : GroupedRealMatrix N) (t : Fin K → ℕ) (u : Fin K → ℤ),
      IsSymplectic B → RealNormal B a t u → SameRealData A B a → SameBlocks r s t u

/-- PDF pp.5–6,25–26: both families, eigenspace count, inertia, and uniqueness. -/
def UnitClassification {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Prop :=
  ∃ (L : ℕ) (m : Fin L → ℕ) (s : Fin L → ℤ),
    UnitNormal A z m s ∧ kernelDim A z 1 = L ∧ UnitSignCounts A z m s ∧
    ∀ (N K : ℕ) (B : GroupedRealMatrix N) (t : Fin K → ℕ) (u : Fin K → ℤ),
      IsSymplectic B → UnitNormal B z t u → SameUnitData A B z → SameBlocks m s t u

/-- PDF pp.20,24: ordinary block diagonal, used inside a symplectic sector. -/
def sectorDiagonal {K : Type*} [Zero K] {a b : ℕ}
    (P : Matrix (Fin a) (Fin a) K) (Q : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := Matrix.fromBlocks P 0 0 Q

/-- PDF p.20, (23): the paired COMPLEX signed block. -/
def complexEvenBlock (z : ℂ) (k : ℕ) (s : ℂ) :
    Matrix ((Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k))
      ((Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) ℂ :=
  let P := sectorDiagonal (jordan (star z) k) (jordan z k)
  let D := lastDiagonal k s
  Matrix.fromBlocks P⁻¹ (P⁻¹ * Matrix.fromBlocks 0 D D 0) 0 P.transpose

/-- PDF p.24, (28): rectangular S; all entries, including the penultimate one. -/
def rectangularS (z : ℂ) (k : ℕ) (s : ℂ) : Matrix (Fin k) (Fin (k + 1)) ℂ :=
  fun i j => if i.val + 1 = k then
    if j.val = k then z * Complex.I * s
    else if j.val + 1 = k then Complex.I * s / 2 else 0
  else 0

/-- PDF p.24, (27): the unequal-sector COMPLEX signed block; ordinary transpose. -/
def complexOddBlock (z : ℂ) (k : ℕ) (s : ℂ) :
    Matrix ((Fin k ⊕ Fin (k + 1)) ⊕ (Fin k ⊕ Fin (k + 1)))
      ((Fin k ⊕ Fin (k + 1)) ⊕ (Fin k ⊕ Fin (k + 1))) ℂ :=
  let P := sectorDiagonal (jordan (star z) k) (jordan z (k + 1))
  let S := rectangularS z k s
  Matrix.fromBlocks P⁻¹ (P⁻¹ * Matrix.fromBlocks 0 S S.transpose 0) 0 P.transpose

/-- PDF pp.19–20: conjugate-paired basis in (23), retaining the real structure. -/
def PairedEvenRepresentation {n : ℕ} (A : GroupedRealMatrix n) (W : Submodule ℂ (CVec n))
    (z : ℂ) (k : ℕ) (s : ℤ) : Prop :=
  ∃ b : Module.Basis ((Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) ℂ W,
    BasisRepresentsC A W b (complexEvenBlock z k (s : ℂ)) ∧
    (∀ i, (b (Sum.inl (Sum.inr i))).val = star (b (Sum.inl (Sum.inl i))).val) ∧
    ∀ i, (b (Sum.inr (Sum.inr i))).val = star (b (Sum.inr (Sum.inl i))).val

/-- PDF pp.23–24: conjugate-paired basis in (27); the central pair has factor -i*s. -/
def PairedOddRepresentation {n : ℕ} (A : GroupedRealMatrix n) (W : Submodule ℂ (CVec n))
    (z : ℂ) (k : ℕ) (s : ℤ) : Prop :=
  ∃ b : Module.Basis ((Fin k ⊕ Fin (k + 1)) ⊕ (Fin k ⊕ Fin (k + 1))) ℂ W,
    BasisRepresentsC A W b (complexOddBlock z k (s : ℂ)) ∧
    (∀ i : Fin k, (b (Sum.inl (Sum.inr i.castSucc))).val =
      star (b (Sum.inl (Sum.inl i))).val) ∧
    (∀ i : Fin k, (b (Sum.inr (Sum.inr i.castSucc))).val =
      star (b (Sum.inr (Sum.inl i))).val) ∧
    (b (Sum.inl (Sum.inr (Fin.last k)))).val =
      (-Complex.I * (s : ℂ)) • star (b (Sum.inr (Sum.inr (Fin.last k)))).val

/-- PDF p.3: the three explicitly displayed catalogue families. -/
inductive CatalogueBlock where
  | single (z : ℂ) (k : ℕ) (s : ℤ)
  | paired (z : ℂ) (k : ℕ) (s : ℤ)
  | unequal (z : ℂ) (k : ℕ) (s : ℤ)

def catalogueSize : CatalogueBlock → ℕ
  | .single _ k _ => k
  | .paired _ k _ => k + k
  | .unequal _ k _ => k + (k + 1)

def catalogueMatrix (c : CatalogueBlock) :
    Matrix (Coord (catalogueSize c)) (Coord (catalogueSize c)) ℂ :=
  match c with
  | .single z k s => signedBlock z k (s : ℂ)
  | .paired z k s => Matrix.reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
      (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) (complexEvenBlock z k (s : ℂ))
  | .unequal z k s => Matrix.reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
      (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) (complexOddBlock z k (s : ℂ))

/-- PDF pp.3–6: the catalogue is restricted to the source's spectral regimes. -/
def CatalogueValid {n : ℕ} (A : GroupedRealMatrix n) : CatalogueBlock → Prop
  | .single z k s => IsEigenvalue A z ∧ 0 < k ∧ z.im = 0 ∧
      ((‖z‖ ≠ 1 ∧ s = 0) ∨
      ((z = 1 ∨ z = -1) ∧ (s = 0 ∨ s = 1 ∨ s = -1) ∧ (s = 0 → Odd k)))
  | .paired z k s => IsEigenvalue A z ∧ 0 < k ∧ z.im ≠ 0 ∧
      ((‖z‖ ≠ 1 ∧ s = 0) ∨ (‖z‖ = 1 ∧ (s = 1 ∨ s = -1)))
  | .unequal z _ s => IsEigenvalue A z ∧ ‖z‖ = 1 ∧ z.im ≠ 0 ∧ (s = 1 ∨ s = -1)

/-- PDF p.3: the integer carried by a catalogue block. -/
def catalogueSign : CatalogueBlock → ℤ
  | .single _ _ s => s
  | .paired _ _ s => s
  | .unequal _ _ s => s

/-- PDF p.3: sign characteristic is the multiset of NONZERO signs. -/
def signCharacteristic {L : ℕ} (c : Fin L → CatalogueBlock) : Multiset ℤ :=
  (((Finset.univ : Finset (Fin L)).val.map fun j => catalogueSign (c j))).filter
    (fun s => s ≠ 0)

/-- PDF p.2: fixed two-summand coordinate permutation. -/
def symplecticDiamond {k l : ℕ} (A : GroupedRealMatrix k) (B : GroupedRealMatrix l) :
    Matrix ((Fin k ⊕ Fin l) ⊕ (Fin k ⊕ Fin l))
      ((Fin k ⊕ Fin l) ⊕ (Fin k ⊕ Fin l)) ℝ :=
  Matrix.fromBlocks
    (sectorDiagonal (A.submatrix Sum.inl Sum.inl) (B.submatrix Sum.inl Sum.inl))
    (sectorDiagonal (A.submatrix Sum.inl Sum.inr) (B.submatrix Sum.inl Sum.inr))
    (sectorDiagonal (A.submatrix Sum.inr Sum.inl) (B.submatrix Sum.inr Sum.inl))
    (sectorDiagonal (A.submatrix Sum.inr Sum.inr) (B.submatrix Sum.inr Sum.inr))

end QAlgorithms.Papers.Independent.Intake100.P39


