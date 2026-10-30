-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15
-- name    : QAlgorithms_Papers_Independent_Extend50_P15
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:53:42.14143+00:00
-- url     : https://prove2.me/theorems/c77934e8-02a6-4af3-9d68-3618964ba1d1
-- title:
--   Definitions for Optimal Universal Quantum Error Correction via Bounded Reference Frames
-- statement:
--   The objects the formalized statements of *Optimal Universal Quantum Error Correction via Bounded Reference Frames* (arXiv:2007.09154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FlaggedRegister`: Erasure output space: a tensor product of local direct sums, retaining every mixed surviving/erased pattern (PDF pp.8,22). `none` is the orthogonal erasure flag.
--   - `IsNormalizedHaar`: Normalized Haar law, with its left and right translation invariance, not Haar volume. The Borel space is fixed above; on this compact group this specifies the unique probability Haar measure (PDF pp.3,10).
--   - `worstFidelity`: A1, PDF p.10. Infimum over all density matrices and all positive finite reference sizes. For lawful channels on nonempty finite spaces this set is nonempty and bounded in [0,1]. No theorem uses the empty-input default of a real infimum.
--   - `stabilizedHalfDiamondError`: A3--A4, PDF p.11: half the stabilized trace distance, equal to half the diamond norm for differences of channels. Stabilization includes arbitrary entangled references. For channels the supremum is nonempty and bounded by 1.
--   - `entanglementError`: A5, PDF p.11; the factor 1/2 acts on normalized Choi states.
--   - `choiPairFidelity`: A2, PDF p.10: squared Uhlmann fidelity of the normalized Choi states.
--   - `IsSUChannelCovariant`: Full SU(d) covariance, not covariance under just one chosen generator (A.6 preamble, PDF p.18).
--   - `maskedTransversalMatrix`: U on selected physical sites and identity on idle sites (A14, PDF p.12). The mask is fixed independently of U and of the logical input.
--   - `CovariantCode`: A14, PDF p.12, and the general-code lower-bound setting on pp.22,26. The encoder is CPTP and exactly covariant under the indicated transversal action. The decoder is an arbitrary CPTP recovery on the full flagged tensor space.
--   - `covariantError`: A16, PDF p.13: worst error over all logical gates, computed from the actual code and actual physical noise. In the channel regimes below the set is nonempty, compact in its gate parameter, and bounded by 1; the supremum equals the source's maximum.
--   - `localErasureKraus`: Kraus family for the single-qudit flagged erasure channel (B1,C1, PDF pp.21,24). The index `none` is the surviving Kraus operator; `some a` erases basis component a. The parameter is used only in [0,1].
--   - `localErasure`: Local erasure, with orthogonal flag (C1, PDF p.24).
--   - `subsetErasure`: Erase exactly the sites in s, retaining the other sites. This tensor definition acts on all operators, including entangled inputs (B1, PDF p.21).
--   - `uniformSubsetErasure`: B19--B20, PDF p.23: uniform distribution on exactly k-element subsets. There is no independent-site assumption and no no-erasure atom when k≥1.
--   - `iidErasure`: Independent erasure of every physical qudit (C1, PDF p.24).
--   - `flaggedGate`: The physical gate extended by identity on the orthogonal erasure flag (PDF p.8).
--   - `flaggedTransversal`: Transversal implementation on the full tensor product of flagged local spaces (PDF p.8). Idle sites and erasure flags are fixed.
--   - `erasurePatternProjector`: Joint projector onto the known erasure pattern s, including mixed patterns (PDF p.8).
--   - `referenceOrbitSpan`: Vector-orbit support under U on one half and identity on the other (D2--D3, PDF p.29). The rank of the twirled pure state is this dimension. SOURCE CORRECTION: D1 prints the span of density operators. Its proof uses the vector-orbit support instead. These dimensions differ; independent moderation is required.
--   - `sineCoefficient`: Raw sine coefficients B8, PDF p.21, evaluated on integer indices. They are not asserted to form a normalized law on the paper's declared [M]={1,...,M}.
--   - `sineOverlapError`: B10, PDF p.22. The cutoff is 2n0; it is not the total physical code size. Natural subtraction in the endpoint is used only for sufficiently large M.
--   - `schurCharacter`: SU(d) character of the actual Young-symmetrizer Schur module, not a free character variable (A12, PDF p.12).
--   - `canonicalEstimateDensity`: Canonical A12 estimate density for a finite support L and probability weights q. At the true gate I the character is evaluated on U inverse (PDF pp.12,15).
--   - `costRepresentation`: The actual UC tensor UL-star representation (A36, PDF p.15). `map conj` is entrywise complex conjugation, not adjoint.
--   - `referenceCostChannel`: A36--A37, PDF p.15: channel induced by the canonical surviving-frame estimate law. Only lawful normalized q and Haar measure are used in the results.
--   - `indexedDifference`: A39, PDF p.15: encode each integer shift in [-n0,n0] by a finite index. The zero-sum constraint is imposed by `differenceIndices`.
--   - `differenceIndices`: Sdiff, A39, PDF p.15, a finite nonempty set containing the zero shift.
--   - `shiftedMass`: Extend q by zero to integer row vectors; different shifted diagrams are not silently truncated into Young shapes (A39, PDF p.15).
--   - `interiorShapes`: Sint: positive support with every pair of distinct rows separated by more than 3n0 (A38, PDF p.15). The `i ≠ j` guard is essential.
--   - `minimumInteriorOverlap`: Attained finite minimum in Lemma 2. Sint may be empty, giving a zero sum; Sdiff is never empty (A38--A39, PDF p.15).
--   - `schurWeylShiftedRow`: Shifted integer rows in C6 (PDF p.25), with one-based source row j=i.val+1.
--   - `schurWeylMass`: Integer Schur--Weyl law C6, PDF p.25. This formula has no fractional Young shapes and no interpolation of factorials. The factorial product includes 0!=1.
--   - `schurWeylConstant`: Gamma in C8, PDF p.25. The d=1 case is not used.
--   - `computationSize`: The integer convention for nC=n^gamma, with bounded downward rounding (C.1, PDF p.24). The positive regime begins at the theorem's threshold.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, https://arxiv.org/abs/2007.09154v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_SchurModules
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Statements from Yang et al., arXiv:2007.09154v2.

Paper-specific objects below are local; matching accepted definitions are imported. Channels use the accepted finite Kraus
semantics. Fidelities are squared Uhlmann fidelities. Stabilization ranges over every
positive finite reference dimension; the two error measures contain the factor 1/2.
Deferred nodes, including source defects, are recorded in the unit's HARD.md and GAPS.json.
No source correction here is certified by independent moderation. Compilation is pending.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)
open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Erasure output space: a tensor product of local direct sums, retaining every mixed
surviving/erased pattern (PDF pp.8,22). `none` is the orthogonal erasure flag. -/
abbrev FlaggedRegister (d n : ℕ) := Fin n → Option (Fin d)

/-- Fixed Borel sigma algebra on SU(d) (PDF p.10). -/
instance specialUnitaryMeasurable (d : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) := borel _

/-- Normalized Haar law, with its left and right translation invariance, not Haar volume.
The Borel space is fixed above; on this compact group this specifies the unique probability
Haar measure (PDF pp.3,10). -/
def IsNormalizedHaar {d : ℕ} (mu : Measure (Matrix.specialUnitaryGroup (Fin d) ℂ)) : Prop :=
  mu Set.univ = 1 ∧
    (∀ V : (Matrix.specialUnitaryGroup (Fin d) ℂ), Measure.map (fun U => V * U) mu = mu) ∧
    (∀ V : (Matrix.specialUnitaryGroup (Fin d) ℂ), Measure.map (fun U => U * V) mu = mu)

/-- A1, PDF p.10. Infimum over all density matrices and all positive finite reference
sizes. For lawful channels on nonempty finite spaces this set is nonempty and bounded in
[0,1]. No theorem uses the empty-input default of a real infimum. -/
def worstFidelity {i o : Type*} [Fintype i] [Fintype o] [DecidableEq o]
    (A B : Superop i o) : ℝ :=
  sInf {v : ℝ | ∃ k : ℕ, 0 < k ∧
    ∃ rho : Matrix (Fin k × i) (Fin k × i) ℂ, IsDensityMatrix rho ∧
      v = squaredFidelity (idTensorSuperop (R := Fin k) A rho)
        (idTensorSuperop (R := Fin k) B rho)}

/-- A3--A4, PDF p.11: half the stabilized trace distance, equal to half the diamond
norm for differences of channels. Stabilization includes arbitrary entangled references.
For channels the supremum is nonempty and bounded by 1. -/
def stabilizedHalfDiamondError {i o : Type*} [Fintype i] [Fintype o] [DecidableEq o]
    (A B : Superop i o) : ℝ :=
  sSup {v : ℝ | ∃ k : ℕ, 0 < k ∧
    ∃ rho : Matrix (Fin k × i) (Fin k × i) ℂ, IsDensityMatrix rho ∧
      v = traceNorm (idTensorSuperop (R := Fin k) A rho -
        idTensorSuperop (R := Fin k) B rho) / 2}

/-- A5, PDF p.11; the factor 1/2 acts on normalized Choi states. -/
def entanglementError (d : ℕ) (hd : 0 < d) (A B : Superop (Fin d) (Fin d)) : ℝ :=
  traceNorm (normalizedChoi A - normalizedChoi B) / 2

/-- A2, PDF p.10: squared Uhlmann fidelity of the normalized Choi states. -/
def choiPairFidelity (d : ℕ) (hd : 0 < d) (A B : Superop (Fin d) (Fin d)) : ℝ :=
  squaredFidelity (normalizedChoi A) (normalizedChoi B)

/-- Full SU(d) covariance, not covariance under just one chosen generator
(A.6 preamble, PDF p.18). -/
def IsSUChannelCovariant {d : ℕ} (A : Superop (Fin d) (Fin d)) : Prop :=
  ∀ U : (Matrix.specialUnitaryGroup (Fin d) ℂ),
    A ∘ conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) =
      conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) ∘ A

/-- U on selected physical sites and identity on idle sites (A14, PDF p.12).
The mask is fixed independently of U and of the logical input. -/
def maskedTransversalMatrix {d n : ℕ} (active : Fin n → Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((Register (fun _ : Fin n => d))) ((Register (fun _ : Fin n => d))) ℂ :=
  fun x y => ∏ j, if active j then U (x j) (y j) else if x j = y j then 1 else 0

/-- A14, PDF p.12, and the general-code lower-bound setting on pp.22,26.
The encoder is CPTP and exactly covariant under the indicated transversal action.
The decoder is an arbitrary CPTP recovery on the full flagged tensor space. -/
structure CovariantCode (d n : ℕ) where
  active : Fin n → Bool
  encoder : Superop (Fin d) ((Register (fun _ : Fin n => d)))
  decoder : Superop (FlaggedRegister d n) (Fin d)
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder
  encoder_covariance : ∀ U : (Matrix.specialUnitaryGroup (Fin d) ℂ),
    encoder ∘ conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) =
      conjSuperop (maskedTransversalMatrix active (U : Matrix (Fin d) (Fin d) ℂ)) ∘ encoder

/-- A16, PDF p.13: worst error over all logical gates, computed from the actual code
and actual physical noise. In the channel regimes below the set is nonempty, compact in
its gate parameter, and bounded by 1; the supremum equals the source's maximum. -/
def covariantError {d n : ℕ} (code : CovariantCode d n)
    (noise : Superop ((Register (fun _ : Fin n => d))) (FlaggedRegister d n)) : ℝ :=
  sSup {v : ℝ | ∃ U : (Matrix.specialUnitaryGroup (Fin d) ℂ),
    v = stabilizedHalfDiamondError (code.decoder ∘ noise ∘
      conjSuperop (maskedTransversalMatrix code.active (U : Matrix (Fin d) (Fin d) ℂ)) ∘ code.encoder)
      (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ))}

/-- Kraus family for the single-qudit flagged erasure channel (B1,C1, PDF pp.21,24).
The index `none` is the surviving Kraus operator; `some a` erases basis component a.
The parameter is used only in [0,1]. -/
def localErasureKraus (d : ℕ) (p : ℝ) :
    Option (Fin d) → Matrix (Option (Fin d)) (Fin d) ℂ
  | none => fun y x => if y = some x then (Real.sqrt (1 - p) : ℂ) else 0
  | some a => fun y x => if y = none ∧ x = a then (Real.sqrt p : ℂ) else 0

/-- Local erasure, with orthogonal flag (C1, PDF p.24). -/
def localErasure (d : ℕ) (p : ℝ) : Superop (Fin d) (Option (Fin d)) :=
  krausApply (localErasureKraus d p)

/-- Erase exactly the sites in s, retaining the other sites. This tensor definition
acts on all operators, including entangled inputs (B1, PDF p.21). -/
def subsetErasure (d n : ℕ) (s : Finset (Fin n)) :
    Superop ((Register (fun _ : Fin n => d))) (FlaggedRegister d n) :=
  piSuperop fun j => localErasure d (if j ∈ s then 1 else 0)

/-- B19--B20, PDF p.23: uniform distribution on exactly k-element subsets.
There is no independent-site assumption and no no-erasure atom when k≥1. -/
def uniformSubsetErasure (d n k : ℕ) : Superop ((Register (fun _ : Fin n => d))) (FlaggedRegister d n) :=
  fun X => ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    (((Nat.choose n k : ℝ)⁻¹ : ℂ)) • subsetErasure d n s X

/-- Independent erasure of every physical qudit (C1, PDF p.24). -/
def iidErasure (d n : ℕ) (p : ℝ) : Superop ((Register (fun _ : Fin n => d))) (FlaggedRegister d n) :=
  piSuperop fun _ => localErasure d p

/-- The physical gate extended by identity on the orthogonal erasure flag
(PDF p.8). -/
def flaggedGate {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℂ
  | some i, some j => U i j
  | none, none => 1
  | _, _ => 0

/-- Transversal implementation on the full tensor product of flagged local spaces
(PDF p.8). Idle sites and erasure flags are fixed. -/
def flaggedTransversal {d n : ℕ} (active : Fin n → Bool)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (FlaggedRegister d n) (FlaggedRegister d n) ℂ :=
  fun x y => ∏ j, if active j then flaggedGate U (x j) (y j)
    else if x j = y j then 1 else 0

/-- Joint projector onto the known erasure pattern s, including mixed patterns
(PDF p.8). -/
def erasurePatternProjector (d n : ℕ) (s : Finset (Fin n)) :
    Matrix (FlaggedRegister d n) (FlaggedRegister d n) ℂ :=
  Matrix.diagonal fun x => if ∀ j, (x j = none ↔ j ∈ s) then 1 else 0

/-- Vector-orbit support under U on one half and identity on the other
(D2--D3, PDF p.29). The rank of the twirled pure state is this dimension.
SOURCE CORRECTION: D1 prints the span of density operators. Its proof uses the
vector-orbit support instead. These dimensions differ; independent moderation is required. -/
def referenceOrbitSpan {d r : ℕ}
    (psi : EuclideanSpace ℂ ((Register (fun _ : Fin r => d)) × (Register (fun _ : Fin r => d)))) :
    Submodule ℂ (EuclideanSpace ℂ ((Register (fun _ : Fin r => d)) × (Register (fun _ : Fin r => d)))) :=
  Submodule.span ℂ (Set.range fun U : (Matrix.specialUnitaryGroup (Fin d) ℂ) =>
    act (Matrix.kronecker (piKron r (U : Matrix (Fin d) (Fin d) ℂ))
      (1 : Matrix ((Register (fun _ : Fin r => d))) ((Register (fun _ : Fin r => d))) ℂ)) psi)

/-- Raw sine coefficients B8, PDF p.21, evaluated on integer indices. They are not
asserted to form a normalized law on the paper's declared [M]={1,...,M}. -/
def sineCoefficient (M : ℕ) (k : ℤ) : ℝ :=
  2 / ((M : ℝ) + 1) *
    Real.sin (Real.pi * (2 * (k : ℝ) + 1) / (2 * ((M : ℝ) + 1))) ^ 2

/-- B10, PDF p.22. The cutoff is 2n0; it is not the total physical code size.
Natural subtraction in the endpoint is used only for sufficiently large M. -/
def sineOverlapError (n0 M : ℕ) (delta : ℤ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc (2 * n0) (M - 2 * n0),
    Real.sqrt (sineCoefficient M k * sineCoefficient M ((k : ℤ) + delta))

/-- SU(d) character of the actual Young-symmetrizer Schur module, not a free
character variable (A12, PDF p.12). -/
def schurCharacter {d m : ℕ} (lambda : QAlgorithms.Schur.Partition d m)
    (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : ℂ :=
  LinearMap.trace ℂ (QAlgorithms.Schur.schurModule lambda)
    (QAlgorithms.Schur.polynomialRepresentation lambda (U : Matrix (Fin d) (Fin d) ℂ))

/-- Canonical A12 estimate density for a finite support L and probability weights q.
At the true gate I the character is evaluated on U inverse (PDF pp.12,15). -/
def canonicalEstimateDensity {d m : ℕ} (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ) (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : ℝ :=
  Complex.normSq (∑ lambda ∈ L, (Real.sqrt (q lambda) : ℂ) * schurCharacter lambda U⁻¹)

/-- The actual UC tensor UL-star representation (A36, PDF p.15).
`map conj` is entrywise complex conjugation, not adjoint. -/
def costRepresentation (d nC : ℕ) (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    Matrix ((Register (fun _ : Fin nC => d)) × Fin d) ((Register (fun _ : Fin nC => d)) × Fin d) ℂ :=
  Matrix.kronecker (piKron nC (U : Matrix (Fin d) (Fin d) ℂ))
    ((U : Matrix (Fin d) (Fin d) ℂ).map conj)

/-- A36--A37, PDF p.15: channel induced by the canonical surviving-frame estimate
law. Only lawful normalized q and Haar measure are used in the results. -/
def referenceCostChannel {d m : ℕ} (mu : Measure (Matrix.specialUnitaryGroup (Fin d) ℂ)) (nC : ℕ)
    (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ) :
    Superop ((Register (fun _ : Fin nC => d)) × Fin d) ((Register (fun _ : Fin nC => d)) × Fin d) :=
  fun X => ∫ U, (canonicalEstimateDensity L q U : ℂ) • conjSuperop (costRepresentation d nC U) X ∂mu

/-- A39, PDF p.15: encode each integer shift in [-n0,n0] by a finite index.
The zero-sum constraint is imposed by `differenceIndices`. -/
def indexedDifference {d n0 : ℕ} (x : Fin d → Fin (2 * n0 + 1)) : Fin d → ℤ :=
  fun i => (x i : ℤ) - (n0 : ℤ)

/-- Sdiff, A39, PDF p.15, a finite nonempty set containing the zero shift. -/
def differenceIndices (d n0 : ℕ) : Finset (Fin d → Fin (2 * n0 + 1)) :=
  Finset.univ.filter fun x => ∑ i, indexedDifference x i = 0

/-- Extend q by zero to integer row vectors; different shifted diagrams are not
silently truncated into Young shapes (A39, PDF p.15). -/
def shiftedMass {d m : ℕ} (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ)
    (lambda : QAlgorithms.Schur.Partition d m) (delta : Fin d → ℤ) : ℝ :=
  ∑ nu ∈ L, if ∀ i : Fin d,
    (nu.val.rowLen i.val : ℤ) = (lambda.val.rowLen i.val : ℤ) + delta i then q nu else 0

/-- Sint: positive support with every pair of distinct rows separated by more than
3n0 (A38, PDF p.15). The `i ≠ j` guard is essential. -/
def interiorShapes {d m : ℕ} (n0 : ℕ) (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ) : Finset (QAlgorithms.Schur.Partition d m) :=
  L.filter fun lambda => 0 < q lambda ∧ ∀ i j : Fin d, i ≠ j →
    (3 * n0 : ℤ) < |(lambda.val.rowLen i.val : ℤ) - (lambda.val.rowLen j.val : ℤ)|

/-- Attained finite minimum in Lemma 2. Sint may be empty, giving a zero sum;
Sdiff is never empty (A38--A39, PDF p.15). -/
def minimumInteriorOverlap {d m : ℕ} (n0 : ℕ)
    (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ) : ℝ :=
  (differenceIndices d n0).inf'
    (by
      refine ⟨fun _ => ⟨n0, by omega⟩, ?_⟩
      simp [differenceIndices, indexedDifference])
    (fun x => ∑ lambda ∈ interiorShapes n0 L q,
      Real.sqrt (q lambda * shiftedMass L q lambda (indexedDifference x)))

/-- Shifted integer rows in C6 (PDF p.25), with one-based source row j=i.val+1. -/
def schurWeylShiftedRow {d s : ℕ} (lambda : QAlgorithms.Schur.Partition d s) (i : Fin d) : ℕ :=
  lambda.val.rowLen i.val + (d - 1 - i.val)

/-- Integer Schur--Weyl law C6, PDF p.25. This formula has no fractional Young
shapes and no interpolation of factorials. The factorial product includes 0!=1. -/
def schurWeylMass {d s : ℕ} (lambda : QAlgorithms.Schur.Partition d s) : ℝ :=
  (Nat.factorial s : ℝ) *
    (∏ i : Fin d, ∏ j : Fin d, if i < j then
      ((schurWeylShiftedRow lambda i : ℝ) - (schurWeylShiftedRow lambda j : ℝ)) ^ 2 else 1) /
    ((d : ℝ) ^ s * (∏ i : Fin d, (Nat.factorial (schurWeylShiftedRow lambda i) : ℝ)) *
      (∏ i : Fin d, (Nat.factorial i.val : ℝ)))

/-- Gamma in C8, PDF p.25. The d=1 case is not used. -/
def schurWeylConstant (d : ℕ) : ℝ :=
  (d : ℝ) ^ (d * (d - 1) / 2) / ∏ i : Fin d, (Nat.factorial i.val : ℝ)

/-- The integer convention for nC=n^gamma, with bounded downward rounding
(C.1, PDF p.24). The positive regime begins at the theorem's threshold. -/
def computationSize (gamma : ℝ) (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ gamma)

/-- Sanity check for squared fidelity, A1, PDF p.10. -/
example : squaredFidelity (1 : Matrix Unit Unit ℂ) 1 = 1 := by
  simp [squaredFidelity, rootFidelity, cfc_one]

example {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : flaggedGate U none none = 1 := rfl

example (d : ℕ) (a : Fin d) : localErasureKraus d 1 none (some a) a = 0 := by
  simp [localErasureKraus]

example (d n0 : ℕ) : (differenceIndices d n0).Nonempty := by
  refine ⟨fun _ => ⟨n0, by omega⟩, ?_⟩
  simp [differenceIndices, indexedDifference]

example (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (x y : (Register (fun _ : Fin 0 => d))) :
    maskedTransversalMatrix (fun _ => true) U x y = 1 := by
  simp [maskedTransversalMatrix]

example : schurWeylConstant 2 = 2 := by
  norm_num [schurWeylConstant, Fin.prod_univ_two]

end QAlgorithms.Papers.Independent.Extend50.P15


