-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70
-- name    : QAlgorithms_Papers_Independent_Intake100_P70
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:30:08.130298+00:00
-- url     : https://prove2.me/theorems/d4efeeeb-d281-4d6a-9d02-5948595cb8e6
-- title:
--   Definitions for Information preserving structures: A general framework for quantum zero-error information
-- statement:
--   The objects the formalized statements of *Information preserving structures: A general framework for quantum zero-error information* (arXiv:1006.1358) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsCode`: PDF pp.2,6–7: convex sets of normalized density matrices; empty codes are allowed.
--   - `weighted`: PDF p.5: the weighted difference with prior p.
--   - `Preserved`: PDF p.7, Definition 7: every pair, every prior, including endpoints.
--   - `IsCodeIsometry`: PDF p.5, Definition 4: complex-linear span identification, bijective on codes, preserving weighted trace norms. An ambient linear extension exists in finite dimension.
--   - `OneIsometric`: PDF p.5: existence of a 1-isometry between normalized code sets.
--   - `MaximumCode`: PDF p.2, Definition 3: maximum in the isometric order, not inclusion-maximal.
--   - `powerMixture`: PDF pp.7,21: arbitrary probability mixtures of nonnegative powers including E^0. For CPTP E, summability follows from finite-dimensional power boundedness and HasSum q 1.
--   - `Noiseless`: PDF p.7, Definition 8: preserved by every probability mixture of powers.
--   - `CorrectableCode`: PDF p.7, Definition 9: recovery makes the code noiseless, not definitionally fixed.
--   - `UnitarilyNoiseless`: PDF p.13, Definition 12: preserved by every individual power, including zero.
--   - `fixedOperators`: PDF pp.8–9: all fixed operators, without a state restriction.
--   - `statePart`: PDF p.25, footnote 12: only positive trace-1 matrices in the specified space.
--   - `fixedStates`: PDF pp.8,22: all fixed density matrices.
--   - `CornerSupported`: PDF p.21: two-sided corner support, including non-Hermitian operators.
--   - `jointSupport`: PDF pp.8,22: least joint physical support, computed from a finite basis of the complex operator span. The resulting projection is basis independent.
--   - `codeSupport`: PDF p.8: support of the whole code.
--   - `fixedSupport`: PDF p.9: support of all fixed operators, not a chosen fixed density.
--   - `CornerInvariant`: PDF p.9(i): invariance of the entire operator corner.
--   - `FullRankOn`: PDF p.21: full rank relative to P, not relative to the ambient space.
--   - `supportInvSqrt`: PDF pp.8,20: support inverse square root, zero on the kernel.
--   - `transposeRecovery`: PDF p.8, Eq.(6): raw transpose recovery on supp(E(P)); no ambient TP claim.
--   - `fullTransposeRecovery`: PDF pp.15,17: full-input transpose recovery, with an explicit maximally mixed replacement on ker E(I). On the channel image it equals the printed formula.
--   - `cornerAdjoint`: PDF p.9(ii): restricted adjoint on B(P0), represented inside the ambient space.
--   - `cornerAlgebra`: PDF p.9(ii): the computed corner fixed algebra.
--   - `IsMatrixAlgebra`: PDF p.8: concrete complex star algebra, with support unit P and zero complement.
--   - `BlockModel`: PDF pp.8,23, Eqs.(7),(B4): orthogonal embedded nonzero tensor sectors. The remaining physical orthogonal complement is allowed.
--   - `BlockModel.support`: PDF p.23: support projection of the sector sum.
--   - `BlockModel.blockSpace`: PDF pp.9,23: arbitrary logical matrices tensored with specified gauge factors.
--   - `BlockModel.algebra`: PDF p.8, Eq.(7): full matrix factors tensored with unnormalized identities.
--   - `BlockModel.DistortionFactors`: PDF p.9, Definition 10: TP distortion normalization Tr(tau_k)=dim(B_k), excluding zero factors. Density gauge formulas use normalized factors instead.
--   - `BlockModel.gaugeCode`: PDF pp.9,25: all probability weights and all logical density matrices, with one density gauge per sector independent of the chosen logical states.
--   - `IsFixedDecomposition`: PDF pp.9,23: coordinates for the computed fixed-support adjoint algebra.
--   - `cesaroAverage`: PDF p.22: actual Cesaro average through power N, starting at n=0.
--   - `rotatingSpace`: PDF pp.16,26: complex span of all unit-modulus eigenoperators; a rotating point need not itself be an eigenoperator.
--   - `operatorHSNorm`: PDF p.27: Hilbert–Schmidt norm, not the entrywise infinity norm.
--   - `RotatingRecurrence`: PDF pp.27–28: strict induced Hilbert–Schmidt norm bound on Rot(E). A common real bound c is chosen before every operator.
--   - `IsPeripheralProjection`: PDF p.28: CPTP idempotent limit along unbounded positive powers, with range and fixed space Rot(E). Pointwise matrix convergence and superoperator-norm convergence are equivalent here by finite dimensionality.
--   - `IsJordanChain`: PDF p.27, Eq.(B9): a Jordan chain already transported to physical coordinates by the similarity. No orthogonality or spectral nondegeneracy is assumed.
--   - `ProjectiveMeasurement`: PDF p.15, Definition 15: projective partitions; zero outcomes are allowed.
--   - `UnconditionalMeasurement`: PDF p.15: exact POVM simulation on EVERY physical input density matrix.
--   - `helstromPartition`: PDF pp.5,15: positive, negative AND zero spectral projectors of Delta.
--   - `UnconditionalCode`: PDF p.15, Definition 16: unconditional simulation of every weighted Helstrom partition. Convexity and normalization belong to the separate code assumption.
--   - `UnconditionalStructure`: PDF pp.15–17: a common algebraic structure containing all unconditional codes up to isometry, including every maximum code as its full state shape.
--   - `Subsystem`: PDF pp.4,17: specified nonzero A tensor B sector embedded in physical H.
--   - `Subsystem.support`: PDF p.17: subsystem support projection.
--   - `Subsystem.logical`: PDF pp.4,17: subnormalized logical marginal, retaining sector population.
--   - `StrictNoiselessSubsystem`: PDF p.4, Eqs.(3)–(5): strict noiselessness, including confinement to the sector.
--   - `InitializationFree`: PDF pp.17–18: no perfect-initialization hypothesis; arbitrary outside population and off-diagonal coherences are retained.
--   - `UnconditionalSubsystem`: PDF pp.17–18: all logical projective measurements, each supplemented by the outside-sector outcome; this concerns every gauge, not one rank-deficient gauge code.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, https://arxiv.org/abs/1006.1358v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-! arXiv:1006.1358v1. All page numbers are PDF pages.
Paper-local definitions have complete bodies. Compilation is pending batch handoff. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF pp.2,6–7: convex sets of normalized density matrices; empty codes are allowed. -/
def IsCode {I : Type*} [Fintype I] (C : Set (Op I)) : Prop :=
  Convex ℝ C ∧ ∀ X ∈ C, IsDensityMatrix X

/-- PDF p.5: the weighted difference with prior p. -/
def weighted {I : Type*} (p : ℝ) (X Y : Op I) : Op I :=
  (p : ℂ) • X - ((1 - p : ℝ) : ℂ) • Y

/-- PDF p.7, Definition 7: every pair, every prior, including endpoints. -/
def Preserved {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : Superop I J) (C : Set (Op I)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, ∀ p ∈ Set.Icc (0 : ℝ) 1,
    traceNorm (E (weighted p X Y)) = traceNorm (weighted p X Y)

/-- PDF p.5, Definition 4: complex-linear span identification, bijective on codes,
preserving weighted trace norms. An ambient linear extension exists in finite dimension. -/
def IsCodeIsometry {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : Superop I J)
    (C : Set (Op I)) (D : Set (Op J)) : Prop :=
  (∃ L : Op I →ₗ[ℂ] Op J, ∀ X, L X = f X) ∧
  (∀ X ∈ Submodule.span ℂ C, f X = 0 → X = 0) ∧ f '' C = D ∧
  ∀ X ∈ C, ∀ Y ∈ C, ∀ p ∈ Set.Icc (0 : ℝ) 1,
    traceNorm (weighted p (f X) (f Y)) = traceNorm (weighted p X Y)

/-- PDF p.5: existence of a 1-isometry between normalized code sets. -/
def OneIsometric {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (C : Set (Op I)) (D : Set (Op J)) : Prop :=
  ∃ f : Superop I J, IsCodeIsometry f C D

/-- PDF p.2, Definition 3: maximum in the isometric order, not inclusion-maximal. -/
def MaximumCode {I : Type*} [Fintype I] [DecidableEq I]
    (criterion : Set (Op I) → Prop) (C : Set (Op I)) : Prop :=
  IsCode C ∧ criterion C ∧ ∀ D : Set (Op I), IsCode D → criterion D →
    ∀ S : Set (Op I), S ⊂ D → ¬ OneIsometric C S

/-- PDF pp.7,21: arbitrary probability mixtures of nonnegative powers including E^0.
For CPTP E, summability follows from finite-dimensional power boundedness and HasSum q 1. -/
def powerMixture {I : Type*} [Fintype I] (E : Superop I I) (q : ℕ → ℝ) : Superop I I :=
  fun X => ∑' n : ℕ, (q n : ℂ) • (E^[n]) X

/-- PDF p.7, Definition 8: preserved by every probability mixture of powers. -/
def Noiseless {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) (C : Set (Op I)) : Prop :=
  ∀ q : ℕ → ℝ, (∀ n, 0 ≤ q n) → HasSum q 1 → Preserved (powerMixture E q) C

/-- PDF p.7, Definition 9: recovery makes the code noiseless, not definitionally fixed. -/
def CorrectableCode {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (E : Superop I J) (C : Set (Op I)) : Prop :=
  ∃ R : Superop J I, IsChannel R ∧ Noiseless (R ∘ E) C

/-- PDF p.13, Definition 12: preserved by every individual power, including zero. -/
def UnitarilyNoiseless {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) (C : Set (Op I)) : Prop := ∀ n : ℕ, Preserved (E^[n]) C

/-- PDF pp.8–9: all fixed operators, without a state restriction. -/
def fixedOperators {I : Type*} (E : Superop I I) : Set (Op I) := {X | E X = X}

/-- PDF p.25, footnote 12: only positive trace-1 matrices in the specified space. -/
def statePart {I : Type*} [Fintype I] (A : Set (Op I)) : Set (Op I) :=
  {X | IsDensityMatrix X ∧ X ∈ A}

/-- PDF pp.8,22: all fixed density matrices. -/
def fixedStates {I : Type*} [Fintype I] (E : Superop I I) : Set (Op I) :=
  statePart (fixedOperators E)

/-- PDF p.21: two-sided corner support, including non-Hermitian operators. -/
def CornerSupported {I : Type*} [Fintype I] (P X : Op I) : Prop := P * X * P = X

/-- PDF pp.8,22: least joint physical support, computed from a finite basis of
the complex operator span. The resulting projection is basis independent. -/
def jointSupport {I : Type*} [Fintype I] [DecidableEq I] (A : Set (Op I)) : Op I :=
  let V := Submodule.span ℂ A
  let b := Module.finBasis ℂ V
  supportProjector (∑ i, (((b i : V) : Op I) * ((b i : V) : Op I)ᴴ +
    ((b i : V) : Op I)ᴴ * ((b i : V) : Op I)))

/-- PDF p.8: support of the whole code. -/
def codeSupport {I : Type*} [Fintype I] [DecidableEq I] (C : Set (Op I)) : Op I :=
  jointSupport C

/-- PDF p.9: support of all fixed operators, not a chosen fixed density. -/
def fixedSupport {I : Type*} [Fintype I] [DecidableEq I] (E : Superop I I) : Op I :=
  jointSupport (fixedOperators E)

/-- PDF p.9(i): invariance of the entire operator corner. -/
def CornerInvariant {I : Type*} [Fintype I] (E : Superop I I) (P : Op I) : Prop :=
  ∀ X, CornerSupported P X → CornerSupported P (E X)

/-- PDF p.21: full rank relative to P, not relative to the ambient space. -/
def FullRankOn {I : Type*} [Fintype I] (P X : Op I) : Prop :=
  ∀ v : I → ℂ, P.mulVec v = v → X.mulVec v = 0 → v = 0

/-- PDF pp.8,20: support inverse square root, zero on the kernel. -/
def supportInvSqrt {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) : Op I :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) X

/-- PDF p.8, Eq.(6): raw transpose recovery on supp(E(P)); no ambient TP claim. -/
def transposeRecovery {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (E : Superop I J) (P : Op I) : Superop J I :=
  fun X => P * channelAdjoint E (supportInvSqrt (E P) * X * supportInvSqrt (E P)) * P

/-- PDF pp.15,17: full-input transpose recovery, with an explicit maximally mixed
replacement on ker E(I). On the channel image it equals the printed formula. -/
def fullTransposeRecovery {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (E : Superop I J) : Superop J I :=
  fun X => transposeRecovery E 1 X + (((1 - supportProjector (E 1)) * X).trace) •
    (((Fintype.card I : ℂ)⁻¹) • (1 : Op I))

/-- PDF p.9(ii): restricted adjoint on B(P0), represented inside the ambient space. -/
def cornerAdjoint {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) : Superop I I :=
  let P := fixedSupport E
  fun X => P * channelAdjoint E (P * X * P) * P

/-- PDF p.9(ii): the computed corner fixed algebra. -/
def cornerAlgebra {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) : Set (Op I) :=
  {X | CornerSupported (fixedSupport E) X ∧ cornerAdjoint E X = X}

/-- PDF p.8: concrete complex star algebra, with support unit P and zero complement. -/
def IsMatrixAlgebra {I : Type*} [Fintype I] (P : Op I) (A : Set (Op I)) : Prop :=
  P ∈ A ∧ (0 : Op I) ∈ A ∧ (∀ X ∈ A, CornerSupported P X) ∧
  (∀ X ∈ A, ∀ Y ∈ A, X + Y ∈ A) ∧ (∀ z : ℂ, ∀ X ∈ A, z • X ∈ A) ∧
  (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ X ∈ A, Xᴴ ∈ A)

/-- PDF pp.8,23, Eqs.(7),(B4): orthogonal embedded nonzero tensor sectors.
The remaining physical orthogonal complement is allowed. -/
structure BlockModel (I : Type*) [Fintype I] where
  sectors : ℕ
  logicalDim : Fin sectors → ℕ
  gaugeDim : Fin sectors → ℕ
  logical_pos : ∀ k, 0 < logicalDim k
  gauge_pos : ∀ k, 0 < gaugeDim k
  embed : (k : Fin sectors) → Matrix I (Fin (logicalDim k) × Fin (gaugeDim k)) ℂ
  isometry : ∀ k, (embed k)ᴴ * embed k = 1
  orthogonal : ∀ k l, k ≠ l → (embed k)ᴴ * embed l = 0

/-- PDF p.23: support projection of the sector sum. -/
def BlockModel.support {I : Type*} [Fintype I] (B : BlockModel I) : Op I :=
  ∑ k, B.embed k * (B.embed k)ᴴ

/-- PDF pp.9,23: arbitrary logical matrices tensored with specified gauge factors. -/
def BlockModel.blockSpace {I : Type*} [Fintype I] (B : BlockModel I)
    (tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k))) : Set (Op I) :=
  Set.range fun X : (k : Fin B.sectors) → Op (Fin (B.logicalDim k)) =>
    ∑ k, B.embed k * Matrix.kronecker (X k) (tau k) * (B.embed k)ᴴ

/-- PDF p.8, Eq.(7): full matrix factors tensored with unnormalized identities. -/
def BlockModel.algebra {I : Type*} [Fintype I] (B : BlockModel I) : Set (Op I) :=
  B.blockSpace (fun _ => 1)

/-- PDF p.9, Definition 10: TP distortion normalization Tr(tau_k)=dim(B_k),
excluding zero factors. Density gauge formulas use normalized factors instead. -/
def BlockModel.DistortionFactors {I : Type*} [Fintype I] (B : BlockModel I)
    (tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k))) : Prop :=
  ∀ k, (tau k).PosSemidef ∧ (tau k).trace = (B.gaugeDim k : ℂ)

/-- PDF pp.9,25: all probability weights and all logical density matrices, with
one density gauge per sector independent of the chosen logical states. -/
def BlockModel.gaugeCode {I : Type*} [Fintype I] (B : BlockModel I)
    (tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k))) : Set (Op I) :=
  {rho | ∃ p : Fin B.sectors → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
    ∃ X : (k : Fin B.sectors) → Op (Fin (B.logicalDim k)),
      (∀ k, IsDensityMatrix (X k)) ∧ rho = ∑ k, (p k : ℂ) •
        (B.embed k * Matrix.kronecker (X k) (tau k) * (B.embed k)ᴴ)}

/-- PDF pp.9,23: coordinates for the computed fixed-support adjoint algebra. -/
def IsFixedDecomposition {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) (B : BlockModel I) : Prop :=
  B.support = fixedSupport E ∧ B.algebra = cornerAlgebra E

/-- PDF p.22: actual Cesaro average through power N, starting at n=0. -/
def cesaroAverage {I : Type*} [Fintype I] (E : Superop I I) (N : ℕ) : Superop I I :=
  fun X => ((N + 1 : ℕ) : ℂ)⁻¹ • ∑ n ∈ Finset.range (N + 1), (E^[n]) X

/-- PDF pp.16,26: complex span of all unit-modulus eigenoperators; a rotating
point need not itself be an eigenoperator. -/
def rotatingSpace {I : Type*} (E : Superop I I) : Submodule ℂ (Op I) :=
  Submodule.span ℂ {X | ∃ z : ℂ, ‖z‖ = 1 ∧ E X = z • X}

/-- PDF p.27: Hilbert–Schmidt norm, not the entrywise infinity norm. -/
def operatorHSNorm {I : Type*} [Fintype I] (X : Op I) : ℝ :=
  Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j))

/-- PDF pp.27–28: strict induced Hilbert–Schmidt norm bound on Rot(E).
A common real bound c is chosen before every operator. -/
def RotatingRecurrence {I : Type*} [Fintype I]
    (E : Superop I I) (N : ℕ) (eps : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < eps ∧ ∀ X ∈ rotatingSpace E,
    operatorHSNorm ((E^[N]) X - X) ≤ c * operatorHSNorm X

/-- PDF p.28: CPTP idempotent limit along unbounded positive powers, with range
and fixed space Rot(E). Pointwise matrix convergence and superoperator-norm
convergence are equivalent here by finite dimensionality. -/
def IsPeripheralProjection {I : Type*} [Fintype I] [DecidableEq I]
    (E F : Superop I I) : Prop :=
  IsChannel F ∧ (∀ X, F (F X) = F X) ∧
  Set.range F = (rotatingSpace E : Set (Op I)) ∧
  fixedOperators F = (rotatingSpace E : Set (Op I)) ∧
  ∃ m : ℕ → ℕ, (∀ n, 0 < m n) ∧ Tendsto m atTop atTop ∧
    ∀ X, Tendsto (fun n => (E^[m n]) X) atTop (nhds (F X))

/-- PDF p.27, Eq.(B9): a Jordan chain already transported to physical coordinates
by the similarity. No orthogonality or spectral nondegeneracy is assumed. -/
def IsJordanChain {I : Type*} {m : ℕ} (E : Superop I I)
    (z : ℂ) (v : Fin m → Op I) : Prop :=
  LinearIndependent ℂ v ∧ ∀ i : Fin m, E (v i) = z • v i +
    (if h : i.val = 0 then 0 else v ⟨i.val - 1, by omega⟩)

/-- PDF p.15, Definition 15: projective partitions; zero outcomes are allowed. -/
def ProjectiveMeasurement {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (P : O → Op I) : Prop :=
  (∀ k, (P k)ᴴ = P k ∧ P k * P k = P k) ∧
  (∀ k l, k ≠ l → P k * P l = 0) ∧ ∑ k, P k = 1

/-- PDF p.15: exact POVM simulation on EVERY physical input density matrix. -/
def UnconditionalMeasurement {I J O : Type*} [Fintype I] [Fintype J] [Fintype O]
    [DecidableEq J] (E : Superop I J) (P : O → Op I) : Prop :=
  ∃ Q : O → Op J, (∀ k, (Q k).PosSemidef) ∧ (∑ k, Q k) = 1 ∧
    ∀ rho, IsDensityMatrix rho → ∀ k, (P k * rho).trace = (Q k * E rho).trace

/-- PDF pp.5,15: positive, negative AND zero spectral projectors of Delta. -/
def helstromPartition {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) : Fin 3 → Op I :=
  ![cfc (fun t : ℝ => if 0 < t then 1 else 0) X,
    cfc (fun t : ℝ => if t < 0 then 1 else 0) X,
    cfc (fun t : ℝ => if t = 0 then 1 else 0) X]

/-- PDF p.15, Definition 16: unconditional simulation of every weighted Helstrom
partition. Convexity and normalization belong to the separate code assumption. -/
def UnconditionalCode {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (E : Superop I J) (C : Set (Op I)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, ∀ p ∈ Set.Icc (0 : ℝ) 1,
    UnconditionalMeasurement E (helstromPartition (weighted p X Y))

/-- PDF pp.15–17: a common algebraic structure containing all unconditional
codes up to isometry, including every maximum code as its full state shape. -/
def UnconditionalStructure {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (E : Superop I J) (A : Set (Op I)) : Prop :=
  IsMatrixAlgebra 1 A ∧ IsCode (statePart A) ∧ UnconditionalCode E (statePart A) ∧
  (∀ C, IsCode C → UnconditionalCode E C →
    ∃ D : Set (Op I), D ⊆ statePart A ∧ OneIsometric C D) ∧
  ∀ C, MaximumCode (UnconditionalCode E) C → OneIsometric C (statePart A)

/-- PDF pp.4,17: specified nonzero A tensor B sector embedded in physical H. -/
structure Subsystem (I : Type*) [Fintype I] where
  logicalDim : ℕ
  gaugeDim : ℕ
  logical_pos : 0 < logicalDim
  gauge_pos : 0 < gaugeDim
  embed : Matrix I (Fin logicalDim × Fin gaugeDim) ℂ
  isometry : embedᴴ * embed = 1

/-- PDF p.17: subsystem support projection. -/
def Subsystem.support {I : Type*} [Fintype I] (S : Subsystem I) : Op I :=
  S.embed * S.embedᴴ

/-- PDF pp.4,17: subnormalized logical marginal, retaining sector population. -/
def Subsystem.logical {I : Type*} [Fintype I] (S : Subsystem I) (X : Op I) :
    Op (Fin S.logicalDim) := traceRight (S.embedᴴ * X * S.embed)

/-- PDF p.4, Eqs.(3)–(5): strict noiselessness, including confinement to the sector. -/
def StrictNoiselessSubsystem {I : Type*} [Fintype I]
    (E : Superop I I) (S : Subsystem I) : Prop :=
  ∀ rho, IsDensityMatrix rho → CornerSupported S.support rho →
    CornerSupported S.support (E rho) ∧ S.logical (E rho) = S.logical rho

/-- PDF pp.17–18: no perfect-initialization hypothesis; arbitrary outside
population and off-diagonal coherences are retained. -/
def InitializationFree {I : Type*} [Fintype I]
    (E : Superop I I) (S : Subsystem I) : Prop :=
  ∀ rho, IsDensityMatrix rho → S.logical (E rho) = S.logical rho

/-- PDF pp.17–18: all logical projective measurements, each supplemented by the
outside-sector outcome; this concerns every gauge, not one rank-deficient gauge code. -/
def UnconditionalSubsystem {I : Type*} [Fintype I] [DecidableEq I]
    (E : Superop I I) (S : Subsystem I) : Prop :=
  ∀ m : ℕ, ∀ P : Fin m → Op (Fin S.logicalDim), ProjectiveMeasurement P →
    UnconditionalMeasurement E (fun k : Option (Fin m) => match k with
      | none => 1 - S.support
      | some j => S.embed * Matrix.kronecker (P j) (1 : Op (Fin S.gaugeDim)) * S.embedᴴ)

/-- Sanity: the endpoint p=0 retains the entire second state, PDF p.5. -/
example {I : Type*} (X Y : Op I) : weighted 0 X Y = -Y := by
  simp [weighted]

/-- Sanity: identity dynamics preserve every weighted difference, PDF p.2. -/
example {I : Type*} [Fintype I] [DecidableEq I] (C : Set (Op I)) :
    Preserved (fun X : Op I => X) C := by
  intro X hX Y hY p hp
  rfl

/-- Sanity: zero support contains only zero, PDF p.21. -/
example {I : Type*} [Fintype I] (X : Op I) : CornerSupported 0 X ↔ X = 0 := by
  simp [CornerSupported, eq_comm]

/-- Sanity: the imported positive and negative spectral parts vanish at zero, PDF p.21. -/
example {I : Type*} [Fintype I] [DecidableEq I] :
    positivePart (0 : Op I) = 0 ∧ negativePart (0 : Op I) = 0 := by
  simp [positivePart, negativePart, cfc_zero]

/-- Sanity: at N=0 the Cesaro average is identity, PDF p.22. -/
example {I : Type*} [Fintype I] (E : Superop I I) (X : Op I) :
    cesaroAverage E 0 X = X := by
  simp [cesaroAverage]

end QAlgorithms.Papers.Independent.Intake100.P70


