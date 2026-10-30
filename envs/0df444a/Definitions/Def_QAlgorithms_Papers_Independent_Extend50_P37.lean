-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37
-- name    : QAlgorithms_Papers_Independent_Extend50_P37
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:17:20.743059+00:00
-- url     : https://prove2.me/theorems/bd146dd7-869a-46d9-ba35-9a0ccbbfb889
-- title:
--   Definitions for A generalization of Schur-Weyl duality with applications in quantum estimation
-- statement:
--   The objects the formalized statements of *A generalization of Schur-Weyl duality with applications in quantum estimation* (arXiv:1112.0638) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `alg`: Complex generated unital algebra (1112.0638v3, PDF p.4).
--   - `unitaryCentralizer`: All unitaries commuting with S (PDF pp.5-6).
--   - `UnitarySubgroup`: A unitary subgroup in its physical matrix embedding (PDF p.6).
--   - `IsGauge`: The double-centralizer definition of a gauge group (PDF p.6).
--   - `orderedTensorProduct`: Local tensor product, with the given factor order (PDF p.7).
--   - `localSet`: Ordered local action (PDF p.7).
--   - `collectiveImage`: Collective action, using the frozen tensor power (PDF p.5, (2.7)).
--   - `perm`: Transport of the frozen permutation action to an arbitrary finite basis; column x is sent to x composed with the inverse permutation (PDF p.5, (2.8)).
--   - `permutations`: Permutation matrices in the physical tensor representation (PDF p.5).
--   - `tensorAlg`: Tensor-power algebra (PDF pp.5-7).
--   - `permutationSector`: The two one-dimensional permutation sectors; true denotes the antisymmetric sector. The factor 1/n! is essential (PDF pp.9-10, Appendix A (A1)).
--   - `cornerAlg`: Algebra restricted to a sector, extended by zero outside it (PDF pp.9-10).
--   - `cornerComm`: Commutant in End(range P), represented by supported matrices; its identity is P. This handles zero-dimensional sectors (PDF pp.9-10).
--   - `hsVector`: Hilbert-Schmidt coordinates, needed to compute conditional expectations onto the physical matrix algebra (PDF pp.7,34-35).
--   - `algebraExpectation`: Hilbert-Schmidt orthogonal projection onto an algebra, reusing the frozen matrix-unit expectation after the finite-basis equivalence. For a unitary commutant this is Haar conditional expectation (PDF (3.4), (A9)).
--   - `promotion`: Corrected canonical promotion map, (3.10)-(3.11), PDF pp.11,35-36. C=T_local(Pi) has eigenvalues p_mu, not unnormalized traces. Its inverse square root is zero on zero blocks. Centrality of C makes this the same as (A14).
--   - `UCP`: Heisenberg unital complete positivity, with linearity and every ancillary dimension explicit; trace preservation is not required (PDF Theorem 8).
--   - `Promotes`: The complete three-clause promotion contract (PDF Theorem 8).
--   - `SubgroupHaarProbability`: A normalized Haar law actually supplied on a measurable subgroup; none is silently postulated for arbitrary nonclosed subgroups (PDF pp.7,13,25).
--   - `subgroupConjugationAverage`: Collective and local twirls (PDF pp.7,13,25).
--   - `GeneratorSpectralPVM`: Joint spectral measurement of generators, allowing projectors of rank larger than one (PDF Proposition 9).
--   - `Postprocess`: A stochastic classical rule after the fixed product spectral measurement. The output space is arbitrary, and each input string has a probability law (PDF pp.14,16-17).
--   - `RankOne`: Rank-one density matrices: rank one, with positivity and trace one supplied separately in a prior or state hypothesis (PDF pp.19-22).
--   - `EstimationPrior`: A probability law on density matrices, with a measurable full-measure support and a finite vector of measurable parameters (PDF pp.17-20). The support permits parameters to be constrained only where the prior lives.
--   - `Symmetry`: Invariance of the actual prior law, and pointwise invariance of parameters on its support. This allows singular pure-state priors (PDF (5.4)-(5.5)).
--   - `PurePrior`: Pure support, not purity of an average state (PDF Theorem 11).
--   - `ParameterBox`: Positive-probability parameter events. Order-convex measurable subsets of R model intervals of every endpoint convention, including unbounded ones (PDF pp.18-20,26).
--   - `EquallyInformative`: Equality of parameter-conditioned outcome laws for an arbitrary measurable outcome space. The simulator is quantified outside all B,D and states.
--   - `InAlgebra`: Image confined to an algebra, for measurable events only (PDF p.20).
--   - `Noiseless`: Noiselessness preserves all algebra observables on every density input; no covariance of the physical channel is imposed (PDF (5.7)).
--   - `Distortion`: Gauge distortion, using the covariance identity actually needed on PDF pp.28-29: N(U rho U*)=U N(rho) U*. The printed p.20 identity omits the output conjugation. The pure prior need not initially be invariant.
--   - `EstimationAssumptions`: Theorem 11 or 13 assumptions, for reuse in the merit statements (PDF p.21).
--   - `heisenbergDual`: Bilinear trace dual, computed on matrix units. For a physical channel this is its Heisenberg adjoint, including on non-Hermitian matrices (PDF pp.21,28).
--   - `BlockPresentation`: Physical block decomposition, including multiplicities and an actual unitary change of basis (PDF (3.3)). Zero padded blocks are omitted.
--   - `repeatedUnitaryBlocks`: The ordered physical embedding of direct sums I_m tensor V_n (PDF (3.3)).
--   - `BlockPresentation.group`: Gauge subgroup realized by a block presentation (PDF (3.3)).
--   - `BlockPresentation.signature`: Unordered block multiplicities, the invariant in uniqueness up to unitary equivalence; absent padded U(0) factors are not counted (PDF pp.6-7).
--   - `traceRightRegister`: Regroup interleaved ordered pairs into left and right registers, then apply the frozen actual partial trace over the right register (PDF p.14).
--   - `liftLeftRegister`: Identity on the complete right register, preserving coherences on the left; factor order remains interleaved (PDF p.14).
--   - `SameReduction`: PDF pp.21-22: equality of reductions, independent of a choice of basis.
--   - `observableAlgebra`: The source constructs the unital adjoint-closed algebra from its single observable; it is not a free algebra with a representation hypothesis (PDF pp.22,32). For Hermitian H this is Alg{H,I}.
--   - `phaseGroup`: Phase shifts with their scalar extension, in the number eigenbasis (PDF pp.15-17).
--   - `diagonalSet`: Diagonal algebra in the chosen basis (PDF p.16).
--   - `pairBasisKet`: Computational basis kets on two systems, specialized from the frozen ket at the ordered word ![a,b] (PDF pp.16-17).
--   - `bellSector`: The two Bell vectors in the one-excitation sector (PDF p.16).
--   - `qubitFilling`: Explicit two-qubit classical kernel from PDF p.16. On 01 and 10 use the Bell state of the chosen sign; 00 and 11 keep their basis state.
--   - `qutritVector`: Normalized versions of the two nonorthogonal vectors printed on PDF p.17. They are not an orthogonal projective basis.
--   - `qutritEffects`: A genuine three-outcome POVM incorporating both source projectors after scaling by 1/2; the third effect is the positive remainder (PDF p.17).
--   - `circleDensity`: Half-angle qubit states from the definition on PDF p.23.
--   - `phaseFlipMixture`: Common real dephasing family actually used in the example (PDF p.24).
--   - `circleDiagonal`: Born diagonal uses half-angles; the last line on PDF p.23 loses /2. At a=pi/2 this is I/2, as required by the state definition.
--   - `BasisProcessing`: A stochastic product-basis measurement (PDF pp.16-17,23-24).
--   - `twoQubitSeed`: The concrete |00> and Bell vectors in the two-qubit decision problem (PDF p.25), with the left register first.
--   - `twoQubitOrbit`: Single-system right-unitary orbit, not independent draws on each copy (PDF p.25).
--   - `decisionMarginal`: The left marginal is |0><0| for b=0 and I/2 for b=1 (PDF p.25).
--   - `SampleConditionals`: General conditional-law comparison, allowing the two independent states in VI B to be the sample, rather than treating them as identical copies.
--   - `pairDensity`: Product of two independent, potentially different density matrices, indexed in the same order as the sector projectors (PDF p.32).
--   - `spinOneGroup`: Spin-one SU(2) image in a Cartesian orthonormal basis: the complexification of SO(3). This is unitarily equivalent to the usual magnetic basis (PDF p.36).
--   - `spinZero`: Spin-zero projector in Cartesian coordinates; the spin-one sector is the antisymmetric sector and spin-two is the remaining symmetric sector (PDF p.36).
--   - `scalarUnitaries`: Scalar phase unitaries (PDF p.36).
--   - `standardSector`: The standard S3 isotypic projector, including all copies, from the character (2,0,-1) on identity, transpositions, 3-cycles (PDF pp.37-39).
--   - `leftUnitaryGroup`: Local U(2) actions on the left and right single-system qubits (PDF p.38).
--   - `rightUnitaryGroup`
--   - `BornKernel`: A measurable Born kernel for the actual n-copy/channel experiment, including continuous outcomes (PDF (5.1), (D2)-(D4)).
--   - `parameterJoint`: Joint estimated/true parameter law. No density for the parameter law and no conditioning on a zero-probability atom is assumed (PDF Appendix D).
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, https://arxiv.org/abs/1112.0638v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

/-- The source's finite-dimensional matrix Borel sigma algebra (PDF pp.17-20). -/
local instance estimationMatrixMeasurable (J : Type*) [Fintype J] :
    MeasurableSpace (Mat J) := borel _

/-- Matrix measurability is the Borel structure of the usual finite-dimensional
norm topology, so continuous state and parameter maps are measurable. -/
local instance estimationMatrixBorel (J : Type*) [Fintype J] :
    BorelSpace (Mat J) := ⟨rfl⟩

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Complex generated unital algebra (1112.0638v3, PDF p.4). -/
def alg (S : Set (Mat I)) : Set (Mat I) := Algebra.adjoin ℂ S

/-- All unitaries commuting with S (PDF pp.5-6). -/
def unitaryCentralizer (S : Set (Mat I)) : Set (Mat I) :=
  {U | U ∈ Matrix.unitaryGroup I ℂ ∧ U ∈ Set.centralizer S}

/-- A unitary subgroup in its physical matrix embedding (PDF p.6). -/
def UnitarySubgroup (G : Set (Mat I)) : Prop :=
  (∀ U ∈ G, U ∈ Matrix.unitaryGroup I ℂ) ∧ 1 ∈ G ∧
    (∀ U ∈ G, ∀ V ∈ G, U * V ∈ G) ∧ (∀ U ∈ G, Uᴴ ∈ G)

/-- The double-centralizer definition of a gauge group (PDF p.6). -/
def IsGauge (G : Set (Mat I)) : Prop :=
  UnitarySubgroup G ∧ unitaryCentralizer (unitaryCentralizer G) = G

/-- Local tensor product, with the given factor order (PDF p.7). -/
def orderedTensorProduct {n : ℕ} (X : Fin n → Mat I) : Mat (Fin n → I) :=
  Matrix.of fun x y => ∏ i, X i (x i) (y i)

/-- Ordered local action (PDF p.7). -/
def localSet (n : ℕ) (S : Set (Mat I)) : Set (Mat (Fin n → I)) :=
  {X | ∃ V : Fin n → Mat I, (∀ i, V i ∈ S) ∧ X = orderedTensorProduct V}

/-- Collective action, using the frozen tensor power (PDF p.5, (2.7)). -/
def collectiveImage (n : ℕ) (S : Set (Mat I)) : Set (Mat (Fin n → I)) :=
  {X | ∃ V ∈ S, X = piKron n V}

/-- Transport of the frozen permutation action to an arbitrary finite basis;
column x is sent to x composed with the inverse permutation (PDF p.5, (2.8)). -/
def perm (I : Type*) [Fintype I] (n : ℕ) (s : Equiv.Perm (Fin n)) :
    Mat (Fin n → I) :=
  (Schur.tensorPermutation (Fintype.card I) n s).submatrix
    (fun x i => Fintype.equivFin I (x i)) (fun x i => Fintype.equivFin I (x i))

/-- Permutation matrices in the physical tensor representation (PDF p.5). -/
def permutations (I : Type*) [Fintype I] (n : ℕ) : Set (Mat (Fin n → I)) :=
  Set.range (perm I n)

/-- Tensor-power algebra (PDF pp.5-7). -/
def tensorAlg (n : ℕ) (A : Set (Mat I)) : Set (Mat (Fin n → I)) :=
  alg (localSet n A)

/-- The two one-dimensional permutation sectors; true denotes the antisymmetric
sector. The factor 1/n! is essential (PDF pp.9-10, Appendix A (A1)). -/
def permutationSector (I : Type*) [Fintype I] (n : ℕ) (antisymmetric : Bool) :
    Mat (Fin n → I) :=
  ((Nat.factorial n : ℂ)⁻¹) • ∑ s : Equiv.Perm (Fin n),
    (if antisymmetric then ((Equiv.Perm.sign s : ℤ) : ℂ) else 1) • perm I n s

/-- Algebra restricted to a sector, extended by zero outside it (PDF pp.9-10). -/
def cornerAlg (P : Mat I) (S : Set (Mat I)) : Set (Mat I) :=
  {X | ∃ Y ∈ alg S, X = P * Y * P}

/-- Commutant in End(range P), represented by supported matrices; its identity
is P. This handles zero-dimensional sectors (PDF pp.9-10). -/
def cornerComm (P : Mat I) (S : Set (Mat I)) : Set (Mat I) :=
  {X | P * X * P = X ∧ ∀ Y ∈ S, X * (P * Y * P) = (P * Y * P) * X}

/-- Hilbert-Schmidt coordinates, needed to compute conditional expectations
onto the physical matrix algebra (PDF pp.7,34-35). -/
def hsVector (X : Mat I) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 fun p => X p.1 p.2

/-- Hilbert-Schmidt orthogonal projection onto an algebra, reusing the frozen
matrix-unit expectation after the finite-basis equivalence. For a unitary
commutant this is Haar conditional expectation (PDF (3.4), (A9)). -/
def algebraExpectation (A : Set (Mat I)) (X : Mat I) : Mat I :=
  let e := Fintype.equivFin I
  let toFin := fun Y : Mat I => Y.submatrix e.symm e.symm
  let AF := Submodule.span ℂ (toFin '' A)
  let Y := QAlgorithms.Papers.Independent.Information100.P26.applyMap
    (QAlgorithms.Papers.Independent.Information100.P26.expectation AF) (toFin X)
  Y.submatrix e e

/-- Corrected canonical promotion map, (3.10)-(3.11), PDF pp.11,35-36.
C=T_local(Pi) has eigenvalues p_mu, not unnormalized traces. Its inverse square
root is zero on zero blocks. Centrality of C makes this the same as (A14). -/
def promotion (A : Set (Mat I)) (n : ℕ) (s : Bool)
    (M : Mat (Fin n → I)) : Mat (Fin n → I) :=
  let P := permutationSector I n s
  let T := algebraExpectation (tensorAlg n A)
  let C := T P
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) C
  let Phi := fun X => R * T (P * X * P) * R
  Phi M + (M.trace / (Fintype.card (Fin n → I) : ℂ)) • (1 - Phi 1)

/-- Heisenberg unital complete positivity, with linearity and every ancillary
dimension explicit; trace preservation is not required (PDF Theorem 8). -/
def UCP (L : Mat I → Mat I) : Prop :=
  ∃ F : Mat I →ₗ[ℂ] Mat I, (∀ X, L X = F X) ∧ F 1 = 1 ∧
    Entanglement.IsCompletelyPositive F

/-- The complete three-clause promotion contract (PDF Theorem 8). -/
def Promotes (A : Set (Mat I)) (n : ℕ) (s : Bool)
    (L : Mat (Fin n → I) → Mat (Fin n → I)) : Prop :=
  UCP L ∧ (∀ X, L X ∈ tensorAlg n A ∩ Set.centralizer (permutations I n)) ∧
    ∀ X, permutationSector I n s * X * permutationSector I n s ∈ Set.centralizer (collectiveImage n (unitaryCentralizer A)) →
      permutationSector I n s * L X * permutationSector I n s = permutationSector I n s * X * permutationSector I n s

/-- A normalized Haar law actually supplied on a measurable subgroup; none is
silently postulated for arbitrary nonclosed subgroups (PDF pp.7,13,25). -/
def SubgroupHaarProbability (H : Set (Mat I)) (mu : Measure (Mat I)) : Prop :=
  UnitarySubgroup H ∧ MeasurableSet H ∧ IsProbabilityMeasure mu ∧
    mu Hᶜ = 0 ∧
    (∀ U ∈ H, Measure.map (fun V => U * V) mu = mu) ∧
    (∀ U ∈ H, Measure.map (fun V => V * U) mu = mu)

/-- Collective and local twirls (PDF pp.7,13,25). -/
def subgroupConjugationAverage (mu : Measure (Mat I)) (X : Mat I) : Mat I :=
  ∫ U, U * X * Uᴴ ∂mu

/-- Joint spectral measurement of generators, allowing projectors of rank
larger than one (PDF Proposition 9). -/
structure GeneratorSpectralPVM (A : StarSubalgebra ℂ (Mat I)) where
  count : ℕ
  projector : Fin count → Mat I
  hermitian : ∀ j, (projector j)ᴴ = projector j
  idempotent : ∀ j, projector j * projector j = projector j
  nonzero : ∀ j, projector j ≠ 0
  orthogonal : ∀ j k, j ≠ k → projector j * projector k = 0
  total : ∑ j, projector j = 1
  spans : Submodule.span ℂ (Set.range projector) = A.toSubalgebra.toSubmodule

/-- A stochastic classical rule after the fixed product spectral measurement.
The output space is arbitrary, and each input string has a probability law
(PDF pp.14,16-17). -/
def Postprocess {O : Type*} [MeasurableSpace O] {n : ℕ}
    {A : StarSubalgebra ℂ (Mat I)} (E : GeneratorSpectralPVM A)
    (K : (Fin n → Fin E.count) → Measure O)
    (M : Set O → Mat (Fin n → I)) : Prop :=
  (∀ z, IsProbabilityMeasure (K z)) ∧
    ∀ B, MeasurableSet B → M B =
      ∑ z, ((K z B).toReal : ℂ) • orderedTensorProduct (fun i => E.projector (z i))

/-- Rank-one density matrices: rank one, with positivity and trace one supplied
separately in a prior or state hypothesis (PDF pp.19-22). -/
def RankOne (rho : Mat I) : Prop := Matrix.rank rho = 1

/-- A probability law on density matrices, with a measurable full-measure
support and a finite vector of measurable parameters (PDF pp.17-20).
The support permits parameters to be constrained only where the prior lives. -/
structure EstimationPrior (I : Type*) [Fintype I] [DecidableEq I] (l : ℕ) where
  law : Measure (Mat I)
  probability : IsProbabilityMeasure law
  support : Set (Mat I)
  measurable_support : MeasurableSet support
  full_support : law supportᶜ = 0
  density : ∀ rho ∈ support, IsDensityMatrix rho
  parameter : Mat I → Fin l → ℝ
  measurable_parameter : Measurable parameter

/-- Invariance of the actual prior law, and pointwise invariance of parameters
on its support. This allows singular pure-state priors (PDF (5.4)-(5.5)). -/
def Symmetry {l : ℕ} (p : EstimationPrior I l) (H : Set (Mat I)) : Prop :=
  ∀ U ∈ H, Measure.map (fun rho => U * rho * Uᴴ) p.law = p.law ∧
    (∀ rho ∈ p.support, U * rho * Uᴴ ∈ p.support ∧
      p.parameter (U * rho * Uᴴ) = p.parameter rho)

/-- Pure support, not purity of an average state (PDF Theorem 11). -/
def PurePrior {l : ℕ} (p : EstimationPrior I l) : Prop :=
  ∀ rho ∈ p.support, RankOne rho

/-- Positive-probability parameter events. Order-convex measurable subsets of
R model intervals of every endpoint convention, including unbounded ones
(PDF pp.18-20,26). -/
def ParameterBox {l : ℕ} (D : Set (Fin l → ℝ)) : Prop :=
  ∃ J : Fin l → Set ℝ, (∀ i, MeasurableSet (J i) ∧ Set.OrdConnected (J i)) ∧
    D = Set.univ.pi J

/-- Equality of parameter-conditioned outcome laws for an arbitrary measurable
outcome space. The simulator is quantified outside all B,D and states. -/
def EquallyInformative {J O : Type*} [Fintype J] [MeasurableSpace O] {l : ℕ}
    (p : EstimationPrior I l) (input : Mat I → Mat J)
    (M N : Set O → Mat J) : Prop :=
  ∀ B, MeasurableSet B → ∀ D, ParameterBox D →
    0 < p.law (p.parameter ⁻¹' D) →
      (∫ rho in p.parameter ⁻¹' D, effectProb (M B) (input rho) ∂p.law) /
          (p.law (p.parameter ⁻¹' D)).toReal =
      (∫ rho in p.parameter ⁻¹' D, effectProb (N B) (input rho) ∂p.law) /
          (p.law (p.parameter ⁻¹' D)).toReal

/-- Image confined to an algebra, for measurable events only (PDF p.20). -/
def InAlgebra {J O : Type*} [Fintype J] [MeasurableSpace O]
    (M : Set O → Mat J) (A : Set (Mat J)) : Prop :=
  ∀ B, MeasurableSet B → M B ∈ A

/-- Noiselessness preserves all algebra observables on every density input;
no covariance of the physical channel is imposed (PDF (5.7)). -/
def Noiseless (A : Set (Mat I)) (E : Mat I → Mat I) : Prop :=
  ∀ rho, IsDensityMatrix rho → ∀ R ∈ A, (R * E rho).trace = (R * rho).trace

/-- Gauge distortion, using the covariance identity actually needed on
PDF pp.28-29: N(U rho U*)=U N(rho) U*. The printed p.20 identity omits the
output conjugation. The pure prior need not initially be invariant. -/
def Distortion {l : ℕ} (A : Set (Mat I)) (p : EstimationPrior I l)
    (N : Mat I → Mat I) : Prop :=
  IsChannel N ∧ Noiseless A N ∧
    (∀ U ∈ unitaryCentralizer A, ∀ X, N (U * X * Uᴴ) = U * N X * Uᴴ) ∧
    ∃ q : Measure (Mat I), IsProbabilityMeasure q ∧
      (∀ᵐ rho ∂q, IsDensityMatrix rho ∧ RankOne rho) ∧
      Measure.map N q = p.law

/-- Theorem 11 or 13 assumptions, for reuse in the merit statements (PDF p.21). -/
def EstimationAssumptions {l : ℕ} (A : Set (Mat I)) (n : ℕ)
    (p : EstimationPrior I l) (E : Mat (Fin n → I) → Mat (Fin n → I)) : Prop :=
  Symmetry p (unitaryCentralizer A) ∧ IsChannel E ∧
    ((E = id ∧ PurePrior p) ∨
      (Noiseless (tensorAlg n A) E ∧ ∃ N, Distortion A p N))

/-- Bilinear trace dual, computed on matrix units. For a physical channel this
is its Heisenberg adjoint, including on non-Hermitian matrices (PDF pp.21,28). -/
def heisenbergDual (E : Mat I → Mat I) (X : Mat I) : Mat I :=
  Matrix.of fun i j => (X * E (Matrix.single j i 1)).trace

/-- Physical block decomposition, including multiplicities and an actual
unitary change of basis (PDF (3.3)). Zero padded blocks are omitted. -/
structure BlockPresentation (I : Type*) [Fintype I] [DecidableEq I] where
  count : ℕ
  multiplicity : Fin count → ℕ
  dimension : Fin count → ℕ
  multiplicity_positive : ∀ j, 0 < multiplicity j
  dimension_positive : ∀ j, 0 < dimension j
  size : ∑ j, multiplicity j * dimension j = Fintype.card I
  change : Matrix I (Σ j : Fin count, Fin (multiplicity j) × Fin (dimension j)) ℂ
  left_unitary : change * changeᴴ = 1
  right_unitary : changeᴴ * change = 1

/-- The ordered physical embedding of direct sums I_m tensor V_n (PDF (3.3)). -/
def repeatedUnitaryBlocks {k : ℕ} (m n : Fin k → ℕ)
    (V : (j : Fin k) → Mat (Fin (n j))) :
    Mat (Σ j : Fin k, Fin (m j) × Fin (n j)) :=
  Matrix.of fun a b => if h : b.1 = a.1 then
    if a.2.1 = (h ▸ b.2).1 then V a.1 a.2.2 (h ▸ b.2).2 else 0 else 0

/-- Gauge subgroup realized by a block presentation (PDF (3.3)). -/
def BlockPresentation.group (b : BlockPresentation I) : Set (Mat I) :=
  {X | ∃ V : (j : Fin b.count) → Mat (Fin (b.dimension j)),
    (∀ j, (V j)ᴴ * V j = 1 ∧ V j * (V j)ᴴ = 1) ∧
    X = b.change * repeatedUnitaryBlocks b.multiplicity b.dimension V * b.changeᴴ}

/-- Unordered block multiplicities, the invariant in uniqueness up to unitary
equivalence; absent padded U(0) factors are not counted (PDF pp.6-7). -/
def BlockPresentation.signature (b : BlockPresentation I) : Multiset (ℕ × ℕ) :=
  ↑(List.ofFn fun j => (b.multiplicity j, b.dimension j))

/-- Regroup interleaved ordered pairs into left and right registers, then
apply the frozen actual partial trace over the right register (PDF p.14). -/
def traceRightRegister {L R : Type*} [Fintype R] {n : ℕ}
    (rho : Mat (Fin n → L × R)) : Mat (Fin n → L) :=
  traceRight (Matrix.of fun p q : (Fin n → L) × (Fin n → R) =>
    rho (fun i => (p.1 i, p.2 i)) (fun i => (q.1 i, q.2 i)))

/-- Identity on the complete right register, preserving coherences on the
left; factor order remains interleaved (PDF p.14). -/
def liftLeftRegister {L R : Type*} {n : ℕ} (X : Mat (Fin n → L)) :
    Mat (Fin n → L × R) :=
  Matrix.of fun x y => if (fun i => (x i).2) = (fun i => (y i).2) then
    X (fun i => (x i).1) (fun i => (y i).1) else 0

/-- PDF pp.21-22: equality of reductions, independent of a choice of basis. -/
def SameReduction (A : Set (Mat I)) (rho sigma : Mat I) : Prop :=
  ∀ X ∈ A, (rho * X).trace = (sigma * X).trace

/-- The source constructs the unital adjoint-closed algebra from its single
observable; it is not a free algebra with a representation hypothesis
(PDF pp.22,32). For Hermitian H this is Alg{H,I}. -/
def observableAlgebra (H : Mat I) : StarSubalgebra ℂ (Mat I) :=
  StarAlgebra.adjoin ℂ ({H} : Set (Mat I))

/-- Phase shifts with their scalar extension, in the number eigenbasis
(PDF pp.15-17). -/
def phaseGroup (d : ℕ) : Set (Mat (Fin d)) :=
  {U | ∃ a t : ℝ, U = Matrix.diagonal (fun i => Complex.exp (Complex.I * (a + t * i.val)))}

/-- Diagonal algebra in the chosen basis (PDF p.16). -/
def diagonalSet (I : Type*) [Fintype I] : Set (Mat I) :=
  {X | ∃ a : I → ℂ, X = Matrix.diagonal a}

/-- Computational basis kets on two systems, specialized from the frozen
ket at the ordered word ![a,b] (PDF pp.16-17). -/
def pairBasisKet (d : ℕ) (a b : Fin d) : EuclideanSpace ℂ (Fin 2 → Fin d) :=
  ket ![a,b]

/-- The ordered basis specialization retains the frozen normalized ket. -/
example (d : ℕ) (a b : Fin d) : pairBasisKet d a b = ket ![a,b] := rfl

/-- The two Bell vectors in the one-excitation sector (PDF p.16). -/
def bellSector (minus : Bool) : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    (pairBasisKet 2 0 1 + (if minus then (-1 : ℂ) else 1) • pairBasisKet 2 1 0)

/-- Explicit two-qubit classical kernel from PDF p.16. On 01 and 10 use the
Bell state of the chosen sign; 00 and 11 keep their basis state. -/
def qubitFilling (s : Bool) (z : Fin 2 → Fin 2) : Mat (Fin 2 → Fin 2) :=
  if z 0 = z 1 then pureDensity (pairBasisKet 2 (z 0) (z 1))
  else pureDensity (bellSector s)

/-- Normalized versions of the two nonorthogonal vectors printed on PDF p.17.
They are not an orthogonal projective basis. -/
def qutritVector (minus : Bool) : EuclideanSpace ℂ (Fin 2 → Fin 3) :=
  (Real.sqrt 3 : ℂ)⁻¹ • (pairBasisKet 3 1 1 +
    (if minus then (-1 : ℂ) else 1) • (pairBasisKet 3 0 2 + pairBasisKet 3 2 0))

/-- A genuine three-outcome POVM incorporating both source projectors after
scaling by 1/2; the third effect is the positive remainder (PDF p.17). -/
def qutritEffects : Fin 3 → Mat (Fin 2 → Fin 3) :=
  ![(1/2 : ℂ) • pureDensity (qutritVector false),
    (1/2 : ℂ) • pureDensity (qutritVector true),
    1 - (1/2 : ℂ) • pureDensity (qutritVector false) -
      (1/2 : ℂ) • pureDensity (qutritVector true)]

/-- Half-angle qubit states from the definition on PDF p.23. -/
def circleDensity (a theta : ℝ) : Mat (Fin 2) :=
  pureDensity (WithLp.toLp 2 ![(Real.cos (a/2) : ℂ),
    Complex.exp (Complex.I * theta) * Real.sin (a/2)])

/-- Common real dephasing family actually used in the example (PDF p.24). -/
def phaseFlipMixture (r : ℝ) (rho : Mat (Fin 2)) : Mat (Fin 2) :=
  (1-r : ℂ) • rho + (r : ℂ) •
    (Matrix.diagonal ![(1 : ℂ), -1] * rho * Matrix.diagonal ![(1 : ℂ), -1])

/-- Born diagonal uses half-angles; the last line on PDF p.23 loses /2.
At a=pi/2 this is I/2, as required by the state definition. -/
def circleDiagonal (a : ℝ) : Mat (Fin 2) :=
  Matrix.diagonal ![(Real.cos (a/2)^2 : ℂ), (Real.sin (a/2)^2 : ℂ)]

/-- A stochastic product-basis measurement (PDF pp.16-17,23-24). -/
def BasisProcessing {O : Type*} [MeasurableSpace O] (n : ℕ)
    (N : Measurements.OperatorPOVM (Fin n → Fin 2) O) : Prop :=
  ∃ K : (Fin n → Fin 2) → Measure O, (∀ z, IsProbabilityMeasure (K z)) ∧
    ∀ B, MeasurableSet B → N.operator B = Matrix.diagonal (fun z => ((K z B).toReal : ℂ))

/-- The concrete |00> and Bell vectors in the two-qubit decision problem
(PDF p.25), with the left register first. -/
def twoQubitSeed (b : Fin 2) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun x => if b = 0 then (if x = (0,0) then 1 else 0)
    else if x.1 ≠ x.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- Single-system right-unitary orbit, not independent draws on each copy
(PDF p.25). -/
def twoQubitOrbit (b : Fin 2) (V : Mat (Fin 2)) : Mat (Fin 2 × Fin 2) :=
  let U := Matrix.kronecker (1 : Mat (Fin 2)) V
  U * pureDensity (twoQubitSeed b) * Uᴴ

/-- The left marginal is |0><0| for b=0 and I/2 for b=1 (PDF p.25). -/
def decisionMarginal (b : Fin 2) : Mat (Fin 2) :=
  if b = 0 then Matrix.diagonal ![(1 : ℂ),0] else (1/2 : ℂ) • 1

/-- General conditional-law comparison, allowing the two independent states
in VI B to be the sample, rather than treating them as identical copies. -/
def SampleConditionals {X J O : Type*} [MeasurableSpace X] [Fintype J]
    [MeasurableSpace O] {l : ℕ} (mu : Measure X) (parameter : X → Fin l → ℝ)
    (input : X → Mat J) (M N : Set O → Mat J) : Prop :=
  ∀ B, MeasurableSet B → ∀ D, ParameterBox D → 0 < mu (parameter ⁻¹' D) →
    (∫ x in parameter ⁻¹' D, effectProb (M B) (input x) ∂mu) /
        (mu (parameter ⁻¹' D)).toReal =
      (∫ x in parameter ⁻¹' D, effectProb (N B) (input x) ∂mu) /
        (mu (parameter ⁻¹' D)).toReal

/-- Product of two independent, potentially different density matrices,
indexed in the same order as the sector projectors (PDF p.32). -/
def pairDensity (rho sigma : Mat I) : Mat (Fin 2 → I) :=
  orderedTensorProduct ![rho,sigma]

/-- Spin-one SU(2) image in a Cartesian orthonormal basis: the complexification
of SO(3). This is unitarily equivalent to the usual magnetic basis (PDF p.36). -/
def spinOneGroup : Set (Mat (Fin 3)) :=
  {U | ∃ R : Matrix (Fin 3) (Fin 3) ℝ,
    R.transpose * R = 1 ∧ R.det = 1 ∧ U = R.map Complex.ofReal}

/-- Spin-zero projector in Cartesian coordinates; the spin-one sector is the
antisymmetric sector and spin-two is the remaining symmetric sector (PDF p.36). -/
def spinZero : Mat (Fin 2 → Fin 3) :=
  pureDensity (WithLp.toLp 2 fun x => if x 0 = x 1 then (Real.sqrt 3 : ℂ)⁻¹ else 0)

/-- Scalar phase unitaries (PDF p.36). -/
def scalarUnitaries (I : Type*) [Fintype I] [DecidableEq I] : Set (Mat I) :=
  {X | ∃ z : ℂ, Complex.normSq z = 1 ∧ X = z • 1}

/-- The standard S3 isotypic projector, including all copies, from the
character (2,0,-1) on identity, transpositions, 3-cycles (PDF pp.37-39). -/
def standardSector (I : Type*) [Fintype I] : Mat (Fin 3 → I) :=
  (1/3 : ℂ) • ∑ s : Equiv.Perm (Fin 3),
    (if s = 1 then (2 : ℂ) else if (Equiv.Perm.sign s : ℤ) = -1 then 0 else -1) • perm I 3 s

/-- Local U(2) actions on the left and right single-system qubits
(PDF p.38). -/
def leftUnitaryGroup : Set (Mat (Fin 2 × Fin 2)) :=
  {X | ∃ U : Mat (Fin 2), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
    X = Matrix.kronecker U (1 : Mat (Fin 2))}

def rightUnitaryGroup : Set (Mat (Fin 2 × Fin 2)) :=
  {X | ∃ U : Mat (Fin 2), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
    X = Matrix.kronecker (1 : Mat (Fin 2)) U}

/-- A measurable Born kernel for the actual n-copy/channel experiment,
including continuous outcomes (PDF (5.1), (D2)-(D4)). -/
def BornKernel {O : Type*} [MeasurableSpace O] {l n : ℕ} (p : EstimationPrior I l)
    (E : Mat (Fin n → I) → Mat (Fin n → I))
    (M : Measurements.OperatorPOVM (Fin n → I) O)
    (K : ProbabilityTheory.Kernel (Mat I) O) : Prop :=
  ∀ rho ∈ p.support, ∀ B, MeasurableSet B →
    K rho B = ENNReal.ofReal (effectProb (M.operator B) (E (piKron n rho)))

/-- Joint estimated/true parameter law. No density for the parameter law
and no conditioning on a zero-probability atom is assumed (PDF Appendix D). -/
def parameterJoint {O : Type*} [MeasurableSpace O] {l : ℕ} (p : EstimationPrior I l)
    (K : ProbabilityTheory.Kernel (Mat I) O) : Measure (O × (Fin l → ℝ)) :=
  Measure.map (fun x => (x.2, p.parameter x.1)) (p.law.compProd K)

/-- Hand check: a number eigenstate at zero polar angle has population one. -/
example (theta : ℝ) : circleDensity 0 theta 0 0 = 1 := by
  simp [circleDensity, pureDensity]

/-- Hand check: the product seed for b=0 is exactly |00>. -/
example : twoQubitSeed 0 (0,0) = 1 := by simp [twoQubitSeed]

/-- Small-instance sanity: zero local factors have scalar identity entry. -/
example (V : Fin 0 → Mat I) (x y : Fin 0 → I) : orderedTensorProduct V x y = 1 := by
  simp [orderedTensorProduct]

/-- Small-instance sanity: the collective product is the frozen tensor power. -/
example (n : ℕ) (V : Mat I) : orderedTensorProduct (fun _ : Fin n => V) = piKron n V := rfl

/-- Hilbert-Schmidt coordinates use every entry, without a transpose. -/
example (X : Mat I) (i j : I) : hsVector X (i,j) = X i j := rfl

/-- The zero corner contains its unique zero endomorphism, even when the
full Hilbert space is nonzero. -/
example (S : Set (Mat I)) : (0 : Mat I) ∈ cornerComm 0 S := by
  simp [cornerComm]

/-- Identity channels are noiseless on every algebra. -/
example (A : Set (Mat I)) : Noiseless A id := by
  intro rho hrho R hR
  rfl

/-- Trace dual uses the transposed matrix-unit indices. -/
example (E : Mat I → Mat I) (X : Mat I) (i j : I) :
    heisenbergDual E X i j = (X * E (Matrix.single j i 1)).trace := rfl

/-- Each multiplicity copy carries precisely the same unitary block. -/
example {k : ℕ} (m n : Fin k → ℕ) (V : (j : Fin k) → Mat (Fin (n j)))
    (j : Fin k) (a : Fin (m j)) (b c : Fin (n j)) :
    repeatedUnitaryBlocks m n V ⟨j,(a,b)⟩ ⟨j,(a,c)⟩ = V j b c := by
  simp [repeatedUnitaryBlocks]

end QAlgorithms.Papers.Independent.Extend50.P37


