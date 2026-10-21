-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36
-- name    : QAlgorithms_Papers_Independent_Next46_P36
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:37:19.907952+00:00
-- url     : https://prove2.me/theorems/2e59d4af-48aa-4fdc-95ec-ab8b071802dd
-- title:
--   Definitions for Optimal estimation of group transformations using entanglement
-- statement:
--   The objects the formalized statements of *Optimal estimation of group transformations using entanglement* (arXiv:quant-ph/0506267) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BasedIrrep`: PDF pp.2-3: a positive-dimensional, based, continuous unitary irrep. Irreducibility means that the only invariant complex subspaces are zero and the whole space.
--   - `BasedIrrepEquivalent`: PDF p.2: equivalence of based representations, by an invertible intertwiner. The rectangular maps allow different presentations of the representation spaces.
--   - `OccurringIrrepsInequivalent`: PDF p.2: the labels in an occurring-irrep decomposition are inequivalent.
--   - `IrrepCatalog`: PDF pp.3,10: the complete unitary dual, with one based irrep per equivalence class. The catalog includes the trivial irrep and the conjugate/dual involution.
--   - `irrepVectorization`: PDF p.2 Eq.(1): row/output coordinate first, with no entrywise conjugation.
--   - `CanonicalIndex`: PDF p.4 Eq.(23): canonical representation-times-multiplicity coordinates.
--   - `canonicalAction`: PDF p.2 Eq.(5), with the canonical multiplicities of p.4 Eq.(21).
--   - `canonicalInput`: PDF p.4 Eq.(25): normalized iff the coefficients have squared moduli summing to one.
--   - `coefficientPhase`: PDF p.6 Eq.(39): the zero coefficient is assigned phase one.
--   - `likelihoodVector`: PDF p.6 Eq.(39): this vector is deliberately not a unit state.
--   - `rightAction`: PDF p.5 Eq.(29): complex conjugate, rather than adjoint, on the second factor.
--   - `representationRisk`: PDF p.3 Eq.(15): risk on an arbitrary actual finite register, also used by applications where an external reference is forbidden or the input is supplied.
--   - `RepresentationAdmissible`: PDF p.3: physical inputs and finite absolute joint cost on the actual register.
--   - `risk`: PDF p.3 Eqs.(14)-(15): the Haar-prior Bayes risk, with the measurement's own finite reference measure. No normalization of the Born weights is performed here.
--   - `CanonicalAdmissible`: PDF p.3: physical input and absolute integrability of the actual joint cost. This prevents Bochner's nonintegrable-default value from standing for a risk.
--   - `InvariantCost`: PDF pp.3-4: standard left AND right invariance (correcting the swapped arguments in printed Eq.(17), as required by the proof on p.5).
--   - `fourierCoefficient`: PDF pp.3-4 Eq.(18): the real coefficients for the conjugated-character convention, defined by their actual Haar Fourier pairing. This weak Fourier interpretation avoids imposing unjustified pointwise convergence on L1 costs.
--   - `HolevoCost`: PDF p.4: the generalized Holevo class, including an arbitrary trivial coefficient. A complete unitary dual is required; signs are checked on every nontrivial irrep.
--   - `couplingSpace`: PDF p.6 Eq.(42): actual intertwiners from sigma to mu tensor conjugate(nu). Their complex dimension is the tensor-product multiplicity, not an arbitrary array.
--   - `couplingMultiplicity`: PDF p.6 Eq.(42): Schur's lemma identifies this finrank with m_sigma^(mu,nu).
--   - `costMatrix`: PDF p.6 Eq.(42): only finitely many tensor-product constituents contribute, even if the cost has infinitely many Fourier coefficients.
--   - `quadraticCost`: PDF p.7: the normalized real-vector expectation of the cost matrix.
--   - `GlobalOptimal`: PDF pp.4-7: attainment, compared with every admissible density-matrix input and every measurement, independently chosen before the unknown group element.
--   - `NormalizedSeed`: PDF pp.5-6 Eqs.(27),(36): a legal covariant seed, using its continuous density.
--   - `componentVector`: PDF p.5 Eq.(33): spectral weights are absorbed in the vectors, which are not states.
--   - `componentSeed`: PDF p.5 Eq.(33): an arbitrary finite dyadic decomposition of the seed.
--   - `MultiplicityIndex`: PDF p.2 Eq.(4): physical multiplicity coordinates before the canonical reduction.
--   - `multiplicityAction`: PDF p.2 Eq.(5): the actual direct-sum action with physical multiplicities m.
--   - `BasedDecomposition`: PDF p.2 Eqs.(4)-(5): an exhaustive based unitary intertwiner for the actual representation. No character formula, multiplicity, or canonical embedding is assumed.
--   - `TensorRegister`: PDF pp.8-11: tensor-register coordinates; paired systems are regrouped A-first, B-second.
--   - `actualTensorRepresentation`: PDF pp.8,10 Eq.(72): the actual tensor-power action, in the fixed product basis.
--   - `tensorBell`: PDF pp.9,11 Eqs.(57),(74): the normalized supplied tensor-Bell vector.
--   - `bellAction`: PDF p.9 Eq.(58), in the regrouped order of the appendix.
--   - `bellEmbedding`: PDF p.11 Eq.(75): the actual canonical-memory embedding induced by the physical tensor representation's basis. The conjugation is on the B basis.
--   - `bellCoefficient`: PDF p.9 Eq.(60): weights are computed from the actual multiplicities of U^N, not the enlarged multiplicities m_mu*d^N of the bipartite representation.
--   - `bellCost`: PDF p.8 Eqs.(53)-(55): SINGLE-copy squared-overlap infidelity for d=2.
--   - `twiceSpin`: PDF pp.8-9: twice the allowed spin j; this treats both parities without half-integer truncation.
--   - `spinWeight`: PDF p.9 Eqs.(62)-(63), with the multiplicities from p.8 Eq.(48).
--   - `spinCostMatrix`: PDF p.9 Eq.(61), using the definition (42) of C. Correction to printed (64): the spin-zero diagonal is zero, since 0 tensor 0 has no spin-one constituent. Thus (65) needs the extra c_0^2/4 for even N. This has no effect on (67)-(68).
--   - `exactBellRisk`: PDF p.9 Eq.(61): the corrected sharp value for the supplied N-copy input.
--   - `optimalBellRisk`: PDF pp.8-9: the genuine optimum over ALL joint measurements of the supplied copies. The risk set is nonempty and lies in [0,1]; its infimum is not used as a surrogate for attainment, which is asserted explicitly in the finite-N theorem.
--   - `frameCost`: PDF pp.7-8 Eq.(45): Cartesian-axis error, using chi_1=|Tr U|^2-1. The central sign of SU(2) disappears from this SO(3) error.
--   - `optimalFrameRisk`: PDF p.8: the genuine no-external-reference optimum on N transmitted spins.
--   - `truncatedFrameProjector`: PDF p.8: remove only the top spin N/2, retaining ALL physical multiplicities in the remaining sectors. This is not an extension by a reference.
--   - `frameEmbedding`: PDF p.8 Eqs.(49)-(50): the canonical truncated subspace embedded in the ACTUAL N-spin space, using the first d_j available multiplicity coordinates. The conditional branch is never taken outside its valid range in the theorem.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, https://arxiv.org/abs/quant-ph/0506267v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Statements from Chiribella, D'Ariano and Sacchi, quant-ph/0506267v2.
All new objects are local to this paper. A density POVM may use ANY finite
reference measure, including atoms; the reference is not fixed to Haar for
competitors. In finite dimension every operator POVM admits such a density
with respect to its finite trace measure. Covariant outputs use Haar itself.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

local instance matrixMeasurable (I : Type*) [Fintype I] :
    MeasurableSpace (Matrix I I ℂ) := borel _

/-- PDF pp.2-3: a positive-dimensional, based, continuous unitary irrep.
Irreducibility means that the only invariant complex subspaces are zero and the whole space. -/
structure BasedIrrep (G : Type*) [Group G] [TopologicalSpace G] where
  dim : ℕ
  positive : 0 < dim
  matrix : G → Matrix (Fin dim) (Fin dim) ℂ
  one : matrix 1 = 1
  mul : ∀ g h, matrix (g * h) = matrix g * matrix h
  unitary : ∀ g, (matrix g)ᴴ * matrix g = 1 ∧ matrix g * (matrix g)ᴴ = 1
  continuous : Continuous matrix
  irreducible : ∀ V : Submodule ℂ (Fin dim → ℂ),
    (∀ g v, v ∈ V → (matrix g).mulVec v ∈ V) → V = ⊥ ∨ V = ⊤

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.2: equivalence of based representations, by an invertible intertwiner.
The rectangular maps allow different presentations of the representation spaces. -/
def BasedIrrepEquivalent (A B : BasedIrrep G) : Prop :=
  ∃ T : Matrix (Fin A.dim) (Fin B.dim) ℂ,
  ∃ S : Matrix (Fin B.dim) (Fin A.dim) ℂ,
    T * S = 1 ∧ S * T = 1 ∧ ∀ g, A.matrix g * T = T * B.matrix g

/-- PDF p.2: the labels in an occurring-irrep decomposition are inequivalent. -/
def OccurringIrrepsInequivalent {S : Type*} (D : S → BasedIrrep G) : Prop :=
  ∀ i j, i ≠ j → ¬ BasedIrrepEquivalent (D i) (D j)

/-- PDF pp.3,10: the complete unitary dual, with one based irrep per equivalence class.
The catalog includes the trivial irrep and the conjugate/dual involution. -/
structure IrrepCatalog (G : Type*) [Group G] [TopologicalSpace G] where
  Label : Type
  rep : Label → BasedIrrep G
  inequivalent : OccurringIrrepsInequivalent rep
  complete : ∀ A : BasedIrrep G, ∃ s, BasedIrrepEquivalent A (rep s)
  trivial : Label
  trivial_dim : (rep trivial).dim = 1
  trivial_matrix : ∀ g, (rep trivial).matrix g = 1
  dual : Label → Label
  dual_involutive : Function.Involutive dual
  dual_character : ∀ s g, ((rep (dual s)).matrix g).trace = conj (((rep s).matrix g).trace)

/-- PDF p.2 Eq.(1): row/output coordinate first, with no entrywise conjugation. -/
def irrepVectorization {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) :
    EuclideanSpace ℂ (Fin n × Fin m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

example {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (i : Fin n) (j : Fin m) :
    irrepVectorization A (i, j) = A i j := rfl

/-- PDF p.4 Eq.(23): canonical representation-times-multiplicity coordinates. -/
abbrev CanonicalIndex {S : Type*} (D : S → BasedIrrep G) :=
  (s : S) × (Fin (D s).dim × Fin (D s).dim)

/-- PDF p.2 Eq.(5), with the canonical multiplicities of p.4 Eq.(21). -/
def canonicalAction {S : Type*} [DecidableEq S] (D : S → BasedIrrep G) (g : G) :
    Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ :=
  Matrix.blockDiagonal' (fun s => (D s).matrix g ⊗ₖ (1 : Matrix (Fin (D s).dim) _ ℂ))

/-- PDF p.4 Eq.(25): normalized iff the coefficients have squared moduli summing to one. -/
def canonicalInput {S : Type*} (D : S → BasedIrrep G) (c : S → ℂ)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) :
    EuclideanSpace ℂ (CanonicalIndex D) :=
  WithLp.toLp 2 (fun p => c p.1 / (Real.sqrt (D p.1).dim : ℂ) *
    (W p.1 : Matrix _ _ ℂ) p.2.1 p.2.2)

/-- PDF p.6 Eq.(39): the zero coefficient is assigned phase one. -/
def coefficientPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

example : coefficientPhase 0 = 1 := by simp [coefficientPhase]

/-- PDF p.6 Eq.(39): this vector is deliberately not a unit state. -/
def likelihoodVector {S : Type*} (D : S → BasedIrrep G) (c : S → ℂ)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) :
    EuclideanSpace ℂ (CanonicalIndex D) :=
  WithLp.toLp 2 (fun p => (Real.sqrt (D p.1).dim : ℂ) * coefficientPhase (c p.1) *
    (W p.1 : Matrix _ _ ℂ) p.2.1 p.2.2)

/-- PDF p.5 Eq.(29): complex conjugate, rather than adjoint, on the second factor. -/
def rightAction {S : Type*} [DecidableEq S] (D : S → BasedIrrep G)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) (g : G) :
    Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ :=
  Matrix.blockDiagonal' (fun s => (1 : Matrix (Fin (D s).dim) _ ℂ) ⊗ₖ
    ((W s : Matrix _ _ ℂ)ᴴ * (D s).matrix g * (W s : Matrix _ _ ℂ)).map conj)

/-- PDF p.3 Eq.(15): risk on an arbitrary actual finite register, also used by
applications where an external reference is forbidden or the input is supplied. -/
def representationRisk {I : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace G]
    (U : G → Matrix I I ℂ) (dg : Measure G) (cost : G → G → ℝ)
    (rho : Matrix I I ℂ) (M : QAlgorithms.Measurements.DensityPOVM I G) : ℝ :=
  ∫ g, ∫ h, cost h g * QAlgorithms.effectProb (M.density h)
    (QAlgorithms.conjSuperop (U g) rho) ∂M.reference ∂dg

/-- PDF p.3: physical inputs and finite absolute joint cost on the actual register. -/
def RepresentationAdmissible {I : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace G]
    (U : G → Matrix I I ℂ) (dg : Measure G) (cost : G → G → ℝ)
    (rho : Matrix I I ℂ) (M : QAlgorithms.Measurements.DensityPOVM I G) : Prop :=
  QAlgorithms.IsDensityMatrix rho ∧
  Integrable (fun p : G × G => cost p.2 p.1 * QAlgorithms.effectProb (M.density p.2)
    (QAlgorithms.conjSuperop (U p.1) rho)) (dg.prod M.reference)

/-- PDF p.3 Eqs.(14)-(15): the Haar-prior Bayes risk, with the measurement's own
finite reference measure. No normalization of the Born weights is performed here. -/
def risk {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace G]
    (D : S → BasedIrrep G) (dg : Measure G) (cost : G → G → ℝ)
    (rho : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G) : ℝ :=
  representationRisk (canonicalAction D) dg cost rho M

/-- PDF p.3: physical input and absolute integrability of the actual joint cost.
This prevents Bochner's nonintegrable-default value from standing for a risk. -/
def CanonicalAdmissible {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace G]
    (D : S → BasedIrrep G) (dg : Measure G) (cost : G → G → ℝ)
    (rho : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G) : Prop :=
  RepresentationAdmissible (canonicalAction D) dg cost rho M

/-- PDF pp.3-4: standard left AND right invariance (correcting the swapped
arguments in printed Eq.(17), as required by the proof on p.5). -/
def InvariantCost {K : Type*} (cost : G → G → K) : Prop :=
  (∀ h g k, cost (k * h) (k * g) = cost h g) ∧
  (∀ h g k, cost (h * k) (g * k) = cost h g)

/-- PDF pp.3-4 Eq.(18): the real coefficients for the conjugated-character
convention, defined by their actual Haar Fourier pairing. This weak Fourier
interpretation avoids imposing unjustified pointwise convergence on L1 costs. -/
def fourierCoefficient [MeasurableSpace G] (dg : Measure G) (cost : G → G → ℝ)
    (A : BasedIrrep G) : ℂ :=
  ∫ g, (cost g 1 : ℂ) * (A.matrix g).trace ∂dg

/-- PDF p.4: the generalized Holevo class, including an arbitrary trivial coefficient.
A complete unitary dual is required; signs are checked on every nontrivial irrep. -/
def HolevoCost [MeasurableSpace G] (dg : Measure G) (K : IrrepCatalog G)
    (cost : G → G → ℝ) : Prop :=
  InvariantCost cost ∧ Measurable (Function.uncurry cost) ∧
  Integrable (fun g => cost g 1) dg ∧
  (∀ s, (fourierCoefficient dg cost (K.rep s)).im = 0) ∧
  (∀ s, s ≠ K.trivial → (fourierCoefficient dg cost (K.rep s)).re ≤ 0) ∧
  (∀ s, fourierCoefficient dg cost (K.rep (K.dual s)) = fourierCoefficient dg cost (K.rep s))

/-- PDF p.6 Eq.(42): actual intertwiners from sigma to mu tensor conjugate(nu).
Their complex dimension is the tensor-product multiplicity, not an arbitrary array. -/
def couplingSpace (A B C : BasedIrrep G) :
    Submodule ℂ (Matrix (Fin A.dim × Fin B.dim) (Fin C.dim) ℂ) where
  carrier := {T | ∀ g, (A.matrix g ⊗ₖ (B.matrix g).map conj) * T = T * C.matrix g}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS g
    simp only [Matrix.mul_add, Matrix.add_mul, hT g, hS g]
  smul_mem' := by
    intro a T hT g
    simp only [Matrix.mul_smul, Matrix.smul_mul, hT g]

/-- PDF p.6 Eq.(42): Schur's lemma identifies this finrank with m_sigma^(mu,nu). -/
def couplingMultiplicity (A B C : BasedIrrep G) : ℕ :=
  Module.finrank ℂ (couplingSpace A B C)

/-- PDF p.6 Eq.(42): only finitely many tensor-product constituents contribute,
even if the cost has infinitely many Fourier coefficients. -/
def costMatrix {S : Type*} [MeasurableSpace G] (D : S → BasedIrrep G)
    (dg : Measure G) (K : IrrepCatalog G) (cost : G → G → ℝ) : Matrix S S ℝ :=
  fun i j => ∑' s : K.Label, if s = K.trivial then 0 else
    (fourierCoefficient dg cost (K.rep s)).re * couplingMultiplicity (D i) (D j) (K.rep s)

/-- PDF p.7: the normalized real-vector expectation of the cost matrix. -/
def quadraticCost {S : Type*} [Fintype S] (C : Matrix S S ℝ) (v : S → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * C i j * v j

/-- PDF pp.4-7: attainment, compared with every admissible density-matrix input
and every measurement, independently chosen before the unknown group element. -/
def GlobalOptimal {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace G]
    (D : S → BasedIrrep G) (dg : Measure G) (cost : G → G → ℝ)
    (rho : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G) : Prop :=
  CanonicalAdmissible D dg cost rho M ∧ ∀ tau N, CanonicalAdmissible D dg cost tau N →
    risk D dg cost rho M ≤ risk D dg cost tau N

/-- PDF pp.5-6 Eqs.(27),(36): a legal covariant seed, using its continuous density. -/
def NormalizedSeed {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace G]
    (D : S → BasedIrrep G) (dg : Measure G)
    (Xi : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) : Prop :=
  Xi.PosSemidef ∧ Continuous (fun g => QAlgorithms.conjSuperop (canonicalAction D g) Xi) ∧
  Integrable (fun g => QAlgorithms.conjSuperop (canonicalAction D g) Xi) dg ∧
  (∫ g, QAlgorithms.conjSuperop (canonicalAction D g) Xi ∂dg) = 1

/-- PDF p.5 Eq.(33): spectral weights are absorbed in the vectors, which are not states. -/
def componentVector {S : Type*} (D : S → BasedIrrep G)
    (A : ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) :
    EuclideanSpace ℂ (CanonicalIndex D) :=
  WithLp.toLp 2 (fun p => (Real.sqrt (D p.1).dim : ℂ) * A p.1 p.2.1 p.2.2)

/-- PDF p.5 Eq.(33): an arbitrary finite dyadic decomposition of the seed. -/
def componentSeed {S : Type*} (D : S → BasedIrrep G) {r : ℕ}
    (A : Fin r → ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) :
    Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ :=
  ∑ i, QAlgorithms.pureDensity (componentVector D (A i))

example {S : Type*} (D : S → BasedIrrep G) :
    componentSeed D (r := 0) (fun i => Fin.elim0 i) = 0 := by
  simp [componentSeed]

/-- PDF p.2 Eq.(4): physical multiplicity coordinates before the canonical reduction. -/
abbrev MultiplicityIndex {S : Type*} (D : S → BasedIrrep G) (m : S → ℕ) :=
  (s : S) × (Fin (D s).dim × Fin (m s))

/-- PDF p.2 Eq.(5): the actual direct-sum action with physical multiplicities m. -/
def multiplicityAction {S : Type*} [DecidableEq S]
    (D : S → BasedIrrep G) (m : S → ℕ) (g : G) :
    Matrix (MultiplicityIndex D m) (MultiplicityIndex D m) ℂ :=
  Matrix.blockDiagonal' (fun s => (D s).matrix g ⊗ₖ (1 : Matrix (Fin (m s)) _ ℂ))

/-- PDF p.2 Eqs.(4)-(5): an exhaustive based unitary intertwiner for the actual
representation. No character formula, multiplicity, or canonical embedding is assumed. -/
structure BasedDecomposition {I S : Type*} [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] (U : G → Matrix I I ℂ) (D : S → BasedIrrep G) where
  multiplicity : S → ℕ
  positive : ∀ s, 0 < multiplicity s
  basis : Matrix I (MultiplicityIndex D multiplicity) ℂ
  isometry : basisᴴ * basis = 1
  exhaustive : basis * basisᴴ = 1
  intertwines : ∀ g, U g * basis = basis * multiplicityAction D multiplicity g

/-- PDF pp.8-11: tensor-register coordinates; paired systems are regrouped A-first, B-second. -/
abbrev TensorRegister (d N : ℕ) := Fin N → Fin d

/-- PDF pp.8,10 Eq.(72): the actual tensor-power action, in the fixed product basis. -/
def actualTensorRepresentation (d N : ℕ) (g : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    Matrix (TensorRegister d N) (TensorRegister d N) ℂ :=
  fun a b => ∏ k, (g : Matrix (Fin d) (Fin d) ℂ) (a k) (b k)

/-- PDF pp.9,11 Eqs.(57),(74): the normalized supplied tensor-Bell vector. -/
def tensorBell (d N : ℕ) :
    EuclideanSpace ℂ (TensorRegister d N × TensorRegister d N) :=
  WithLp.toLp 2 (fun p => if p.1 = p.2 then (Real.sqrt ((d : ℝ) ^ N) : ℂ)⁻¹ else 0)

/-- PDF p.9 Eq.(58), in the regrouped order of the appendix. -/
def bellAction (d N : ℕ) (g : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    Matrix (TensorRegister d N × TensorRegister d N)
      (TensorRegister d N × TensorRegister d N) ℂ :=
  actualTensorRepresentation d N g ⊗ₖ (1 : Matrix (TensorRegister d N) _ ℂ)

example (d : ℕ) (g : Matrix.specialUnitaryGroup (Fin d) ℂ) (a b : TensorRegister d 0) :
    actualTensorRepresentation d 0 g a b = 1 := by simp [actualTensorRepresentation]

/-- PDF p.11 Eq.(75): the actual canonical-memory embedding induced by the
physical tensor representation's basis. The conjugation is on the B basis. -/
def bellEmbedding {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ)) (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    Matrix (TensorRegister d N × TensorRegister d N) (CanonicalIndex D) ℂ :=
  fun p q => (Real.sqrt (B.multiplicity q.1) : ℂ)⁻¹ *
    ∑ k : Fin (B.multiplicity q.1),
      B.basis p.1 ⟨q.1, (q.2.1, k)⟩ * conj (B.basis p.2 ⟨q.1, (q.2.2, k)⟩)

/-- PDF p.9 Eq.(60): weights are computed from the actual multiplicities of U^N,
not the enlarged multiplicities m_mu*d^N of the bipartite representation. -/
def bellCoefficient {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ)) (B : BasedDecomposition (actualTensorRepresentation d N) D) (s : S) : ℝ :=
  Real.sqrt (((D s).dim : ℝ) * B.multiplicity s / (d : ℝ) ^ N)

/-- PDF p.8 Eqs.(53)-(55): SINGLE-copy squared-overlap infidelity for d=2. -/
def bellCost (h g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  1 - Complex.normSq (((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
    (h : Matrix (Fin 2) (Fin 2) ℂ)).trace) / 4

/-- PDF pp.8-9: twice the allowed spin j; this treats both parities without half-integer truncation. -/
def twiceSpin (N : ℕ) (k : Fin (N / 2 + 1)) : ℕ := N % 2 + 2 * k.val

/-- PDF p.9 Eqs.(62)-(63), with the multiplicities from p.8 Eq.(48). -/
def spinWeight (N : ℕ) (k : Fin (N / 2 + 1)) : ℝ :=
  ((twiceSpin N k + 1 : ℕ) : ℝ) * Real.sqrt
    ((Nat.choose N ((N + twiceSpin N k) / 2) : ℝ) /
      ((2 : ℝ) ^ N * (((N + twiceSpin N k) / 2 + 1 : ℕ) : ℝ)))

/-- PDF p.9 Eq.(61), using the definition (42) of C. Correction to printed (64):
the spin-zero diagonal is zero, since 0 tensor 0 has no spin-one constituent.
Thus (65) needs the extra c_0^2/4 for even N. This has no effect on (67)-(68). -/
def spinCostMatrix (N : ℕ) : Matrix (Fin (N / 2 + 1)) (Fin (N / 2 + 1)) ℝ :=
  fun i j => -(1 / 4 : ℝ) *
    ((if i = j ∧ 0 < twiceSpin N i then 1 else 0) +
      (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0))

/-- PDF p.9 Eq.(61): the corrected sharp value for the supplied N-copy input. -/
def exactBellRisk (N : ℕ) : ℝ :=
  3 / 4 + quadraticCost (spinCostMatrix N) (spinWeight N)

/-- PDF pp.8-9: the genuine optimum over ALL joint measurements of the supplied
copies. The risk set is nonempty and lies in [0,1]; its infimum is not used as
a surrogate for attainment, which is asserted explicitly in the finite-N theorem. -/
def optimalBellRisk [MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] (dg : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ)) (N : ℕ) : ℝ :=
  sInf {r | ∃ M : QAlgorithms.Measurements.DensityPOVM
    (TensorRegister 2 N × TensorRegister 2 N) (Matrix.specialUnitaryGroup (Fin 2) ℂ),
    RepresentationAdmissible (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) M ∧
    r = representationRisk (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) M}

/-- PDF pp.7-8 Eq.(45): Cartesian-axis error, using chi_1=|Tr U|^2-1.
The central sign of SU(2) disappears from this SO(3) error. -/
def frameCost (h g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  8 - 2 * Complex.normSq (((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
    (h : Matrix (Fin 2) (Fin 2) ℂ)).trace)

/-- PDF p.8: the genuine no-external-reference optimum on N transmitted spins. -/
def optimalFrameRisk [MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] (dg : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ)) (N : ℕ) : ℝ :=
  sInf {r | ∃ rho : Matrix (TensorRegister 2 N) (TensorRegister 2 N) ℂ,
    ∃ M : QAlgorithms.Measurements.DensityPOVM (TensorRegister 2 N) (Matrix.specialUnitaryGroup (Fin 2) ℂ),
      RepresentationAdmissible (actualTensorRepresentation 2 N) dg frameCost rho M ∧
      r = representationRisk (actualTensorRepresentation 2 N) dg frameCost rho M}

/-- PDF p.8: remove only the top spin N/2, retaining ALL physical multiplicities
in the remaining sectors. This is not an extension by a reference. -/
def truncatedFrameProjector {N : ℕ}
    (D : Fin (N / 2 + 1) → BasedIrrep (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation 2 N) D) :
    Matrix (TensorRegister 2 N) (TensorRegister 2 N) ℂ :=
  B.basis * Matrix.blockDiagonal' (fun k =>
    if k.val < N / 2 then (1 : Matrix (Fin (D k).dim × Fin (B.multiplicity k)) _ ℂ)
    else 0) * B.basisᴴ

/-- PDF p.8 Eqs.(49)-(50): the canonical truncated subspace embedded in the
ACTUAL N-spin space, using the first d_j available multiplicity coordinates.
The conditional branch is never taken outside its valid range in the theorem. -/
def frameEmbedding {N : ℕ}
    (D : Fin (N / 2 + 1) → BasedIrrep (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation 2 N) D) :
    Matrix (TensorRegister 2 N) (CanonicalIndex (fun k : Fin (N / 2) => D k.castSucc)) ℂ :=
  fun a q => if h : q.2.2.val < B.multiplicity q.1.castSucc then
    B.basis a ⟨q.1.castSucc, (q.2.1, ⟨q.2.2.val, h⟩)⟩ else 0

end QAlgorithms.Papers.Independent.Next46.P36


