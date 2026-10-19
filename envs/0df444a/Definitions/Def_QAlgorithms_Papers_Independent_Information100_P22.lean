-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
-- name    : QAlgorithms_Papers_Independent_Information100_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:46:18.892898+00:00
-- url     : https://prove2.me/theorems/7d6a1ab2-a14d-44c7-8997-20c349d906ed
-- title:
--   Definitions for Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning
-- statement:
--   The objects the formalized statements of *Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning* (arXiv:2609.28241) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Op`
--   - `Wires`
--   - `Signals`
--   - `Full`
--   - `mixed`: PDF p.3: maximally mixed operator on the named register.
--   - `bell`: PDF p.3: normalized Bell vector.
--   - `rhoS`: PDF p.3: resource signal marginal.
--   - `rhoN`: PDF p.3: resource common-key marginal.
--   - `encoding`: PDF pp.3,10: encoding isometry computed from R and the AS operator; N is untouched.
--   - `encoded`: PDF p.3: encoded channel on every operator.
--   - `Rest`
--   - `joinSignal`: Reinsert the prescribed output into its complementary signal configuration.
--   - `authorized`: PDF p.3: Q_i outputs exactly S_i and the full common key N.
--   - `individual`: PDF p.3: channel on one individual output.
--   - `jointSignals`: PDF p.4: channel on the complete signal register.
--   - `Recoverable`: PDF p.3: a finite CPTP decoder fixed before all input operators.
--   - `AllRecoverable`: PDF p.3: recovery from every prescribed output.
--   - `Concealed`: PDF p.3: concealment with an arbitrary fixed output density matrix.
--   - `UniformlyConcealed`: PDF pp.4,6: individual channels are completely depolarizing.
--   - `omega`: PDF p.3: normalized encoded Choi vector.
--   - `referenceComplement`: PDF p.19: reference and complementary AS_(not i) Choi marginal.
--   - `quantumMI`: Quantum mutual information in bits; used only on computed density matrices.
--   - `sourceMarginal`: PDF pp.5,27: transformed source marginal at the maximally mixed Choi input.
--   - `Axis`: PDF p.2: the named Pauli axes.
--   - `axisMatrix`: PDF p.2: accepted Pauli matrices.
--   - `remaining`: PDF p.4: signed R=iPQ.
--   - `tensorOps`: Finite tensor product over named qubits.
--   - `quarterRotation`: PDF p.2: exp(-i pi M/4) for a Hermitian involution M.
--   - `sectorEncoder`: PDF p.2: one sector; the Q factor acts first.
--   - `twoPauliEncoder`: PDF p.2: tensor product of the k sector encoders.
--   - `sectorMoment`: PDF p.4: T(c), the signed complete-sector observable.
--   - `inputMoment`: PDF p.4: input R_A(c) observable.
--   - `oddForm`: PDF p.4, Eq.(3): odd-m expansion with real coefficients, normalization, and positivity.
--   - `ResourceCriterion`: PDF p.4: algebraic criterion, without assuming recovery.
--   - `marginal`: PDF p.43: marginal on selected coordinates; discarded coordinates agree on bra and ket.
--   - `F2`
--   - `CutGraph`: PDF pp.6,28: finite simple graph in a fixed oriented balanced cut and Pauli frame.
--   - `bit`: A computational bit as a binary field element.
--   - `quadratic`: PDF p.36: graph quadratic phase, counting each edge once.
--   - `graphVector`: PDF p.35, Eq.(S47): standard positive graph-state convention.
--   - `cutKernel`: PDF p.7: complete cut kernel over F₂, not merely its dimension.
--   - `sectorIndicator`: PDF p.7: sector-indicator map F.
--   - `exceptionalX`: PDF p.7, Eq.(6): ambient X-type exceptional space.
--   - `exceptionalY`: PDF p.7, Eq.(6): ambient Y-type exceptional space; sector parity is explicit.
--   - `classXZ`: Encoder classes keep the ordered axes in the encoder itself.
--   - `classYZ`
--   - `classXY`
--   - `exceptionalSpace`: PDF p.7, Eq.(6): ambient E, independent of the cut kernel.
--   - `signalGenerator`: PDF pp.6,29: signed signal stabilizer generator; multiplication preserves graph signs.
--   - `signalStabilizer`: PDF p.29: signed K_S(x), never replaced by an unsigned X^x Z^(AS x).
--   - `ExceptionalVector`: PDF p.7, Definition 1: support only on A after forward conjugation.
--   - `graphProjector`: PDF p.29: normalized sum of the signal-only stabilizer subgroup.
--   - `HasConstantSectors`: PDF p.33: an ordered sector assignment of exactly m vertices in each of k sectors.
--   - `czLayer`: PDF p.11: CZ layer induced by a binary graph adjacency.
--   - `linearLayer`: PDF p.11: reversible binary map |x> ↦ |Mx>; used with invertible M.
--   - `bellNormalizer`: PDF p.11, Eq.(9): rightmost CZ_AN, then H, then B^(-T), then CZ_AS.
--   - `RegisterClifford`: Clifford normalizer on a named qubit register, including fourth-root Pauli phases.
--   - `SingleClifford`: PDF p.11: a one-qubit unitary is Clifford exactly when it permutes signed axes.
--   - `LocalCliffordPermutation`: PDF p.11: local Clifford product up to a wire permutation.
--   - `BinaryPermutation`: Binary permutation matrix in the chosen signal/noise orderings.
--   - `rankTwoExample`: PDF p.12 and Eq.(S54), p.39: fixed rank-two cut, zero internal adjacencies.
--   - `regroupResource`: PDF p.24: regroup a fixed physical resource by the same coordinate bijection on each side.
--   - `SpectralForm`: PDF pp.6,28: explicit unitary spectral form on d times L dimensions.
--   - `DivisibleEigenmultiplicities`: PDF p.6: every eigenvalue, including a zero eigenvalue when present, has L-divisible multiplicity.
--   - `directionMatrix`: PDF p.20: identity or a nonidentity Pauli direction.
--   - `remainingAxis`: PDF p.20: the axis complementary to the distinct ordered axes; signs omitted only for support.
--   - `SourceOnly`: PDF p.20: trivial total signal support, with arbitrary action on the source.
--   - `HasSignalDirection`: PDF p.20: restriction of a tensor operator to a specified signal position.
--   - `dicke`: PDF pp.42–43: normalized computational Dicke vector, zero on infeasible excitation inputs.
--   - `dickeResource`: PDF p.43: same Dicke vector in any balanced signal/noise coordinates.
--   - `dickeLambda`: PDF p.43: lambda_j are probabilities, not Schmidt amplitudes.
--   - `dickeEntropy`: PDF pp.43–44: Shannon entropy of the feasible excitation probabilities in bits.
--   - `twoQubitMarginal`: PDF p.43: marginal on two distinct qubits with the ordered computational basis 00,01,10,11.
--   - `dickePairFormula`: PDF p.43, Eq.(S70): coefficients use real subtraction, even at r=0 and r=n.
--   - `omegaFour`: PDF pp.5,25: four qudits are ordered reference, transformed A, S, N.
--   - `AMEFour`: PDF p.25: AME(4,d) means unit norm and all six two-party marginals maximally mixed.
--   - `fieldEncoder`: PDF p.25: explicit finite-field encoder, over F_(2^k), rather than coordinatewise F₂.
--   - `fieldDecoder`: Eq.(S18), PDF p.25: both decoder outputs, with distinct linear combinations.
--   - `fieldChoi`: Eq.(S17), PDF p.25: normalized 1/d AME amplitudes.
--   - `fieldAuthorized`: PDF p.25: authorized channel obtained by tracing transformed A from the Bell-resource encoding.
--   - `AuthorizedPauli`: PDF p.10: a Pauli observable on S_i N, with its fourth-root phase.
--   - `AuthorizedClifford`: PDF p.10: Clifford normalizer of the full authorized Pauli group.
--   - `logicalAxis`: PDF p.10: source/input Pauli on the jth logical qubit.
--   - `liftAuthorized`: PDF p.10: lift an authorized operator, acting identically on the entire erased complement.
--   - `LabeledGraph`: Graph on a fixed labeled vertex set. All cuts and sectorings will be chosen explicitly.
--   - `realize`: PDF pp.9,33: the bijection chooses a balanced cut and an ordered sector decomposition at once.
--   - `GSECC`: PDF p.9, Eq.(8): existential graph-level GSECC decision, not failure of one cut.
--   - `undirectedGraph`: Make an undirected simple graph from an edge prescription, deleting loops.
--   - `matchingGraph`: PDF p.38: consecutive pairs form a perfect matching.
--   - `pathGraph`: PDF p.38: path P_(2nu) with vertices 0,...,2nu-1.
--   - `cycleGraph`: PDF p.38: cycle C_(2nu), used only for nu>=2.
--   - `rectangularGraph`: PDF pp.38–39: row-major rectangular cluster with 2a rows and b columns.
--   - `completeGraph`: PDF p.39: complete and star families.
--   - `starGraph`
--   - `sparseCutMatrix`: Original PDF p.42, Eq.(S65), read directly in the original PDF. No sampled graph is inferred.
--   - `densityPurification`: Canonical purification of a density operator, reference first. The input marginal is rho.
--   - `coherentInformation`: PDF p.3: coherent information of a channel at rho, via a purification.
--   - `singleUseInformation`: PDF p.3: optimized single-use coherent information, over all density inputs. For finite nonempty registers and channels the value set is nonempty and bounded.
--   - `quantumCapacity`: PDF p.3, refs.[34–36]: quantum capacity via regularized optimized coherent information. Devetak, quant-ph/0304127, Theorem 5 / Proposition 7 identifies this with unassisted quantum capacity. Positive block lengths only; the superadditive regularization is written as a supremum.
--   - `BellGate`: PDF pp.11,37–38: elementary Clifford gates with arbitrary wire connectivity.
--   - `BellGate.Legal`: Exclude repeated control/target endpoints as required by the elementary gate set.
--   - `BellGate.matrix`: Exact gate matrices; an H acts only on its named wire, CNOT uses the first wire as control.
--   - `bellWordMatrix`: Chronological gate list: first element acts first. Size is the actual list length.
--   - `reindexCut`: Reindex both sides of a fixed cut; this is coordinate relabelling, not a physical operation.
--   - `FixedCutAdmissible`: PDF pp.33–34: fixed-cut acceptance searches only for a compatible sector assignment.
--   - `axisCode`: Lossless encoder of ordered axes for the counted RAM input.
--   - `matrixWords`: Row-major binary matrix input; all n² entries are supplied, no graph certificate is assumed.
--   - `fixedCutInput`: Fixed-cut machine input header followed by AS, B, AN.
--   - `graphInput`: Graph-level machine input header followed by the complete labeled adjacency matrix.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, https://arxiv.org/abs/2609.28241v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_ClassicalDecoderMachines

/-! Paper-local definitions and statements for arXiv:2609.28241v1.
Coordinates are (sector, position), key wires independent of signal wires.
Compilation and independent moderation are pending. -/

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Op (I : Type*) := Matrix I I ℂ

abbrev Wires (m k : ℕ) := Fin k × Fin m

abbrev Signals (m k : ℕ) := Wires m k → Bool

abbrev Full (m k : ℕ) := (Qubits k × Signals m k) × Signals m k

/-- PDF p.3: maximally mixed operator on the named register. -/
def mixed (I : Type*) [Fintype I] [DecidableEq I] : Op I :=
  (Fintype.card I : ℂ)⁻¹ • 1

/-- PDF p.3: normalized Bell vector. -/
def bell (I : Type*) [Fintype I] [DecidableEq I] : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then
    ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.3: resource signal marginal. -/
def rhoS {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k)) :=
  traceRight (pureDensity R)

/-- PDF p.3: resource common-key marginal. -/
def rhoN {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k)) :=
  traceLeft (pureDensity R)

/-- PDF pp.3,10: encoding isometry computed from R and the AS operator; N is untouched. -/
def encoding {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : Matrix (Full m k) (Qubits k) ℂ :=
  fun y a => ∑ s, U y.1 (a,s) * R (s,y.2)

/-- PDF p.3: encoded channel on every operator. -/
def encoded {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (X : Op (Qubits k)) : Op (Full m k) :=
  encoding R U * X * (encoding R U)ᴴ

abbrev Rest (m k : ℕ) (i : Fin m) := {w : Wires m k // w.2 ≠ i} → Bool

/-- Reinsert the prescribed output into its complementary signal configuration. -/
def joinSignal {m k : ℕ} (i : Fin m) (b : Qubits k) (t : Rest m k i) : Signals m k :=
  fun w => if h : w.2 = i then b w.1 else t ⟨w,h⟩

/-- PDF p.3: Q_i outputs exactly S_i and the full common key N. -/
def authorized {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (i : Fin m) :
    Superop (Qubits k) (Qubits k × Signals m k) :=
  fun X p q => ∑ a : Qubits k, ∑ t : Rest m k i,
    encoded R U X ((a,joinSignal i p.1 t),p.2) ((a,joinSignal i q.1 t),q.2)

/-- PDF p.3: channel on one individual output. -/
def individual {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (i : Fin m) : Superop (Qubits k) (Qubits k) :=
  fun X => traceRight (authorized R U i X)

/-- PDF p.4: channel on the complete signal register. -/
def jointSignals {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (X : Op (Qubits k)) : Op (Signals m k) :=
  traceLeft (traceRight (encoded R U X))

/-- PDF p.3: a finite CPTP decoder fixed before all input operators. -/
def Recoverable {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (i : Fin m) : Prop :=
  ∃ D : Superop (Qubits k × Signals m k) (Qubits k), IsChannel D ∧
    ∀ X, D (authorized R U i X) = X

/-- PDF p.3: recovery from every prescribed output. -/
def AllRecoverable {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : Prop := ∀ i, Recoverable R U i

/-- PDF p.3: concealment with an arbitrary fixed output density matrix. -/
def Concealed {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (i : Fin m) : Prop :=
  ∃ tau : Op (Qubits k), IsDensityMatrix tau ∧ ∀ X, individual R U i X = X.trace • tau

/-- PDF pp.4,6: individual channels are completely depolarizing. -/
def UniformlyConcealed {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : Prop :=
  ∀ i X, individual R U i X = X.trace • mixed (Qubits k)

/-- PDF p.3: normalized encoded Choi vector. -/
def omega {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : EuclideanSpace ℂ (Qubits k × Full m k) :=
  WithLp.toLp 2 fun p => ((Real.sqrt ((2 : ℝ)^k))⁻¹ : ℂ) * encoding R U p.2 p.1

/-- PDF p.19: reference and complementary AS_(not i) Choi marginal. -/
def referenceComplement {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (i : Fin m) :
    Op (Qubits k × (Qubits k × Rest m k i)) :=
  fun p q => ∑ b : Qubits k, ∑ n : Signals m k,
    pureDensity (omega R U) (p.1,((p.2.1,joinSignal i b p.2.2),n))
      (q.1,((q.2.1,joinSignal i b q.2.2),n))

/-- Quantum mutual information in bits; used only on computed density matrices. -/
def quantumMI {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Op (I × J)) : ℝ := vnEntropy (traceRight X) + vnEntropy (traceLeft X) - vnEntropy X

/-- PDF pp.5,27: transformed source marginal at the maximally mixed Choi input. -/
def sourceMarginal {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : Op (Qubits k) :=
  traceRight (traceRight (encoded R U (mixed (Qubits k))))

/-- PDF p.2: the named Pauli axes. -/
inductive Axis where
  | X | Y | Z
  deriving DecidableEq

/-- The three Pauli axes, enumerated explicitly to avoid derived-instance transparency issues. -/
instance : Fintype Axis where
  elems := {.X, .Y, .Z}
  complete := by intro a; cases a <;> simp

/-- PDF p.2: accepted Pauli matrices. -/
def axisMatrix : Axis → Op Bool
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

/-- PDF p.4: signed R=iPQ. -/
def remaining (P Q : Axis) : Op Bool := Complex.I • (axisMatrix P * axisMatrix Q)

/-- Finite tensor product over named qubits. -/
def tensorOps {I : Type*} [Fintype I] (M : I → Op Bool) : Op (I → Bool) :=
  fun a b => ∏ i, M i (a i) (b i)

/-- PDF p.2: exp(-i pi M/4) for a Hermitian involution M. -/
def quarterRotation {I : Type*} [Fintype I] [DecidableEq I] (M : Op I) : Op I :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (1 - Complex.I • M)

/-- PDF p.2: one sector; the Q factor acts first. -/
def sectorEncoder (m : ℕ) (P Q : Axis) : Op (Bool × Qubits m) :=
  quarterRotation (Matrix.kronecker (axisMatrix P) (tensorOps fun _ : Fin m => axisMatrix P)) *
  quarterRotation (Matrix.kronecker (axisMatrix Q) (tensorOps fun _ : Fin m => axisMatrix Q))

/-- PDF p.2: tensor product of the k sector encoders. -/
def twoPauliEncoder (m k : ℕ) (P Q : Axis) : Op (Qubits k × Signals m k) :=
  fun a b => ∏ j, sectorEncoder m P Q (a.1 j,fun i => a.2 (j,i))
    (b.1 j,fun i => b.2 (j,i))

/-- PDF p.4: T(c), the signed complete-sector observable. -/
def sectorMoment (m k : ℕ) (P Q : Axis) (c : Qubits k) : Op (Signals m k) :=
  tensorOps fun w => if c w.1 then remaining P Q else 1

/-- PDF p.4: input R_A(c) observable. -/
def inputMoment (k : ℕ) (P Q : Axis) (c : Qubits k) : Op (Qubits k) :=
  tensorOps fun j => if c j then remaining P Q else 1

/-- PDF p.4, Eq.(3): odd-m expansion with real coefficients, normalization, and positivity. -/
def oddForm {m k : ℕ} (P Q : Axis) (rho : Op (Signals m k)) : Prop :=
  ∃ alpha : Qubits k → ℝ, alpha (fun _ => false) = 1 ∧
    rho = ((2 : ℂ)^(m*k))⁻¹ • ∑ c, (alpha c : ℂ) • sectorMoment m k P Q c ∧
    rho.PosSemidef

/-- PDF p.4: algebraic criterion, without assuming recovery. -/
def ResourceCriterion {m k : ℕ} (P Q : Axis) (rho : Op (Signals m k)) : Prop :=
  if Even m then rho = mixed (Signals m k) else oddForm P Q rho

/-- PDF p.43: marginal on selected coordinates; discarded coordinates agree on bra and ket. -/
def marginal {W D : Type*} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]
    (J : Finset W) (rho : Op (W → D)) : Op (J → D) :=
  fun a b => ∑ x : W → D, ∑ y : W → D,
    if (∀ j : J, x j = a j) ∧ (∀ j : J, y j = b j) ∧
      (∀ w, w ∉ J → x w = y w) then rho x y else 0

example {m k : ℕ} (i : Fin m) (b : Qubits k) (t : Rest m k i) (j : Fin k) :
    joinSignal i b t (j,i) = b j := by simp [joinSignal]

example (X : Op (Unit × Unit)) : traceRight X () () = X ((),()) ((),()) := by
  simp [traceRight]

example : axisMatrix Axis.X = pauliX := rfl

abbrev F2 := ZMod 2

/-- PDF pp.6,28: finite simple graph in a fixed oriented balanced cut and Pauli frame. -/
structure CutGraph (I : Type*) where
  AS : Matrix I I F2
  AN : Matrix I I F2
  B : Matrix I I F2
  symS : ∀ a b, AS a b = AS b a
  symN : ∀ a b, AN a b = AN b a
  diagS : ∀ a, AS a a = 0
  diagN : ∀ a, AN a a = 0

/-- A computational bit as a binary field element. -/
def bit (b : Bool) : F2 := if b then 1 else 0

/-- PDF p.36: graph quadratic phase, counting each edge once. -/
def quadratic {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2) (x : I → Bool) : F2 :=
  ∑ a, ∑ b, if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val
    then A a b * bit (x a) * bit (x b) else 0

/-- PDF p.35, Eq.(S47): standard positive graph-state convention. -/
def graphVector {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    EuclideanSpace ℂ ((I → Bool) × (I → Bool)) :=
  WithLp.toLp 2 fun p => ((2 : ℂ)^(Fintype.card I))⁻¹ *
    (if quadratic G.AS p.1 + (∑ a, ∑ b, bit (p.1 a) * G.B a b * bit (p.2 b)) +
      quadratic G.AN p.2 = 0 then 1 else -1)

/-- PDF p.7: complete cut kernel over F₂, not merely its dimension. -/
def cutKernel {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :=
  LinearMap.ker G.B.transpose.mulVecLin

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- PDF p.7: sector-indicator map F. -/
def sectorIndicator {m k : ℕ} (c : Fin k → F2) : Wires m k → F2 := fun w => c w.1

/-- PDF p.7, Eq.(6): ambient X-type exceptional space. -/
def exceptionalX {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) : Set (Wires m k → F2) :=
  {x | ∃ c, x = sectorIndicator c ∧ A.mulVec x = 0}

/-- PDF p.7, Eq.(6): ambient Y-type exceptional space; sector parity is explicit. -/
def exceptionalY {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) : Set (Wires m k → F2) :=
  {x | ∃ c, x = sectorIndicator c ∧ (A+1).mulVec x = 0 ∧ ∑ j, c j = 0}

/-- Encoder classes keep the ordered axes in the encoder itself. -/
def classXZ (P Q : Axis) : Prop := (P = .X ∧ Q = .Z) ∨ (P = .Z ∧ Q = .X)

def classYZ (P Q : Axis) : Prop := (P = .Y ∧ Q = .Z) ∨ (P = .Z ∧ Q = .Y)

def classXY (P Q : Axis) : Prop := (P = .X ∧ Q = .Y) ∨ (P = .Y ∧ Q = .X)

/-- PDF p.7, Eq.(6): ambient E, independent of the cut kernel. -/
def exceptionalSpace {m k : ℕ} (P Q : Axis) (A : Matrix (Wires m k) (Wires m k) F2) :
    Set (Wires m k → F2) :=
  if Even m then {0} else if classXZ P Q then exceptionalY A
    else if classYZ P Q then exceptionalX A else {0}

/-- PDF pp.6,29: signed signal stabilizer generator; multiplication preserves graph signs. -/
def signalGenerator {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I F2) (v : I) : Op (I → Bool) :=
  tensorOps fun w => if w = v then pauliX else if A v w = 1 then pauliZ else 1

/-- PDF p.29: signed K_S(x), never replaced by an unsigned X^x Z^(AS x). -/
def signalStabilizer {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I F2) (x : I → F2) : Op (I → Bool) :=
  (List.ofFn fun a : Fin (Fintype.card I) =>
    let v := (Fintype.equivFin I).symm a
    if x v = 1 then signalGenerator A v else 1).prod

/-- PDF p.7, Definition 1: support only on A after forward conjugation. -/
def ExceptionalVector {m k : ℕ} (P Q : Axis) (G : CutGraph (Wires m k))
    (x : Wires m k → F2) : Prop :=
  ∃ M : Op (Qubits k), twoPauliEncoder m k P Q *
    Matrix.kronecker (1 : Op (Qubits k)) (signalStabilizer G.AS x) * (twoPauliEncoder m k P Q)ᴴ =
      Matrix.kronecker M (1 : Op (Signals m k))

/-- PDF p.29: normalized sum of the signal-only stabilizer subgroup. -/
def graphProjector {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) : Op (I → Bool) :=
  (Fintype.card (cutKernel G) : ℂ)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1

/-- PDF p.33: an ordered sector assignment of exactly m vertices in each of k sectors. -/
def HasConstantSectors {m k : ℕ} (K : Submodule F2 (Fin (m*k) → F2)) : Prop :=
  ∃ e : (Fin k × Fin m) ≃ Fin (m*k),
    ∀ x ∈ K, ∀ j a b, x (e (j,a)) = x (e (j,b))

/-- PDF p.11: CZ layer induced by a binary graph adjacency. -/
def czLayer {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2) : Op (I → Bool) :=
  Matrix.diagonal fun x => if quadratic A x = 0 then 1 else -1

/-- PDF p.11: reversible binary map |x> ↦ |Mx>; used with invertible M. -/
def linearLayer {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I F2) : Op (I → Bool) :=
  fun a b => if (fun i => bit (a i)) = M.mulVec (fun i => bit (b i)) then 1 else 0

/-- PDF p.11, Eq.(9): rightmost CZ_AN, then H, then B^(-T), then CZ_AS. -/
def bellNormalizer {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) : Op (I → Bool) :=
  czLayer G.AS * linearLayer (G.B.transpose)⁻¹ * tensorOps (fun _ : I => hadamard) * czLayer G.AN

/-- Clifford normalizer on a named qubit register, including fourth-root Pauli phases. -/
def RegisterClifford {I : Type*} [Fintype I] [DecidableEq I] (U : Op (I → Bool)) : Prop :=
  U ∈ Matrix.unitaryGroup (I → Bool) ℂ ∧
    ∀ l : I → Option Axis, ∃ t : I → Option Axis, ∃ p : Fin 4,
      U * tensorOps (fun i => match l i with | none => 1 | some a => axisMatrix a) * Uᴴ =
        Complex.I^p.val • tensorOps (fun i => match t i with | none => 1 | some a => axisMatrix a)

/-- PDF p.11: a one-qubit unitary is Clifford exactly when it permutes signed axes. -/
def SingleClifford (U : Op Bool) : Prop :=
  U ∈ Matrix.unitaryGroup Bool ℂ ∧ ∀ a : Axis, ∃ b : Axis, ∃ s : ℂ,
    (s = 1 ∨ s = -1) ∧ U * axisMatrix a * Uᴴ = s • axisMatrix b

/-- PDF p.11: local Clifford product up to a wire permutation. -/
def LocalCliffordPermutation {I : Type*} [Fintype I] [DecidableEq I] (U : Op (I → Bool)) : Prop :=
  ∃ e : Equiv.Perm I, ∃ V : I → Op Bool, (∀ i, SingleClifford (V i)) ∧
    ∀ a b, U a b = ∏ i, V i (a (e i)) (b i)

/-- Binary permutation matrix in the chosen signal/noise orderings. -/
def BinaryPermutation {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I F2) : Prop :=
  ∃ e : Equiv.Perm I, ∀ a b, B a b = if a = e b then 1 else 0

/-- PDF p.12 and Eq.(S54), p.39: fixed rank-two cut, zero internal adjacencies. -/
def rankTwoExample : CutGraph (Wires 3 1) where
  AS := 0
  AN := 0
  B := fun a b => (![![1,0,0],![0,1,0],![1,1,0]] : Matrix (Fin 3) (Fin 3) F2) a.2 b.2
  symS := by intros; rfl
  symN := by intros; rfl
  diagS := by intros; rfl
  diagN := by intros; rfl

example : rankTwoExample.AS = 0 := rfl

example : bit false = 0 := rfl

/-- PDF p.24: regroup a fixed physical resource by the same coordinate bijection on each side. -/
def regroupResource {nu m k : ℕ} (e : Wires m k ≃ Fin nu)
    (R : EuclideanSpace ℂ (Qubits nu × Qubits nu)) :
    EuclideanSpace ℂ (Signals m k × Signals m k) :=
  WithLp.toLp 2 fun p => R (p.1 ∘ e.symm,p.2 ∘ e.symm)

/-- PDF pp.6,28: explicit unitary spectral form on d times L dimensions. -/
def SpectralForm {m k : ℕ} (rho : Op (Signals m k)) : Prop :=
  ∃ sigma : Op (Qubits k), IsDensityMatrix sigma ∧
    ∃ W : Matrix (Signals m k) (Qubits k × Qubits ((m-1)*k)) ℂ,
      Wᴴ*W = 1 ∧ W*Wᴴ = 1 ∧
      rho = W * Matrix.kronecker sigma (mixed (Qubits ((m-1)*k))) * Wᴴ

/-- PDF p.6: every eigenvalue, including a zero eigenvalue when present, has L-divisible multiplicity. -/
def DivisibleEigenmultiplicities {m k : ℕ} (rho : Op (Signals m k)) : Prop :=
  ∀ z : ℂ, 2^((m-1)*k) ∣ Module.finrank ℂ
    (LinearMap.ker ((rho-z • (1 : Op (Signals m k))).mulVecLin))

/-- PDF p.20: identity or a nonidentity Pauli direction. -/
def directionMatrix : Option Axis → Op Bool
  | none => 1
  | some a => axisMatrix a

/-- PDF p.20: the axis complementary to the distinct ordered axes; signs omitted only for support. -/
def remainingAxis (P Q : Axis) : Axis :=
  if P ≠ .X ∧ Q ≠ .X then .X else if P ≠ .Y ∧ Q ≠ .Y then .Y else .Z

/-- PDF p.20: trivial total signal support, with arbitrary action on the source. -/
def SourceOnly (m : ℕ) (M : Op (Bool × Qubits m)) : Prop :=
  ∃ A : Op Bool, M = Matrix.kronecker A (1 : Op (Qubits m))

/-- PDF p.20: restriction of a tensor operator to a specified signal position. -/
def HasSignalDirection {m : ℕ} (M : Op (Bool × Qubits m)) (i : Fin m) (a : Axis) : Prop :=
  ∃ V : Op (Bool × ({j : Fin m // j ≠ i} → Bool)), ∀ p q,
    M p q = axisMatrix a (p.2 i) (q.2 i) *
      V (p.1,fun j => p.2 j) (q.1,fun j => q.2 j)

/-- PDF pp.42–43: normalized computational Dicke vector, zero on infeasible excitation inputs. -/
def dicke {I : Type*} [Fintype I] (r : ℕ) : EuclideanSpace ℂ (I → Bool) :=
  WithLp.toLp 2 fun x => if hammingWeight x = r then
    ((Real.sqrt ((Nat.choose (Fintype.card I) r : ℕ) : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.43: same Dicke vector in any balanced signal/noise coordinates. -/
def dickeResource (I : Type*) [Fintype I] (r : ℕ) :
    EuclideanSpace ℂ ((I → Bool) × (I → Bool)) :=
  WithLp.toLp 2 fun p => if hammingWeight p.1 + hammingWeight p.2 = r then
    ((Real.sqrt ((Nat.choose (2*Fintype.card I) r : ℕ) : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.43: lambda_j are probabilities, not Schmidt amplitudes. -/
def dickeLambda (nu r j : ℕ) : ℝ :=
  (Nat.choose nu j : ℝ) * (Nat.choose nu (r-j) : ℝ) / (Nat.choose (2*nu) r : ℝ)

/-- PDF pp.43–44: Shannon entropy of the feasible excitation probabilities in bits. -/
def dickeEntropy (nu r : ℕ) : ℝ :=
  -∑ j ∈ Finset.Icc (r-nu) (min r nu), dickeLambda nu r j * Real.logb 2 (dickeLambda nu r j)

/-- PDF p.43: marginal on two distinct qubits with the ordered computational basis 00,01,10,11. -/
def twoQubitMarginal {n : ℕ} (rho : Op (Qubits n)) (a b : Fin n) : Op (Bool × Bool) :=
  fun p q => ∑ x : Qubits n, ∑ y : Qubits n,
    if x a = p.1 ∧ x b = p.2 ∧ y a = q.1 ∧ y b = q.2 ∧
      (∀ t, t ≠ a → t ≠ b → x t = y t) then rho x y else 0

/-- PDF p.43, Eq.(S70): coefficients use real subtraction, even at r=0 and r=n. -/
def dickePairFormula (n r : ℕ) : Op (Bool × Bool) :=
  ((((n : ℝ)-r)*((n : ℝ)-r-1)/((n : ℝ)*((n : ℝ)-1)) : ℝ) : ℂ) • pureDensity (ket (false,false)) +
  ((((r : ℝ)*(r-1))/((n : ℝ)*((n : ℝ)-1)) : ℝ) : ℂ) • pureDensity (ket (true,true)) +
  ((((r : ℝ)*((n : ℝ)-r))/((n : ℝ)*((n : ℝ)-1)) : ℝ) : ℂ) •
    pureDensity (ket (false,true) + ket (true,false))

example : dickeLambda 1 0 0 = 1 := by norm_num [dickeLambda]

example : dickeEntropy 1 0 = 0 := by norm_num [dickeEntropy, dickeLambda]

/-- PDF pp.5,25: four qudits are ordered reference, transformed A, S, N. -/
def omegaFour {k : ℕ} (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k))
    (U : Op (Qubits k × Signals 1 k)) : EuclideanSpace ℂ (Fin 4 → Qubits k) :=
  WithLp.toLp 2 fun p => omega R U (p 0,((p 1,fun w => p 2 w.1),fun w => p 3 w.1))

/-- PDF p.25: AME(4,d) means unit norm and all six two-party marginals maximally mixed. -/
def AMEFour {D : Type*} [Fintype D] [DecidableEq D]
    (v : EuclideanSpace ℂ (Fin 4 → D)) : Prop :=
  IsState v ∧ ∀ J : Finset (Fin 4), J.card = 2 →
    marginal J (pureDensity v) = mixed (J → D)

/-- PDF p.25: explicit finite-field encoder, over F_(2^k), rather than coordinatewise F₂. -/
def fieldEncoder {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam : F) : Op (F × F) :=
  fun p q => if p.1 = q.1+q.2 ∧ p.2 = q.1+lam*q.2 then 1 else 0

/-- Eq.(S18), PDF p.25: both decoder outputs, with distinct linear combinations. -/
def fieldDecoder {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam : F) : Op (F × F) :=
  fun p q => if p.1 = q.1-lam*q.2 ∧ p.2 = q.1+(1-lam)*q.2 then 1 else 0

/-- Eq.(S17), PDF p.25: normalized 1/d AME amplitudes. -/
def fieldChoi {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam : F) :
    EuclideanSpace ℂ (Fin 4 → F) :=
  WithLp.toLp 2 fun p => if p 1 = p 0+p 3 ∧ p 2 = p 0+lam*p 3 then
    (Fintype.card F : ℂ)⁻¹ else 0

/-- PDF p.25: authorized channel obtained by tracing transformed A from the Bell-resource encoding. -/
def fieldAuthorized {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam : F) : Superop F (F × F) :=
  fun X p q => ∑ a, ∑ b, ∑ c,
    fieldEncoder lam (a,p.1) (b,p.2) * X b c *
      conj (fieldEncoder lam (a,q.1) (c,q.2)) / (Fintype.card F : ℂ)

/-- PDF p.10: a Pauli observable on S_i N, with its fourth-root phase. -/
def AuthorizedPauli {m k : ℕ} (M : Op (Qubits k × Signals m k)) : Prop :=
  ∃ p : Fin 4, ∃ a : Fin k → Option Axis, ∃ b : Wires m k → Option Axis,
    M = Complex.I^p.val • Matrix.kronecker
      (tensorOps fun j => directionMatrix (a j)) (tensorOps fun w => directionMatrix (b w))

/-- PDF p.10: Clifford normalizer of the full authorized Pauli group. -/
def AuthorizedClifford {m k : ℕ} (C : Op (Qubits k × Signals m k)) : Prop :=
  C ∈ Matrix.unitaryGroup (Qubits k × Signals m k) ℂ ∧
    ∀ M, AuthorizedPauli M → AuthorizedPauli (C*M*Cᴴ)

/-- PDF p.10: source/input Pauli on the jth logical qubit. -/
def logicalAxis {k : ℕ} (j : Fin k) (a : Axis) : Op (Qubits k) :=
  tensorOps fun l => if l = j then axisMatrix a else 1

/-- PDF p.10: lift an authorized operator, acting identically on the entire erased complement. -/
def liftAuthorized {m k : ℕ} (i : Fin m) (M : Op (Qubits k × Signals m k)) : Op (Full m k) :=
  fun p q => if p.1.1 = q.1.1 ∧ (∀ w : Wires m k, w.2 ≠ i → p.1.2 w = q.1.2 w)
    then M (fun j => p.1.2 (j,i),p.2) (fun j => q.1.2 (j,i),q.2) else 0

/-- Graph on a fixed labeled vertex set. All cuts and sectorings will be chosen explicitly. -/
structure LabeledGraph (V : Type*) where
  adj : Matrix V V F2
  sym : ∀ a b, adj a b = adj b a
  diag : ∀ a, adj a a = 0

/-- PDF pp.9,33: the bijection chooses a balanced cut and an ordered sector decomposition at once. -/
def realize {m k : ℕ} {V : Type*} (G : LabeledGraph V)
    (e : (Wires m k ⊕ Wires m k) ≃ V) : CutGraph (Wires m k) where
  AS := fun a b => G.adj (e (.inl a)) (e (.inl b))
  AN := fun a b => G.adj (e (.inr a)) (e (.inr b))
  B := fun a b => G.adj (e (.inl a)) (e (.inr b))
  symS := fun a b => G.sym _ _
  symN := fun a b => G.sym _ _
  diagS := fun a => G.diag _
  diagN := fun a => G.diag _

/-- PDF p.9, Eq.(8): existential graph-level GSECC decision, not failure of one cut. -/
def GSECC {m k : ℕ} {V : Type*} (P Q : Axis) (G : LabeledGraph V) : Prop :=
  ∃ e : (Wires m k ⊕ Wires m k) ≃ V,
    (cutKernel (realize G e) : Set _) ⊆ exceptionalSpace P Q (realize G e).AS

/-- Make an undirected simple graph from an edge prescription, deleting loops. -/
def undirectedGraph (n : ℕ) (p : Fin n → Fin n → Prop) : LabeledGraph (Fin n) where
  adj := fun a b => if a ≠ b ∧ (p a b ∨ p b a) then 1 else 0
  sym := by intro a b; simp only [ne_comm, or_comm]
  diag := by intro a; simp

/-- PDF p.38: consecutive pairs form a perfect matching. -/
def matchingGraph (nu : ℕ) := undirectedGraph (2*nu) fun a b => a.val/2 = b.val/2

/-- PDF p.38: path P_(2nu) with vertices 0,...,2nu-1. -/
def pathGraph (nu : ℕ) := undirectedGraph (2*nu) fun a b => a.val+1 = b.val

/-- PDF p.38: cycle C_(2nu), used only for nu>=2. -/
def cycleGraph (nu : ℕ) := undirectedGraph (2*nu) fun a b =>
  a.val+1 = b.val ∨ (a.val+1 = 2*nu ∧ b.val = 0)

/-- PDF pp.38–39: row-major rectangular cluster with 2a rows and b columns. -/
def rectangularGraph (nu b : ℕ) := undirectedGraph (2*nu) fun v w =>
  (v.val/b = w.val/b ∧ v.val%b+1 = w.val%b) ∨
  (v.val/b+1 = w.val/b ∧ v.val%b = w.val%b)

/-- PDF p.39: complete and star families. -/
def completeGraph (nu : ℕ) := undirectedGraph (2*nu) fun _ _ => True

def starGraph (nu : ℕ) := undirectedGraph (2*nu) fun a _ => a.val = 0

/-- Original PDF p.42, Eq.(S65), read directly in the original PDF. No sampled graph is inferred. -/
def sparseCutMatrix : Matrix (Fin 12) (Fin 12) F2 :=
  ![![1,1,1,0,1,0,1,1,0,0,0,1], ![0,0,0,0,0,0,0,1,0,1,1,1],
    ![1,0,0,0,1,0,0,1,0,1,1,0], ![0,0,0,1,0,1,0,0,1,0,0,0],
    ![1,1,0,1,1,0,0,0,1,1,1,0], ![1,0,0,1,0,0,0,0,0,0,0,0],
    ![0,1,0,1,1,0,0,0,0,0,1,0], ![1,0,1,1,1,1,0,0,1,0,0,0],
    ![0,0,0,0,1,1,0,0,0,1,1,0], ![0,0,0,0,1,0,1,1,0,1,1,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0], ![1,0,0,1,0,0,0,0,0,0,1,0]]

example : sparseCutMatrix 10 3 = 1 := rfl

/-- Canonical purification of a density operator, reference first. The input marginal is rho. -/
def densityPurification {I : Type*} [Fintype I] [DecidableEq I] (rho : Op I) :
    EuclideanSpace ℂ (I × I) := WithLp.toLp 2 fun p => (cfc Real.sqrt rho) p.2 p.1

/-- PDF p.3: coherent information of a channel at rho, via a purification. -/
def coherentInformation {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Phi : Superop I J) (rho : Op I) : ℝ :=
  vnEntropy (Phi rho) - vnEntropy (idTensorSuperop (R := I) Phi (pureDensity (densityPurification rho)))

/-- PDF p.3: optimized single-use coherent information, over all density inputs.
For finite nonempty registers and channels the value set is nonempty and bounded. -/
def singleUseInformation {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Phi : Superop I J) : ℝ :=
  sSup {r | ∃ rho : Op I, IsDensityMatrix rho ∧ r = coherentInformation Phi rho}

/-- PDF p.3, refs.[34–36]: quantum capacity via regularized optimized coherent information.
Devetak, quant-ph/0304127, Theorem 5 / Proposition 7 identifies this with unassisted quantum
capacity. Positive block lengths only; the superadditive regularization is written as a supremum. -/
def quantumCapacity {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Phi : Superop I J) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧
    r = singleUseInformation (piSuperop (fun _ : Fin n => Phi)) / (n : ℝ)}

/-- PDF pp.11,37–38: elementary Clifford gates with arbitrary wire connectivity. -/
inductive BellGate (n : ℕ) where
  | H (a : Fin n)
  | CNOT (control target : Fin n)
  | CZ (a b : Fin n)

/-- Exclude repeated control/target endpoints as required by the elementary gate set. -/
def BellGate.Legal {n : ℕ} : BellGate n → Prop
  | .H _ => True
  | .CNOT a b => a ≠ b
  | .CZ a b => a ≠ b

/-- Exact gate matrices; an H acts only on its named wire, CNOT uses the first wire as control. -/
def BellGate.matrix {n : ℕ} : BellGate n → Op (Qubits n)
  | .H a => fun x y => hadamard (x a) (y a) * ∏ b ∈ Finset.univ.erase a, if x b = y b then 1 else 0
  | .CNOT a b => fun x y => if x = Function.update y b (xor (y b) (y a)) then 1 else 0
  | .CZ a b => Matrix.diagonal fun x => if x a && x b then -1 else 1

/-- Chronological gate list: first element acts first. Size is the actual list length. -/
def bellWordMatrix {n : ℕ} (word : List (BellGate n)) : Op (Qubits n) :=
  (word.map BellGate.matrix).reverse.prod

example (n : ℕ) : bellWordMatrix ([] : List (BellGate n)) = 1 := rfl

example : densityPurification (1 : Op Unit) ((),()) = 1 := by
  simp [densityPurification, cfc_one]

/-- Reindex both sides of a fixed cut; this is coordinate relabelling, not a physical operation. -/
def reindexCut {I J : Type*} (G : CutGraph I) (e : J ≃ I) : CutGraph J where
  AS := fun a b => G.AS (e a) (e b)
  AN := fun a b => G.AN (e a) (e b)
  B := fun a b => G.B (e a) (e b)
  symS := fun a b => G.symS _ _
  symN := fun a b => G.symN _ _
  diagS := fun a => G.diagS _
  diagN := fun a => G.diagN _

/-- PDF pp.33–34: fixed-cut acceptance searches only for a compatible sector assignment. -/
def FixedCutAdmissible {m k : ℕ} (P Q : Axis) (G : CutGraph (Fin (m*k))) : Prop :=
  ∃ e : Wires m k ≃ Fin (m*k),
    (cutKernel (reindexCut G e) : Set _) ⊆ exceptionalSpace P Q (reindexCut G e).AS

/-- Lossless encoder of ordered axes for the counted RAM input. -/
def axisCode : Axis → ℕ
  | .X => 0
  | .Y => 1
  | .Z => 2

/-- Row-major binary matrix input; all n² entries are supplied, no graph certificate is assumed. -/
def matrixWords {n : ℕ} (A : Matrix (Fin n) (Fin n) F2) : List ℕ :=
  (List.finRange n).flatMap fun i => List.ofFn fun j => (A i j).val

/-- Fixed-cut machine input header followed by AS, B, AN. -/
def fixedCutInput {m k : ℕ} (P Q : Axis) (G : CutGraph (Fin (m*k))) : List ℕ :=
  [m,k,axisCode P,axisCode Q] ++ matrixWords G.AS ++ matrixWords G.B ++ matrixWords G.AN

/-- Graph-level machine input header followed by the complete labeled adjacency matrix. -/
def graphInput {m k : ℕ} (P Q : Axis) (G : LabeledGraph (Fin (2*(m*k)))) : List ℕ :=
  [m,k,axisCode P,axisCode Q] ++ matrixWords G.adj

example : axisCode Axis.Z = 2 := rfl

/-- Sanity: scalar identity normalization on a zero-qubit register. -/
example : mixed Unit () () = 1 := by simp [mixed]

example : bell Unit ((),()) = 1 := by simp [bell]

/-- Sanity: encoding is computed from its resource, rather than chosen independently. -/
example {m k : ℕ} (U : Op (Qubits k × Signals m k)) :
    encoding (0 : EuclideanSpace ℂ (Signals m k × Signals m k)) U = 0 := by
  ext y a
  simp [encoding]

/-- Sanity: the computed encoded channel sends the zero operator to zero. -/
example {m k : ℕ} (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) : encoded R U 0 = 0 := by
  simp [encoded]

example {m k : ℕ} (c : Fin k → F2) (j : Fin k) (i : Fin m) :
    sectorIndicator (m := m) c (j,i) = c j := rfl

/-- Sanity: the two finite-field decoder combinations are kept distinct. -/
example {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam u n : F) :
    fieldDecoder lam (u-lam*n,u+(1-lam)*n) (u,n) = 1 := by
  simp [fieldDecoder]

example {F : Type*} [Field F] [Fintype F] [DecidableEq F] (lam a b : F) :
    fieldEncoder lam (a+b,a+lam*b) (a,b) = 1 := by
  simp [fieldEncoder]

end

end QAlgorithms.Papers.Independent.Information100.P22


