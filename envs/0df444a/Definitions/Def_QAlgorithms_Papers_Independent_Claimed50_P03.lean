-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
-- name    : QAlgorithms_Papers_Independent_Claimed50_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T08:38:36.093836+00:00
-- url     : https://prove2.me/theorems/e0ad13ec-207d-44e5-97f1-25f600256a26
-- title:
--   Definitions for Learning to predict arbitrary quantum processes
-- statement:
--   The objects the formalized statements of *Learning to predict arbitrary quantum processes* (arXiv:2210.14894) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `singlePauli`: Paper p.18: the fixed one-qubit Pauli matrices.
--   - `namedWireTensor`: Paper p.18: tensor product in the named-wire computational basis.
--   - `wordMatrix`: Paper p.18: matrix of a phase-free Pauli word (I/X/Y/Z encoded as 0/1/2/3).
--   - `wordSupport`: Paper p.18: nonidentity support, including the empty support of I.
--   - `pauliWeight`: Paper p.18: Pauli weight.
--   - `coefficient`: Paper pp.18,30: real Pauli coefficient with ordinary trace.
--   - `IsLocal`: Paper p.18: locality is vanishing of coefficients above weight k.
--   - `IsHomogeneous`: Paper p.23: homogeneous locality; degree zero retains the identity.
--   - `HasBoundedDegree`: Paper pp.18,21,32: a finite decomposition into at most k-body Hermitian terms, with at most d terms incident on each wire.
--   - `HasExpansion`: Paper p.18, A2: counts nonzero coefficients with comparable supports, including the identity. de≤n is imposed by downstream theorems, not here.
--   - `pauliNorm`: Paper p.30, B1: Pauli-p norm including the identity coefficient.
--   - `expansionExponent`: Paper p.19: r=2 de/(de+1).
--   - `expansionConstant`: Paper pp.19,31, A5/B4: exact expansion constant.
--   - `localityConstant`: Paper pp.20,31: ce=4^k,de=k; the initial 2 is multiplicative.
--   - `degreeConstant`: Paper p.31, B12: exact bounded-participation constant.
--   - `IsStateLaw`: Paper pp.3,35: normalized Borel law supported on trace-one PSD matrices. The matrix space carries its usual finite-dimensional Borel sigma algebra.
--   - `conjugateWire`: Paper p.35: conjugation by U on a single named wire.
--   - `IsLocallyFlat`: Paper pp.3,35: local H- and S-invariance as equality of pushforward measures, allowing discrete ensembles without densities.
--   - `subsystemPurity`: Paper p.36, D4: nonidentity purity on subsystem S, written using embedded Pauli moments rather than an implicit partial-trace reindexing.
--   - `momentWeight`: Paper pp.36,38: distribution-dependent coefficient weight.
--   - `coefficientRisk`: Paper p.36, D6: weighted squared coefficient error.
--   - `truncateStrict`: Paper p.37, D14: strict cutoff, distinguished from ≤k in D2/E20.
--   - `smallWeightFilter`: Paper p.38, D22: evaluate the denominator only above the positive threshold.
--   - `sparseFilter`: Paper pp.38-39, D28: both coefficient filtering layers.
--   - `sampleMaximum`: Paper p.42: finite sample maximum, with empty-data fallback used only at N=0.
--   - `polarization`: Paper p.23, A33: injections assign the k support wires to k replicas, once per permutation; linear extension. At k=0 this retains scalar operators.
--   - `rademacherValue`: Paper p.24: ±1 sign encoding.
--   - `signAverage`: Paper p.24: average over k independent uniform Rademacher signs.
--   - `productPath`: Paper pp.22,24, A26/A35: signed tensor-product path for every real t. Only |t|≤1 is needed when the operator must be a density matrix.
--   - `deletedSlice`: Paper p.22, A23: delete wire i from the homogeneous derivative.
--   - `localBeta`: Paper p.22, A24: actual local-optimization coefficient.
--   - `qubitHaarParameters`: Paper p.25: independent z-uniform and angle-uniform coordinates of Haar surface measure on the Bloch sphere, with normalization 1/(4π).
--   - `haarQubit`: Paper p.25: normalized qubit density in Haar coordinates. Clipping z extends the function outside the sampling support while preserving normalization.
--   - `haarProductLaw`: Paper pp.25-27: independent Haar parameters on all named wires.
--   - `localMaximizer`: Paper p.22, A25: pure local Bloch-field maximizer; Z+ resolves the zero-field tie, avoiding 0/0 and a spurious maximally mixed 'pure state'.
--   - `completedReplicas`: Paper p.22: append the actual locally optimized last replica.
--   - `homogeneousSlice`: Paper p.22, A21: homogeneous slice.
--   - `bestDegree`: Paper p.22: a source-selected best homogeneous degree; the finite argmax exists for k≥1. No cost is assigned to this mathematical choice.
--   - `bestTime`: Paper p.23, A27: attained mathematical optimizer on the compact interval; no exact polynomial optimization oracle is given unit computational cost.
--   - `sliceConstant`: Paper p.27, A60: exact slice prefactor.
--   - `optimizedSliceMean`: Paper p.27: mean absolute slice energy for the actual A.3 Haar replicas, local maximizers and independent signs.
--   - `sliceInfluence`: Paper p.27: the sum of square roots of wire/axis influences.
--   - `sliceMass`: Paper p.29: Pauli-r norm of one homogeneous slice.
--   - `Shot`: Paper p.46, E2: recorded Pauli axis and ± eigenvalue on each wire.
--   - `shotProjector`: Paper pp.5,46: normalized single-qubit Pauli eigendensity.
--   - `shotWeight`: Paper p.46, E2: complete conditional Born weight, including the 3^-n probability of selecting the measurement bases.
--   - `pauliSnapshot`: Paper pp.5,47: adapt the recorded X/Y/Z indices and sign convention to the frozen local-Pauli snapshot. Here false means +1; the frozen label uses true.
--   - `shadowPredictor`: Paper p.8, Eq.24: empirical predictor from actual single-shot records.
--   - `shotEventProbability`: Paper p.46, E3: probability under independent conditional Born shots. No exact expectation is substituted for the recorded single-shot label.
--   - `localPauliShadowNorm`: Paper p.32, C1: uncentered local-Pauli shadow norm. The optimization set is nonempty and compact, and the finite second moment is continuous and bounded.
--   - `shadowSampleScale`: Paper pp.32-33: sufficient dependence from C5 and B12, polynomial in d and k^{O(k)} in locality; the latter refines the headline's informal wording.
--   - `densityCopies`: Paper p.34: N tensor copies, including the scalar zero-copy space.
--   - `CollectiveEstimator`: Paper pp.8,34: arbitrary collective POVM including classical postprocessing. It depends on the known observables, never the unknown state.
--   - `SolvesTomography`: Paper p.34: success on every legal family and state, simultaneously for all supplied observables, at the proof's constant probability 3/4.
--   - `IsPureQubit`: Paper p.22: normalized pure qubit densities for the actual A.3 replicas.
--   - `Execution`: Paper pp.18-23,47: arithmetic/access execution. Values and costs are computed together by the concrete loops below, not freely chosen cost contracts.
--   - `executionPure`: Zero-cost return.
--   - `executionBind`: Sequential composition adds the costs of the executions actually performed.
--   - `runAdd`: One arithmetic addition.
--   - `runMul`: One arithmetic multiplication.
--   - `runDiv`: One guarded real-arithmetic division (source arithmetic-operation model).
--   - `runSqrt`: One elementary real square-root operation.
--   - `runAbs`: One absolute-value operation.
--   - `runIfLe`: One comparison and branch; only the selected branch is executed.
--   - `runReadWire`: A single random-access read of a recorded axis and eigenvalue.
--   - `SparseWord`: Sparse Pauli representation: only the nonidentity (wire,axis) pairs.
--   - `decodeSparseWord`: Decode a sparse Pauli description; valid descriptions have distinct wires.
--   - `SparseObservable`: Paper p.47: finite sparse Pauli expansion supplied classically.
--   - `decodeObservable`: Matrix denoted by a sparse Pauli expansion.
--   - `ValidDescription`: Paper p.47: canonical nonzero sparse Pauli description of a local observable.
--   - `runRecordMoment`: Paper pp.5,47: evaluate a Pauli moment from input eigendensities (shadow=false) or output inverse snapshots (shadow=true), by reading every support entry.
--   - `runLabel`: Paper p.47, E10: the actual output-label loop, with every coefficient read, support read, multiplication and addition charged.
--   - `runLabels`: Paper p.47: label preprocessing, once per sample, without recomputing labels for each input Pauli coefficient.
--   - `runAppend`: Costed list append used by the concrete increasing-wire schedule generator.
--   - `runScheduleAux`: Paper pp.5,47: enumerate all sparse Pauli words of weight≤k by extending an increasing sequence of wires. A node emits its prefix and branches only to later wires and three axes. The fuel bounds locality, not register size. List allocation, wire/axis loop overhead, and append work are charged explicitly.
--   - `runSchedule`: The retained input-Pauli schedule, generated independently of the channel and data.
--   - `runCoefficientMass`: Paper p.47, E11: sum of absolute output coefficients, computed once.
--   - `runCorrelation`: Paper p.47, E14: one empirical input/output correlation, using cached labels.
--   - `runKnownWeight`: Paper p.47, E15: compute 3^(-|P|) by a division per support entry.
--   - `runFilter`: Paper p.47, E16: exact guarded sparse filter, compiled into charged comparison, square-root, absolute-value and arithmetic operations.
--   - `runProcessTraining`: Paper p.47: actual E10-E16 training computation with shared labels.
--   - `runProcessPrediction`: Paper pp.4-5,47, E17: final prediction from classically supplied Pauli-moment access. Each supplied moment is read once, multiplied and summed; acquisition of moments/RDMs from a quantum state is outside this classical cost.
--   - `processCorrelation`: Paper p.47, E14: correlation using the conditional single-shot output label.
--   - `processPredictor`: Paper p.47, E14-E17: the actual learned predictor for a specified hyperparameter, independent of the unknown channel except through recorded data.
--   - `lowWeightPauliCount`: Paper p.5: exact number of retained input Pauli coefficients.
--   - `classicalTVDistance`: Paper p.34, Lemma 13: total variation distance between probability laws, as the supremum of absolute measurable-event probability differences. On probability laws the defining set contains zero and is bounded by one.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, https://arxiv.org/abs/2210.14894v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_LocalPauliShadows

/-! Statements from Huang--Chen--Preskill, arXiv:2210.14894v3.
Ordinary traces, phase-free Paulis, Borel state laws, spectral norms.
Source discrepancies and deferred nodes are recorded in the unit's HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable
open scoped BigOperators ComplexConjugate

/-- Paper pp.3,35-36: Borel sigma algebra on matrices over any finite named-wire register. -/
local instance namedWireMatrixMeasurableSpace {I : Type*} [Fintype I] :
    MeasurableSpace (Matrix (I → Bool) (I → Bool) ℂ) := borel _

/-- The preceding measurable structure is the usual finite-dimensional Borel one. -/
local instance namedWireMatrixBorelSpace {I : Type*} [Fintype I] :
    BorelSpace (Matrix (I → Bool) (I → Bool) ℂ) := ⟨rfl⟩

/-- Paper p.18: the fixed one-qubit Pauli matrices. -/
def singlePauli (p : Fin 4) : Matrix Bool Bool ℂ :=
  if p = 0 then 1 else if p = 1 then pauliX else if p = 2 then pauliY else pauliZ

/-- Paper p.18: tensor product in the named-wire computational basis. -/
def namedWireTensor {I : Type*} [Fintype I] (A : I → Matrix Bool Bool ℂ) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  fun x y => ∏ i, A i (x i) (y i)

/-- Paper p.18: matrix of a phase-free Pauli word (I/X/Y/Z encoded as 0/1/2/3). -/
def wordMatrix {I : Type*} [Fintype I] (P : (I → Fin 4)) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  namedWireTensor fun i => singlePauli (P i)

/-- Paper p.18: nonidentity support, including the empty support of I. -/
def wordSupport {I : Type*} [Fintype I] [DecidableEq I] (P : (I → Fin 4)) : Finset I :=
  Finset.univ.filter fun i => P i ≠ 0

/-- Paper p.18: Pauli weight. -/
def pauliWeight {I : Type*} [Fintype I] [DecidableEq I] (P : (I → Fin 4)) : ℕ := (wordSupport P).card

/-- Paper pp.18,30: real Pauli coefficient with ordinary trace. -/
def coefficient {I : Type*} [Fintype I] (H : (Matrix (I → Bool) (I → Bool) ℂ)) (P : (I → Fin 4)) : ℝ :=
  (wordMatrix P * H).trace.re / (2 : ℝ) ^ Fintype.card I

/-- Paper p.18: locality is vanishing of coefficients above weight k. -/
def IsLocal {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : Prop :=
  ∀ P, k < pauliWeight P → coefficient H P = 0

/-- Paper p.23: homogeneous locality; degree zero retains the identity. -/
def IsHomogeneous {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : Prop :=
  ∀ P, pauliWeight P ≠ k → coefficient H P = 0

/-- Paper pp.18,21,32: a finite decomposition into at most k-body Hermitian
terms, with at most d terms incident on each wire. -/
def HasBoundedDegree {I : Type*} [Fintype I] [DecidableEq I]
    (k d : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : Prop :=
  ∃ (m : ℕ) (S : Fin m → Finset I) (T : Fin m → (Matrix (I → Bool) (I → Bool) ℂ)),
    H = ∑ j, T j ∧
    (∀ j, (T j).IsHermitian ∧ (S j).card ≤ k ∧
      ∀ P, ¬ wordSupport P ⊆ S j → coefficient (T j) P = 0) ∧
    ∀ i, (Finset.univ.filter fun j => i ∈ S j).card ≤ d

/-- Paper p.18, A2: counts nonzero coefficients with comparable supports,
including the identity. de≤n is imposed by downstream theorems, not here. -/
def HasExpansion {I : Type*} [Fintype I] [DecidableEq I]
    (H : (Matrix (I → Bool) (I → Bool) ℂ)) (ce : ℝ) (de : ℕ) : Prop :=
  ∀ S : Finset I, S.card = de →
    ((Finset.univ.filter fun P : (I → Fin 4) => coefficient H P ≠ 0 ∧
      (S ⊆ wordSupport P ∨ wordSupport P ⊆ S)).card : ℝ) ≤ ce

/-- Paper p.30, B1: Pauli-p norm including the identity coefficient. -/
def pauliNorm {I : Type*} [Fintype I] (p : ℝ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : ℝ :=
  Real.rpow (∑ P : (I → Fin 4), Real.rpow |coefficient H P| p) (1 / p)

/-- Paper p.19: r=2 de/(de+1). -/
def expansionExponent (de : ℕ) : ℝ := 2 * (de : ℝ) / ((de : ℝ) + 1)

/-- Paper pp.19,31, A5/B4: exact expansion constant. -/
def expansionConstant (ce : ℝ) (de k : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.factorial k : ℝ)) /
    (Real.rpow ce (1 / (2 * (de : ℝ))) *
      Real.rpow (k : ℝ) ((k : ℝ) + 3 / 2 + 1 / expansionExponent de) *
      (Real.sqrt 6 + 2 * Real.sqrt 3) ^ k)

/-- Paper pp.20,31: ce=4^k,de=k; the initial 2 is multiplicative. -/
def localityConstant (k : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.factorial k : ℝ)) /
    (2 * Real.rpow (k : ℝ) ((k : ℝ) + 3 / 2 + ((k : ℝ) + 1) / (2 * (k : ℝ))) *
      (Real.sqrt 6 + 2 * Real.sqrt 3) ^ k)

/-- Paper p.31, B12: exact bounded-participation constant. -/
def degreeConstant (k d : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.factorial k : ℝ)) /
    (Real.sqrt (d : ℝ) * Real.rpow (k : ℝ) ((k : ℝ) + 5 / 2) *
      (2 * Real.sqrt 6 + 4 * Real.sqrt 3) ^ k)

/-- Paper pp.3,35: normalized Borel law supported on trace-one PSD matrices.
The matrix space carries its usual finite-dimensional Borel sigma algebra. -/
def IsStateLaw {I : Type*} [Fintype I] (D : Measure ((Matrix (I → Bool) (I → Bool) ℂ))) : Prop :=
  IsProbabilityMeasure D ∧ ∀ᵐ rho ∂D, IsDensityMatrix rho

/-- Paper p.35: conjugation by U on a single named wire. -/
def conjugateWire {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (U : Matrix Bool Bool ℂ) (rho : (Matrix (I → Bool) (I → Bool) ℂ)) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  let V := namedWireTensor fun j => if j = i then U else 1
  V * rho * V.conjTranspose

/-- Paper pp.3,35: local H- and S-invariance as equality of pushforward
measures, allowing discrete ensembles without densities. -/
def IsLocallyFlat {I : Type*} [Fintype I] [DecidableEq I]
    (D : Measure ((Matrix (I → Bool) (I → Bool) ℂ))) : Prop :=
  ∀ i, Measure.map (conjugateWire i hadamard) D = D ∧
    Measure.map (conjugateWire i phaseS) D = D

/-- Paper p.36, D4: nonidentity purity on subsystem S, written using embedded
Pauli moments rather than an implicit partial-trace reindexing. -/
def subsystemPurity {I : Type*} [Fintype I] [DecidableEq I]
    (rho : (Matrix (I → Bool) (I → Bool) ℂ)) (S : Finset I) : ℝ :=
  (∑ P ∈ Finset.univ.filter (fun P : (I → Fin 4) => wordSupport P = S),
    effectProb (wordMatrix P) rho ^ 2) / (2 : ℝ) ^ S.card

/-- Paper pp.36,38: distribution-dependent coefficient weight. -/
def momentWeight {I : Type*} [Fintype I] [DecidableEq I]
    (D : Measure ((Matrix (I → Bool) (I → Bool) ℂ))) (P : (I → Fin 4)) : ℝ :=
  (2 / 3 : ℝ) ^ pauliWeight P * ∫ rho, subsystemPurity rho (wordSupport P) ∂D

/-- Paper p.36, D6: weighted squared coefficient error. -/
def coefficientRisk {I : Type*} [Fintype I] [DecidableEq I]
    (D : Measure ((Matrix (I → Bool) (I → Bool) ℂ))) (A B : (Matrix (I → Bool) (I → Bool) ℂ)) : ℝ :=
  ∑ P : (I → Fin 4), momentWeight D P * |coefficient A P - coefficient B P| ^ 2

/-- Paper p.37, D14: strict cutoff, distinguished from ≤k in D2/E20. -/
def truncateStrict {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  ∑ P ∈ Finset.univ.filter (fun P : (I → Fin 4) => pauliWeight P < k), (coefficient H P : ℂ) • wordMatrix P

/-- Paper p.38, D22: evaluate the denominator only above the positive threshold. -/
def smallWeightFilter (e xhat bhat : ℝ) : ℝ :=
  if bhat ≤ 2 * e then 0 else xhat / bhat

/-- Paper pp.38-39, D28: both coefficient filtering layers. -/
def sparseFilter (e eta xhat bhat : ℝ) : ℝ :=
  if bhat ≤ 2 * e then 0
  else if |xhat| / Real.sqrt bhat ≤ 2 * eta * Real.sqrt e then 0
  else xhat / bhat

/-- Paper p.42: finite sample maximum, with empty-data fallback used only at N=0. -/
def sampleMaximum {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin N)).Nonempty then Finset.univ.sup' h x else 0

/-- Paper p.23, A33: injections assign the k support wires to k replicas,
once per permutation; linear extension. At k=0 this retains scalar operators. -/
def polarization {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : (Matrix ((Fin k × I) → Bool) ((Fin k × I) → Bool) ℂ) :=
  ∑ P : (I → Fin 4), (coefficient H P / (Nat.factorial k : ℝ) : ℂ) •
    ∑ e ∈ Finset.univ.filter (fun e : Fin k → I =>
      Function.Injective e ∧ Finset.univ.image e = wordSupport P),
      namedWireTensor (fun si : Fin k × I =>
        if e si.1 = si.2 then singlePauli (P si.2) else 1)

/-- Paper p.24: ±1 sign encoding. -/
def rademacherValue (b : Bool) : ℝ := if b then -1 else 1

/-- Paper p.24: average over k independent uniform Rademacher signs. -/
def signAverage (k : ℕ) (f : (Fin k → Bool) → ℝ) : ℝ :=
  (∑ sigma, f sigma) / (2 : ℝ) ^ k

/-- Paper pp.22,24, A26/A35: signed tensor-product path for every real t.
Only |t|≤1 is needed when the operator must be a density matrix. -/
def productPath {I : Type*} [Fintype I] {k : ℕ} (t : ℝ)
    (rho : Fin k → I → Matrix Bool Bool ℂ) (sigma : Fin k → Bool) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  namedWireTensor fun i => (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) +
    (t / (k : ℝ) : ℂ) • ∑ s, (rademacherValue (sigma s) : ℂ) •
      (rho s i - (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ))

/-- Paper p.22, A23: delete wire i from the homogeneous derivative. -/
def deletedSlice {n : ℕ} (q : ℕ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (i : Fin n) (p : Fin 3) :
    (Matrix ({j : Fin n // j ≠ i} → Bool) ({j : Fin n // j ≠ i} → Bool) ℂ) :=
  ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q ∧ (P i).val = p.val + 1),
    (coefficient H P : ℂ) • namedWireTensor (fun j : {j : Fin n // j ≠ i} => singlePauli (P j.val))

/-- Paper p.22, A24: actual local-optimization coefficient. -/
def localBeta {n q : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ))
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (i : Fin n) (p : Fin 3) : ℝ :=
  signAverage q fun sigma => (∏ s, rademacherValue (sigma s)) *
    effectProb (deletedSlice (q + 1) H i p)
      (productPath 1 (fun s (j : {j : Fin n // j ≠ i}) => rho s j.val) sigma)

/-- Paper p.25: independent z-uniform and angle-uniform coordinates of Haar
surface measure on the Bloch sphere, with normalization 1/(4π). -/
def qubitHaarParameters : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 / (4 * Real.pi)) •
    ((volume.restrict (Set.Icc (-1 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))

/-- Paper p.25: normalized qubit density in Haar coordinates. Clipping z
extends the function outside the sampling support while preserving normalization. -/
def haarQubit (u : ℝ × ℝ) : Matrix Bool Bool ℂ :=
  let z := max (-1 : ℝ) (min 1 u.1)
  pureDensity (WithLp.toLp 2 (fun b : Bool =>
    if b then (Real.sqrt ((1 - z) / 2) : ℂ) * Complex.exp (Complex.I * (u.2 : ℂ))
    else (Real.sqrt ((1 + z) / 2) : ℂ)))

/-- Paper pp.25-27: independent Haar parameters on all named wires. -/
def haarProductLaw (I : Type*) [Fintype I] [DecidableEq I] : Measure (I → ℝ × ℝ) :=
  Measure.pi fun _ : I => qubitHaarParameters

/-- Paper p.22, A25: pure local Bloch-field maximizer; Z+ resolves the
zero-field tie, avoiding 0/0 and a spurious maximally mixed 'pure state'. -/
def localMaximizer (b : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  let r := Real.sqrt (∑ p, b p ^ 2)
  if r = 0 then (1 / 2 : ℂ) • (1 + pauliZ)
  else (1 / 2 : ℂ) • (1 + ∑ p : Fin 3,
    (b p / r : ℂ) • singlePauli ⟨p.val + 1, by omega⟩)

/-- Paper p.22: append the actual locally optimized last replica. -/
def completedReplicas {n q : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ))
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) : Fin (q + 1) → Fin n → Matrix Bool Bool ℂ :=
  fun s i => if h : s.val < q then rho ⟨s.val, h⟩ i else localMaximizer (localBeta H rho i)

/-- Paper p.22, A21: homogeneous slice. -/
def homogeneousSlice {I : Type*} [Fintype I] [DecidableEq I]
    (q : ℕ) (H : (Matrix (I → Bool) (I → Bool) ℂ)) : (Matrix (I → Bool) (I → Bool) ℂ) :=
  ∑ P ∈ Finset.univ.filter (fun P : (I → Fin 4) => pauliWeight P = q),
    (coefficient H P : ℂ) • wordMatrix P

/-- Paper p.22: a source-selected best homogeneous degree; the finite argmax
exists for k≥1. No cost is assigned to this mathematical choice. -/
def bestDegree {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) (k : ℕ) (r : ℝ) : ℕ :=
  let mass := fun q => ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q),
    Real.rpow |coefficient H P| r
  if h : ∃ q ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, mass j ≤ mass q then
    Classical.choose h else 1

/-- Paper p.23, A27: attained mathematical optimizer on the compact interval;
no exact polynomial optimization oracle is given unit computational cost. -/
def bestTime {n q : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ))
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (sigma : Fin q → Bool) : ℝ :=
  let f := fun t => |effectProb H (productPath t rho sigma) - coefficient H (fun _ => 0)|
  if h : ∃ t ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, f u ≤ f t then
    Classical.choose h else 0

/-- Paper p.27, A60: exact slice prefactor. -/
def sliceConstant (q : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.factorial q : ℝ)) /
    (Real.rpow (q : ℝ) ((q : ℝ) + 3 / 2) * Real.sqrt 6 ^ q)

/-- Paper p.27: mean absolute slice energy for the actual A.3 Haar replicas,
local maximizers and independent signs. -/
def optimizedSliceMean {n q : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∫ u, signAverage (q + 1) (fun sigma =>
    |effectProb (homogeneousSlice (q + 1) H)
      (productPath 1 (completedReplicas H (fun s i => haarQubit (u (s, i)))) sigma)|)
    ∂haarProductLaw (Fin q × Fin n)

/-- Paper p.27: the sum of square roots of wire/axis influences. -/
def sliceInfluence {n : ℕ} (q : ℕ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∑ i : Fin n, ∑ p : Fin 3, Real.sqrt
    (∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q ∧ (P i).val = p.val + 1),
      coefficient H P ^ 2)

/-- Paper p.29: Pauli-r norm of one homogeneous slice. -/
def sliceMass {n : ℕ} (q : ℕ) (r : ℝ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  Real.rpow (∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q),
    Real.rpow |coefficient H P| r) (1 / r)

/-- Paper p.46, E2: recorded Pauli axis and ± eigenvalue on each wire. -/
abbrev Shot (n : ℕ) := Fin n → Fin 3 × Bool

/-- Paper pp.5,46: normalized single-qubit Pauli eigendensity. -/
def shotProjector (s : Fin 3 × Bool) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + (rademacherValue s.2 : ℂ) • singlePauli ⟨s.1.val + 1, by omega⟩)

/-- Paper p.46, E2: complete conditional Born weight, including the 3^-n
probability of selecting the measurement bases. -/
def shotWeight {n : ℕ} (rho : (Matrix (Qubits n) (Qubits n) ℂ)) (s : Shot n) : ℝ :=
  effectProb (namedWireTensor fun i => shotProjector (s i)) rho / (3 : ℝ) ^ n

/-- Paper pp.5,47: adapt the recorded X/Y/Z indices and sign convention to
 the frozen local-Pauli snapshot. Here false means +1; the frozen label uses true. -/
def pauliSnapshot {n : ℕ} (s : Shot n) : Matrix (Qubits n) (Qubits n) ℂ :=
  GroundStateLearning.snapshot fun i =>
    (if (s i).1 = 0 then GroundStateLearning.Axis.X
     else if (s i).1 = 1 then GroundStateLearning.Axis.Y
     else GroundStateLearning.Axis.Z, !(s i).2)

/-- Paper p.8, Eq.24: empirical predictor from actual single-shot records. -/
def shadowPredictor {n N : ℕ} (data : Fin N → Shot n) (H : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  (∑ l, effectProb H (pauliSnapshot (data l))) / (N : ℝ)

/-- Paper p.46, E3: probability under independent conditional Born shots.
No exact expectation is substituted for the recorded single-shot label. -/
def shotEventProbability {n N : ℕ} (rho : (Matrix (Qubits n) (Qubits n) ℂ))
    (event : (Fin N → Shot n) → Prop) : ℝ :=
  ∑ data : Fin N → Shot n, if event data then ∏ l, shotWeight rho (data l) else 0

/-- Paper p.32, C1: uncentered local-Pauli shadow norm. The optimization set
is nonempty and compact, and the finite second moment is continuous and bounded. -/
def localPauliShadowNorm {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  sSup {v : ℝ | ∃ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho ∧
    v = Real.sqrt (∑ s : Shot n, shotWeight rho s * effectProb H (pauliSnapshot s) ^ 2)}

/-- Paper pp.32-33: sufficient dependence from C5 and B12, polynomial in d
and k^{O(k)} in locality; the latter refines the headline's informal wording. -/
def shadowSampleScale (k d : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (3 : ℝ) ^ (2 * k) * (3 / degreeConstant k d) ^ 2

/-- Paper p.34: N tensor copies, including the scalar zero-copy space. -/
def densityCopies {n : ℕ} (N : ℕ) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) :
    Matrix (Fin N → Qubits n) (Fin N → Qubits n) ℂ :=
  fun x y => ∏ l, rho (x l) (y l)

/-- Paper pp.8,34: arbitrary collective POVM including classical
postprocessing. It depends on the known observables, never the unknown state. -/
abbrev CollectiveEstimator (n M N : ℕ) :=
  (Fin M → (Matrix (Qubits n) (Qubits n) ℂ)) →
    Measurements.OperatorPOVM (Fin N → Qubits n) (Fin M → ℝ)

/-- Paper p.34: success on every legal family and state, simultaneously
for all supplied observables, at the proof's constant probability 3/4. -/
def SolvesTomography {n M N : ℕ} (k d : ℕ) (B eps : ℝ)
    (A : CollectiveEstimator n M N) : Prop :=
  ∀ O : Fin M → (Matrix (Qubits n) (Qubits n) ℂ),
    (∀ i, (O i).IsHermitian ∧ HasBoundedDegree k d (O i) ∧ specNorm (O i) ≤ B) →
    ∀ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
      3 / 4 ≤ effectProb ((A O).operator {y | ∀ i, |y i - effectProb (O i) rho| ≤ eps})
        (densityCopies N rho)

/-! Definition sanity checks; no source theorem is proved here. -/

example : singlePauli 0 = (1 : Matrix Bool Bool ℂ) := by simp [singlePauli]

example : expansionExponent 1 = 1 := by norm_num [expansionExponent]

example {I : Type*} [Fintype I] [DecidableEq I] : pauliWeight (fun _ : I => (0 : Fin 4)) = 0 := by
  simp [pauliWeight, wordSupport]

example (e x b : ℝ) (h : b ≤ 2 * e) : smallWeightFilter e x b = 0 := by
  simp [smallWeightFilter, h]

example (e eta x b : ℝ) (h : b ≤ 2 * e) : sparseFilter e eta x b = 0 := by
  simp [sparseFilter, h]

example (c : ℝ) : signAverage 0 (fun _ => c) = c := by simp [signAverage]

example : sampleMaximum (fun i : Fin 0 => (i.elim0 : ℝ)) = 0 := by
  simp [sampleMaximum]

/-- Paper p.22: normalized pure qubit densities for the actual A.3 replicas. -/
def IsPureQubit (rho : Matrix Bool Bool ℂ) : Prop :=
  ∃ psi : EuclideanSpace ℂ Bool, IsState psi ∧ rho = pureDensity psi

example (psi : EuclideanSpace ℂ Bool) (h : IsState psi) : IsPureQubit (pureDensity psi) :=
  ⟨psi, h, rfl⟩

/-- Paper pp.18-23,47: arithmetic/access execution. Values and costs are
computed together by the concrete loops below, not freely chosen cost contracts. -/
structure Execution (A : Type*) where
  value : A
  steps : ℕ

/-- Zero-cost return. -/
def executionPure {A : Type*} (a : A) : Execution A := ⟨a, 0⟩

/-- Sequential composition adds the costs of the executions actually performed. -/
def executionBind {A B : Type*} (a : Execution A) (f : A → Execution B) : Execution B :=
  let b := f a.value
  ⟨b.value, a.steps + b.steps⟩

/-- Paper pp.5,47: writer-style sequencing of actual arithmetic/access executions. -/
instance executionMonad : Monad Execution where
  pure := executionPure
  bind := executionBind

/-- One arithmetic addition. -/
def runAdd (x y : ℝ) : Execution ℝ := ⟨x + y, 1⟩

/-- One arithmetic multiplication. -/
def runMul (x y : ℝ) : Execution ℝ := ⟨x * y, 1⟩

/-- One guarded real-arithmetic division (source arithmetic-operation model). -/
def runDiv (x y : ℝ) : Execution ℝ := ⟨x / y, 1⟩

/-- One elementary real square-root operation. -/
def runSqrt (x : ℝ) : Execution ℝ := ⟨Real.sqrt x, 1⟩

/-- One absolute-value operation. -/
def runAbs (x : ℝ) : Execution ℝ := ⟨|x|, 1⟩

/-- One comparison and branch; only the selected branch is executed. -/
def runIfLe {A : Type*} (x y : ℝ) (yes no : Unit → Execution A) : Execution A :=
  let r := if x ≤ y then yes () else no ()
  ⟨r.value, r.steps + 1⟩

/-- A single random-access read of a recorded axis and eigenvalue. -/
def runReadWire {n : ℕ} (s : Shot n) (i : Fin n) : Execution (Fin 3 × Bool) := ⟨s i, 1⟩

/-- Sparse Pauli representation: only the nonidentity (wire,axis) pairs. -/
abbrev SparseWord (n : ℕ) := List (Fin n × Fin 3)

/-- Decode a sparse Pauli description; valid descriptions have distinct wires. -/
def decodeSparseWord {n : ℕ} (w : SparseWord n) : (Fin n → Fin 4) :=
  fun i => match w.find? (fun a => decide (a.1 = i)) with
    | none => 0
    | some a => ⟨a.2.val + 1, by omega⟩

/-- Paper p.47: finite sparse Pauli expansion supplied classically. -/
abbrev SparseObservable (n : ℕ) := List (ℝ × SparseWord n)

/-- Matrix denoted by a sparse Pauli expansion. -/
def decodeObservable {n : ℕ} (terms : SparseObservable n) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  (terms.map fun a => (a.1 : ℂ) • wordMatrix (decodeSparseWord a.2)).sum

/-- Paper p.47: canonical nonzero sparse Pauli description of a local observable. -/
def ValidDescription {n : ℕ} (kap : ℕ) (terms : SparseObservable n) : Prop :=
  (terms.map fun a => decodeSparseWord a.2).Nodup ∧
    ∀ a ∈ terms, a.1 ≠ 0 ∧ a.2.length ≤ kap ∧ (a.2.map Prod.fst).Nodup

/-- Paper pp.5,47: evaluate a Pauli moment from input eigendensities (shadow=false)
or output inverse snapshots (shadow=true), by reading every support entry. -/
def runRecordMoment {n : ℕ} (shadow : Bool) (s : Shot n) (w : SparseWord n) : Execution ℝ :=
  w.foldlM (fun acc a => do
    let z ← runReadWire s a.1
    let same : Execution Bool := ⟨decide (z.1 = a.2), 1⟩
    let matched ← same
    let signed : Execution ℝ := ⟨if matched then rademacherValue z.2 else 0, 1⟩
    let v ← signed
    let v ← runMul (if shadow then 3 else 1) v
    runMul acc v) 1

/-- Paper p.47, E10: the actual output-label loop, with every coefficient
read, support read, multiplication and addition charged. -/
def runLabel {n : ℕ} (terms : SparseObservable n) (s : Shot n) : Execution ℝ :=
  terms.foldlM (fun acc a => do
    let coeff : Execution ℝ := ⟨a.1, 1⟩
    let c ← coeff
    let v ← runRecordMoment true s a.2
    let v ← runMul c v
    runAdd acc v) 0

/-- Paper p.47: label preprocessing, once per sample, without recomputing
labels for each input Pauli coefficient. -/
def runLabels {n N : ℕ} (terms : SparseObservable n) (data : Fin N → Shot n) : Execution (Array ℝ) := do
  let labels ← (List.finRange N).mapM fun l => runLabel terms (data l)
  let array : Execution (Array ℝ) := ⟨labels.toArray, labels.length⟩
  array

/-- Costed list append used by the concrete increasing-wire schedule generator. -/
def runAppend {A : Type*} (x y : List A) : Execution (List A) := ⟨x ++ y, x.length⟩

/-- Paper pp.5,47: enumerate all sparse Pauli words of weight≤k by extending
an increasing sequence of wires. A node emits its prefix and branches only to
later wires and three axes. The fuel bounds locality, not register size.
List allocation, wire/axis loop overhead, and append work are charged explicitly. -/
def runScheduleAux (n : ℕ) : ℕ → ℕ → SparseWord n → Execution (List (SparseWord n))
  | 0, _, partialWord => ⟨[partialWord], partialWord.length + 1⟩
  | fuel + 1, start, partialWord => do
    let positions : Execution (List (Fin n)) :=
      ⟨(List.finRange n).filter (fun i => decide (start ≤ i.val)), n + 1⟩
    let positions ← positions
    let children ← positions.foldlM (fun acc i =>
      (List.finRange 3).foldlM (fun acc p => do
        let next : Execution (SparseWord n) := ⟨(i, p) :: partialWord, 3⟩
        let next ← next
        let branch ← runScheduleAux n fuel (i.val + 1) next
        runAppend branch acc) acc) []
    let result : Execution (List (SparseWord n)) := ⟨partialWord :: children, partialWord.length + 1⟩
    result

/-- The retained input-Pauli schedule, generated independently of the channel and data. -/
def runSchedule (n k : ℕ) : Execution (List (SparseWord n)) := runScheduleAux n k 0 []

/-- Paper p.47, E11: sum of absolute output coefficients, computed once. -/
def runCoefficientMass {n : ℕ} (terms : SparseObservable n) : Execution ℝ :=
  terms.foldlM (fun acc a => do
    let v ← runAbs a.1
    runAdd acc v) 0

/-- Paper p.47, E14: one empirical input/output correlation, using cached labels. -/
def runCorrelation {n N : ℕ} (data : Fin N → Shot n) (labels : Array ℝ)
    (w : SparseWord n) : Execution ℝ := do
  let total ← (List.finRange N).foldlM (fun acc l => do
    let label : Execution ℝ := ⟨(labels[l.val]?).getD 0, 1⟩
    let y ← label
    let x ← runRecordMoment false (data l) w
    let xy ← runMul x y
    runAdd acc xy) 0
  runDiv total (N : ℝ)

/-- Paper p.47, E15: compute 3^(-|P|) by a division per support entry. -/
def runKnownWeight {n : ℕ} (w : SparseWord n) : Execution ℝ :=
  w.foldlM (fun acc _ => runDiv acc 3) 1

/-- Paper p.47, E16: exact guarded sparse filter, compiled into charged
comparison, square-root, absolute-value and arithmetic operations. -/
def runFilter (e eta x b : ℝ) : Execution ℝ := do
  let threshold ← runMul 2 e
  runIfLe b threshold (fun _ => pure 0) (fun _ => do
    let root ← runSqrt b
    let ax ← runAbs x
    let ratio ← runDiv ax root
    let rootE ← runSqrt e
    let threshold ← runMul 2 eta
    let threshold ← runMul threshold rootE
    runIfLe ratio threshold (fun _ => pure 0) (fun _ => runDiv x b))

/-- Paper p.47: actual E10-E16 training computation with shared labels. -/
def runProcessTraining {n N : ℕ} (k : ℕ) (e : ℝ) (terms : SparseObservable n)
    (data : Fin N → Shot n × Shot n) : Execution (List (ℝ × SparseWord n)) := do
  let labels ← runLabels terms (fun l => (data l).2)
  let eta ← runCoefficientMass terms
  let words ← runSchedule n k
  words.mapM fun w => do
    let x ← runCorrelation (fun l => (data l).1) labels w
    let b ← runKnownWeight w
    let a ← runFilter e eta x b
    pure (a, w)

/-- Paper pp.4-5,47, E17: final prediction from classically supplied
Pauli-moment access. Each supplied moment is read once, multiplied and summed;
acquisition of moments/RDMs from a quantum state is outside this classical cost. -/
def runProcessPrediction {n : ℕ} (model : List (ℝ × SparseWord n))
    (moment : SparseWord n → ℝ) : Execution ℝ :=
  model.foldlM (fun acc a => do
    let access : Execution ℝ := ⟨moment a.2, 1⟩
    let m ← access
    let v ← runMul a.1 m
    runAdd acc v) 0

example (x y : ℝ) : (runMul x y).value = x * y ∧ (runMul x y).steps = 1 := ⟨rfl, rfl⟩

example {n : ℕ} (s : Shot n) : (runRecordMoment true s []).value = 1 := rfl

example {n : ℕ} (s : Shot n) : (runLabel ([] : SparseObservable n) s).value = 0 := rfl

example (e eta x b : ℝ) : (runFilter e eta x b).value = sparseFilter e eta x b := by
  by_cases hsmall : b ≤ 2 * e <;>
    by_cases hfiltered : |x| / Real.sqrt b ≤ 2 * eta * Real.sqrt e <;>
    simp [runFilter, sparseFilter, runMul, runSqrt, runAbs, runDiv, runIfLe,
      executionBind, executionPure, Bind.bind, Pure.pure, hsmall, hfiltered]

/-- Paper p.47, E14: correlation using the conditional single-shot output label. -/
def processCorrelation {n N : ℕ} (data : Fin N → Shot n × Shot n)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (P : (Fin n → Fin 4)) : ℝ :=
  (∑ l, effectProb (wordMatrix P) (namedWireTensor (fun i => shotProjector ((data l).1 i))) *
    effectProb H (pauliSnapshot (data l).2)) / (N : ℝ)

/-- Paper p.47, E14-E17: the actual learned predictor for a specified
hyperparameter, independent of the unknown channel except through recorded data. -/
def processPredictor {n N : ℕ} (k : ℕ) (e : ℝ)
    (data : Fin N → Shot n × Shot n) (H rho : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P ≤ k),
    sparseFilter e (pauliNorm 1 H) (processCorrelation data H P) ((1 / 3 : ℝ) ^ pauliWeight P) *
      effectProb (wordMatrix P) rho

/-- Paper p.5: exact number of retained input Pauli coefficients. -/
def lowWeightPauliCount (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min k n + 1), Nat.choose n j * 3 ^ j

/-- Paper p.34, Lemma 13: total variation distance between probability laws,
as the supremum of absolute measurable-event probability differences.
On probability laws the defining set contains zero and is bounded by one. -/
def classicalTVDistance {Omega : Type*} [MeasurableSpace Omega]
    (p0 p1 : Measure Omega) : ℝ :=
  sSup {v : ℝ | ∃ S : Set Omega, MeasurableSet S ∧
    v = |(p0 S).toReal - (p1 S).toReal|}

example {Omega : Type*} [MeasurableSpace Omega] (p : Measure Omega) :
    classicalTVDistance p p = 0 := by
  have h : {v : ℝ | ∃ S : Set Omega, MeasurableSet S ∧
      v = |(p S).toReal - (p S).toReal|} = {0} := by
    ext v
    simp only [sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS, hv⟩
      exact hv
    · intro hv
      exact ⟨∅, MeasurableSet.empty, hv⟩
  unfold classicalTVDistance
  rw [h]
  simp

end QAlgorithms.Papers.Independent.Claimed50.P03


