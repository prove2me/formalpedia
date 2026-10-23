-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07
-- name    : QAlgorithms_Papers_Independent_Gap20_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T06:59:33.723927+00:00
-- url     : https://prove2.me/theorems/01ff38a9-781f-48ea-af3b-4c080cf2d4a5
-- title:
--   Definitions for Tema Con Variazioni: Quantum Channel Capacity
-- statement:
--   The objects the formalized statements of *Tema Con Variazioni: Quantum Channel Capacity* (arXiv:quant-ph/0311037) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TCChannel`: PDF pp.2--3: all CPTP maps on the full trace class, with no assistance.
--   - `codingSimulationDistance`: PDF p.3, (2): actual coding infimum, retaining infinity and the full cb norm.
--   - `blockError`: PDF p.3: block error for independent parallel uses of both channels.
--   - `rateRatio`: PDF p.3: nonnegative extended rate ratios avoid real limsup defaults.
--   - `AllSequenceRate`: PDF p.3, Definition 2.1: every diverging positive block sequence with limsup ratio at most R has vanishing computed error. Positivity of R is separate.
--   - `errorCapacity`: PDF p.3: supremum of positive rates; empty supremum is zero.
--   - `relativeCapacity`: PDF p.3: relative capacity with exactly this paper's limsup convention.
--   - `qubitReferenceCapacity`: PDF p.3: the ideal qubit fixes the unit bit.
--   - `Sporadic`: PDF pp.3--4: sporadic rates use just one diverging block sequence.
--   - `sporadicCapacity`: PDF pp.4,29: supremum, without asserting achievability at its endpoint.
--   - `finiteErrorCapacity`: PDF p.6: eventual full-cb error at most epsilon, including the exact-zero variant.
--   - `TraceClassBlockCode`: PDF pp.4--5: a physical unassisted code for a d-level system through n uses.
--   - `TraceClassBlockCode.effective`: PDF pp.4--5: the corrected channel, computed from its actual maps.
--   - `TraceClassBlockCode.error`: PDF pp.28--29: error of a particular code, not an independent parameter.
--   - `minimumFidelity`: PDF p.4, (4): minimum over the normalized finite unit sphere.
--   - `minimumFe`: PDF p.5, (8): infimum over density matrices, never all trace-class operators.
--   - `ordinaryNorm`: PDF pp.2,13: full induced trace norm, equivalently the dual operator norm.
--   - `finiteCbNorm`: PDF pp.2,13: full stabilized trace norm. In the finite lawful uses below the extended norm is finite, so conversion to a real cannot discard infinity.
--   - `FidelityCriterion`: PDF pp.4--5: the four fidelity criteria on one corrected logical channel.
--   - `fidelityValue`: PDF pp.4--5, (4)--(9): all overlaps are squared.
--   - `FidelityAchievable`: PDF p.4: one code for each positive n; the rate is the printed limsup.
--   - `fidelityCapacity`: PDF pp.4--5: capacity for a specified fidelity criterion.
--   - `ordinaryCapacity`: PDF pp.11--14: capacity from the ordinary induced trace-norm error.
--   - `ExponentialReliable`: PDF pp.6,29: positive exponential decay for all positive block lengths.
--   - `exponentialCapacity`: PDF pp.6,29: supremum of positive rates with some positive exponential exponent.
--   - `QuantumSource`: PDF pp.5--6: arbitrary nonzero finite block spaces, not a fixed tensor source.
--   - `QuantumSource.entropyRate`: PDF p.5, (10): extended limsup bit-entropy per positive block length.
--   - `QuantumSource.typical`: PDF p.19, (66): the full spectral typical window; no global eigenvalue bound.
--   - `QuantumSource.typicalMass`: PDF p.19: mass of the typical spectral restriction.
--   - `QuantumSource.typicalRestriction`: PDF p.19: normalized restriction is used only when its mass is positive, which QAEP guarantees eventually. Its unused zero-mass value is the zero operator.
--   - `QuantumSource.QAEP`: PDF p.19: QAEP means asymptotically all mass in every typical window.
--   - `QuantumSource.ExponentialDimension`: PDF pp.6,19: each source has its own exponential dimension bound.
--   - `SourceReliable`: PDF p.5: one pair of CPTP maps on the whole source space per n.
--   - `sourceEntropyCapacity`: PDF pp.5--6: source-restricted entropy capacity; downward closure of rate witnesses preserves the supremum and includes infinite entropy rates.
--   - `enlargedMixture`: PDF p.19, (67): actual direct-sum mixture, in consecutive coordinate blocks.
--   - `VariableSourceGenerationRate`: PDF pp.5,19--20: arbitrary normalized Gamma, compared with maximally entangled Omega.
--   - `variableSourceGenerationCapacity`: PDF pp.5,19--20: unassisted entanglement-generation capacity.
--   - `TraceClassBlockCode.Isometric`: PDF pp.7,20--22: isometric encoding on every trace-class argument.
--   - `isometricCapacity`: PDF pp.7,22: fidelity capacity restricted only at the encoder.
--   - `Subchannel`: PDF p.22: a CP trace-nonincreasing operation is linear and every finite amplification sends each density to a subnormalized density. The zero branch is allowed.
--   - `TraceClassForwardBlockCode`: PDF pp.22--23: instrument outcomes followed by their CPTP decoders. The branches sum to a channel; the summed unnormalized fidelities preclude postselection.
--   - `TraceClassForwardBlockCode.fidelity`: PDF p.23, (82): sum, with no branch normalization.
--   - `instrumentForwardCapacity`: PDF pp.22--23: the message budget may grow arbitrarily rapidly.
--   - `classicalIdentity`: PDF p.3: ideal classical bits are diagonal quantum channels.
--   - `compressedChannel`: PDF p.17, (54): compression into the actual k-dimensional isometric range.
--   - `firstCoordinatePinching`: PDF p.16, (51): firstCoordinatePinching off the first one-dimensional coordinate.
--   - `hashingBound`: PDF p.29, (107): exact expression, allowed to be negative.
--   - `hashingSupremum`: PDF p.29: supremum over actual prime-dimensional codes; negative bounds contribute zero to the nonnegative capacity lattice.
--   - `ErrorMonotone`: PDF pp.26--27: wasting one physical use or one requested output use.
--   - `ErrorSubadditive`: PDF p.27, (101): tensor blocking is subadditivity.
--   - `blockingEnvelope`: PDF p.27, (102): finite multisets of available blocks, with repetitions. Clipping at one makes the error finite even when no block packing is possible.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, https://arxiv.org/abs/quant-ph/0311037v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

/-! Kretschmann--Werner, quant-ph/0311037v1. Physical systems have arbitrary
nonempty orthonormal-basis index types, with completed l2 Hilbert spaces and
full nuclear trace class. Logical systems are finite and nonzero. The independent
paper override permits the pinned accepted paper modules imported here.
Only source theorems are admitted. Compilation and independent moderation pending. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)
open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-! The accepted basenames flagged by the mechanical check denote other concepts:
classical correlation simulation, PPT distillation, finite or zero-error capacities,
energy-constrained entropy, fixed-letter source instruments, and shape-indexed
pinching. They cannot replace Definition 2.1 or its arbitrary-system variations.
The distinct paper-local names below retain the original bodies; accepted trace
class, CPTP, tensor, norm, fidelity and Haar definitions remain imported above.
ASSESSMENT.json records exact declaration/type comparisons for each collision. -/

/-- PDF pp.2--3: all CPTP maps on the full trace class, with no assistance. -/
abbrev TCChannel (I J : Type) := {E : Operation I J // IsTraceClassChannel E}

/-- PDF p.3, (2): actual coding infimum, retaining infinity and the full cb norm. -/
def codingSimulationDistance {I J K L : Type} (T : Operation I J) (S : Operation K L) : ℝ≥0∞ :=
  ⨅ E : TCChannel K I, ⨅ D : TCChannel J L,
    stabilizedTraceClassNorm (fun X => D.val (T (E.val X)) - S X)

/-- PDF p.3: block error for independent parallel uses of both channels. -/
def blockError {I J K L : Type} (T : Operation I J) (S : Operation K L)
    (n m : ℕ+) : ℝ≥0∞ :=
  codingSimulationDistance (traceClassChannelPower T n) (traceClassChannelPower S m)

/-- PDF p.3: nonnegative extended rate ratios avoid real limsup defaults. -/
def rateRatio (n m : ℕ → ℕ+) (a : ℕ) : ℝ≥0∞ :=
  (m a : ℝ≥0∞) / (n a : ℝ≥0∞)

/-- PDF p.3, Definition 2.1: every diverging positive block sequence with
limsup ratio at most R has vanishing computed error. Positivity of R is separate. -/
def AllSequenceRate (delta : ℕ+ → ℕ+ → ℝ≥0∞) (R : ℝ) : Prop :=
  ∀ n m : ℕ → ℕ+, Tendsto (fun a => (n a : ℕ)) atTop atTop →
    Filter.limsup (rateRatio n m) atTop ≤ ENNReal.ofReal R →
    Tendsto (fun a => delta (n a) (m a)) atTop (𝓝 0)

/-- PDF p.3: supremum of positive rates; empty supremum is zero. -/
def errorCapacity (delta : ℕ+ → ℕ+ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ AllSequenceRate delta R}, ENNReal.ofReal R.val

/-- PDF p.3: relative capacity with exactly this paper's limsup convention. -/
def relativeCapacity {I J K L : Type} (T : Operation I J) (S : Operation K L) : ℝ≥0∞ :=
  errorCapacity (blockError T S)

/-- PDF p.3: the ideal qubit fixes the unit bit. -/
def qubitReferenceCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  relativeCapacity T (id : Operation (Fin 2) (Fin 2))

/-- PDF pp.3--4: sporadic rates use just one diverging block sequence. -/
def Sporadic (delta : ℕ+ → ℕ+ → ℝ≥0∞) (R : ℝ) : Prop :=
  ∃ n m : ℕ → ℕ+, Tendsto (fun a => (n a : ℕ)) atTop atTop ∧
    Filter.limsup (rateRatio n m) atTop = ENNReal.ofReal R ∧
    Tendsto (fun a => delta (n a) (m a)) atTop (𝓝 0)

/-- PDF pp.4,29: supremum, without asserting achievability at its endpoint. -/
def sporadicCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ Sporadic (blockError T (id : Operation (Fin 2) (Fin 2))) R},
    ENNReal.ofReal R.val

/-- PDF p.6: eventual full-cb error at most epsilon, including the exact-zero variant. -/
def finiteErrorCapacity {I J : Type} (T : Operation I J) (epsilon : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ∀ n m : ℕ → ℕ+,
    Tendsto (fun a => (n a : ℕ)) atTop atTop →
    Filter.limsup (rateRatio n m) atTop ≤ ENNReal.ofReal R →
    ∀ᶠ a in atTop, blockError T (id : Operation (Fin 2) (Fin 2)) (n a) (m a) ≤
      ENNReal.ofReal epsilon}, ENNReal.ofReal R.val

/-- PDF pp.4--5: a physical unassisted code for a d-level system through n uses. -/
structure TraceClassBlockCode {I J : Type} (T : Operation I J) (n d : ℕ) where
  enc : TCChannel (Fin d) (Fin n → I)
  dec : TCChannel (Fin n → J) (Fin d)

/-- PDF pp.4--5: the corrected channel, computed from its actual maps. -/
def TraceClassBlockCode.effective {I J : Type} {T : Operation I J} {n d : ℕ} (C : TraceClassBlockCode T n d) :
    Superop (Fin d) (Fin d) :=
  C.dec.val ∘ traceClassChannelPower T n ∘ C.enc.val

/-- PDF pp.28--29: error of a particular code, not an independent parameter. -/
def TraceClassBlockCode.error {I J : Type} {T : Operation I J} {n d : ℕ} (C : TraceClassBlockCode T n d) : ℝ≥0∞ :=
  stabilizedTraceClassNorm (fun X => C.effective X - X)

/-- PDF p.4, (4): minimum over the normalized finite unit sphere. -/
def minimumFidelity (d : ℕ) (T : Superop (Fin d) (Fin d)) : ℝ :=
  sInf {r : ℝ | ∃ psi : EuclideanSpace ℂ (Fin d), IsState psi ∧
    r = effectProb (pureDensity psi) (T (pureDensity psi))}

/-- PDF p.5, (8): infimum over density matrices, never all trace-class operators. -/
def minimumFe (d : ℕ) (T : Superop (Fin d) (Fin d)) : ℝ :=
  sInf {r : ℝ | ∃ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho ∧ r = fe rho T}

/-- PDF pp.2,13: full induced trace norm, equivalently the dual operator norm. -/
def ordinaryNorm (d : ℕ) (T : Superop (Fin d) (Fin d)) : ℝ :=
  sSup {r : ℝ | ∃ X : Matrix (Fin d) (Fin d) ℂ, traceNorm X ≤ 1 ∧ r = traceNorm (T X)}

/-- PDF pp.2,13: full stabilized trace norm. In the finite lawful uses below the
extended norm is finite, so conversion to a real cannot discard infinity. -/
def finiteCbNorm (d : ℕ) (T : Superop (Fin d) (Fin d)) : ℝ :=
  (stabilizedTraceClassNorm T).toReal

/-- PDF pp.4--5: the four fidelity criteria on one corrected logical channel. -/
inductive FidelityCriterion where
  | minimum | entanglement | average | channel

/-- PDF pp.4--5, (4)--(9): all overlaps are squared. -/
def fidelityValue (c : FidelityCriterion) (d : ℕ+) (T : Superop (Fin d) (Fin d)) : ℝ :=
  match c with
  | .minimum => minimumFidelity d T
  | .entanglement => minimumFe d T
  | .average => QuditFidelity.averageFidelity d d.pos T
  | .channel => QuditFidelity.entanglementFidelity d d.pos T

/-- PDF p.4: one code for each positive n; the rate is the printed limsup. -/
def FidelityAchievable {I J : Type} (T : Operation I J) (c : FidelityCriterion) (R : ℝ) : Prop :=
  ∃ d : ℕ → ℕ+, ∃ C : (a : ℕ) → TraceClassBlockCode T (a + 1) (d a),
    Filter.limsup (fun a => ENNReal.ofReal (Real.logb 2 (d a : ℝ) / (a + 1 : ℝ))) atTop =
      ENNReal.ofReal R ∧
    Tendsto (fun a => fidelityValue c (d a) (C a).effective) atTop (𝓝 1)

/-- PDF pp.4--5: capacity for a specified fidelity criterion. -/
def fidelityCapacity {I J : Type} (T : Operation I J) (c : FidelityCriterion) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ FidelityAchievable T c R}, ENNReal.ofReal R.val

/-- PDF pp.11--14: capacity from the ordinary induced trace-norm error. -/
def ordinaryCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ∃ d : ℕ → ℕ+,
    ∃ C : (n : ℕ) → TraceClassBlockCode T (n + 1) (d n),
    Filter.limsup (fun n => ENNReal.ofReal (Real.logb 2 (d n : ℝ) / (n + 1 : ℝ))) atTop =
      ENNReal.ofReal R ∧
    Tendsto (fun n => ordinaryNorm (d n) (fun X => (C n).effective X - X)) atTop (𝓝 0)},
    ENNReal.ofReal R.val

/-- PDF pp.6,29: positive exponential decay for all positive block lengths. -/
def ExponentialReliable {I J : Type} (T : Operation I J) (R : ℝ) : Prop :=
  ∃ (a C : ℝ), 0 < a ∧ 0 < C ∧
    ∃ codes : (n : ℕ) → TraceClassBlockCode T (n + 1) (2 ^ Nat.floor ((n + 1 : ℝ) * R)),
      ∀ᶠ n in atTop, (codes n).error ≤ ENNReal.ofReal (C * Real.exp (-a * (n + 1 : ℝ)))

/-- PDF pp.6,29: supremum of positive rates with some positive exponential exponent. -/
def exponentialCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ExponentialReliable T R}, ENNReal.ofReal R.val

/-- PDF pp.5--6: arbitrary nonzero finite block spaces, not a fixed tensor source. -/
structure QuantumSource where
  dimension : ℕ → ℕ+
  rho : (n : ℕ) → Matrix (Fin (dimension n)) (Fin (dimension n)) ℂ
  density : ∀ n, IsDensityMatrix (rho n)

/-- PDF p.5, (10): extended limsup bit-entropy per positive block length. -/
def QuantumSource.entropyRate (S : QuantumSource) : ℝ≥0∞ :=
  Filter.limsup (fun n => ENNReal.ofReal (vnEntropy (S.rho n) / (n + 1 : ℝ))) atTop

/-- PDF p.19, (66): the full spectral typical window; no global eigenvalue bound. -/
def QuantumSource.typical (S : QuantumSource) (R epsilon : ℝ) (n : ℕ) :=
  cfc (fun x : ℝ => if (2 : ℝ) ^ (-(n + 1 : ℝ) * (R + epsilon)) ≤ x ∧
    x ≤ (2 : ℝ) ^ (-(n + 1 : ℝ) * (R - epsilon)) then 1 else 0) (S.rho n)

/-- PDF p.19: mass of the typical spectral restriction. -/
def QuantumSource.typicalMass (S : QuantumSource) (R epsilon : ℝ) (n : ℕ) : ℝ :=
  ((S.typical R epsilon n * S.rho n * S.typical R epsilon n).trace).re

/-- PDF p.19: normalized restriction is used only when its mass is positive,
which QAEP guarantees eventually. Its unused zero-mass value is the zero operator. -/
def QuantumSource.typicalRestriction (S : QuantumSource) (R epsilon : ℝ) (n : ℕ) :=
  ((S.typicalMass R epsilon n : ℂ)⁻¹) •
    (S.typical R epsilon n * S.rho n * S.typical R epsilon n)

/-- PDF p.19: QAEP means asymptotically all mass in every typical window. -/
def QuantumSource.QAEP (S : QuantumSource) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ S.entropyRate = ENNReal.ofReal R ∧
    ∀ epsilon : ℝ, 0 < epsilon → Tendsto (S.typicalMass R epsilon) atTop (𝓝 1)

/-- PDF pp.6,19: each source has its own exponential dimension bound. -/
def QuantumSource.ExponentialDimension (S : QuantumSource) : Prop :=
  ∃ tau : ℝ, 0 < tau ∧ ∀ n, (S.dimension n : ℝ) ≤ tau ^ (n + 1)

/-- PDF p.5: one pair of CPTP maps on the whole source space per n. -/
def SourceReliable {I J : Type} (T : Operation I J) (S : QuantumSource) : Prop :=
  ∃ C : (n : ℕ) → TraceClassBlockCode T (n + 1) (S.dimension n),
    Tendsto (fun n => fe (S.rho n) (C n).effective) atTop (𝓝 1)

/-- PDF pp.5--6: source-restricted entropy capacity; downward closure of rate
witnesses preserves the supremum and includes infinite entropy rates. -/
def sourceEntropyCapacity {I J : Type} (T : Operation I J) (P : QuantumSource → Prop) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ∃ S : QuantumSource,
    P S ∧ SourceReliable T S ∧ ENNReal.ofReal R ≤ S.entropyRate}, ENNReal.ofReal R.val

/-- PDF p.19, (67): actual direct-sum mixture, in consecutive coordinate blocks. -/
def enlargedMixture (d k : ℕ+) (epsilon : ℝ) : Matrix (Fin (d + k : ℕ+)) (Fin (d + k : ℕ+)) ℂ :=
  Matrix.diagonal fun i => if i.val < (d : ℕ) then
    (((1 - epsilon) / (d : ℝ) : ℝ) : ℂ) else ((epsilon / (k : ℝ) : ℝ) : ℂ)

/-- PDF pp.5,19--20: arbitrary normalized Gamma, compared with maximally entangled Omega. -/
def VariableSourceGenerationRate {I J : Type} (T : Operation I J) (R : ℝ) : Prop :=
  ∃ d : ℕ → ℕ+, ∃ C : (n : ℕ) → TraceClassBlockCode T (n + 1) (d n),
    ∃ gamma : (n : ℕ) → EuclideanSpace ℂ (Fin (d n) × Fin (d n)),
    (∀ n, IsState (gamma n)) ∧
    Filter.limsup (fun n => ENNReal.ofReal (Real.logb 2 (d n : ℝ) / (n + 1 : ℝ))) atTop =
      ENNReal.ofReal R ∧
    Tendsto (fun n => letI : Nonempty (Fin (d n)) := ⟨⟨0,(d n).pos⟩⟩
      effectProb (pureDensity (finiteMaxEntangled (Fin (d n))))
        (idTensorSuperop (C n).effective (pureDensity (gamma n)))) atTop (𝓝 1)

/-- PDF pp.5,19--20: unassisted entanglement-generation capacity. -/
def variableSourceGenerationCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ VariableSourceGenerationRate T R}, ENNReal.ofReal R.val

/-- PDF pp.7,20--22: isometric encoding on every trace-class argument. -/
def TraceClassBlockCode.Isometric {I J : Type} {T : Operation I J} {n d : ℕ} (C : TraceClassBlockCode T n d) : Prop :=
  ∃ V : Hilbert (Fin d) →ₗᵢ[ℂ] Hilbert (Fin n → I),
    ∀ X, IsTraceClass X → C.enc.val X = conjugateKernel (isometryCoeff V) X

/-- PDF pp.7,22: fidelity capacity restricted only at the encoder. -/
def isometricCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ∃ d : ℕ → ℕ+,
    ∃ C : (n : ℕ) → TraceClassBlockCode T (n + 1) (d n),
    (∀ n, (C n).Isometric) ∧
    Filter.limsup (fun n => ENNReal.ofReal (Real.logb 2 (d n : ℝ) / (n + 1 : ℝ))) atTop =
      ENNReal.ofReal R ∧
    Tendsto (fun n => fidelityValue .channel (d n) (C n).effective) atTop (𝓝 1)},
    ENNReal.ofReal R.val

/-- PDF p.22: a CP trace-nonincreasing operation is linear and every finite
amplification sends each density to a subnormalized density. The zero branch is allowed. -/
def Subchannel {I J : Type} (E : Operation I J) : Prop :=
  TraceLinear E ∧ ∀ k : ℕ, ∀ rho : State (I × Fin k),
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ ∃ sigma : State (J × Fin k),
      tensorApply E rho.coefficients = (p : ℂ) • sigma.coefficients

/-- PDF pp.22--23: instrument outcomes followed by their CPTP decoders.
The branches sum to a channel; the summed unnormalized fidelities preclude postselection. -/
structure TraceClassForwardBlockCode {I J : Type} (T : Operation I J) (n d messages : ℕ) where
  enc : Fin messages → Operation (Fin d) (Fin n → I)
  branch : ∀ j, Subchannel (enc j)
  total : IsTraceClassChannel (fun X => ∑ j, enc j X)
  dec : Fin messages → TCChannel (Fin n → J) (Fin d)

/-- PDF p.23, (82): sum, with no branch normalization. -/
def TraceClassForwardBlockCode.fidelity {I J : Type} {T : Operation I J} {n d messages : ℕ}
    (C : TraceClassForwardBlockCode T n d messages) (hd : 0 < d) : ℝ :=
  ∑ j, QuditFidelity.entanglementFidelity d hd
    ((C.dec j).val ∘ traceClassChannelPower T n ∘ C.enc j)

/-- PDF pp.22--23: the message budget may grow arbitrarily rapidly. -/
def instrumentForwardCapacity {I J : Type} (T : Operation I J) (budget : ℕ → ℕ+ → Prop) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 < R ∧ ∃ d messages : ℕ → ℕ+,
    (∀ n, budget n (messages n)) ∧
    ∃ C : (n : ℕ) → TraceClassForwardBlockCode T (n + 1) (d n) (messages n),
    Filter.limsup (fun n => ENNReal.ofReal (Real.logb 2 (d n : ℝ) / (n + 1 : ℝ))) atTop =
      ENNReal.ofReal R ∧
    Tendsto (fun n => (C n).fidelity (d n).pos) atTop (𝓝 1)}, ENNReal.ofReal R.val

/-- PDF p.3: ideal classical bits are diagonal quantum channels. -/
def classicalIdentity (d : ℕ) : Operation (Fin d) (Fin d) :=
  fun X => Matrix.diagonal (Matrix.diag X)

/-- PDF p.17, (54): compression into the actual k-dimensional isometric range. -/
def compressedChannel {d k : ℕ} (V : Matrix (Fin d) (Fin k) ℂ)
    (T : Superop (Fin d) (Fin d)) : Superop (Fin k) (Fin k) :=
  fun X => let Y := T (V * X * V.conjTranspose)
    V.conjTranspose * Y * V + ((((1 - V * V.conjTranspose) * Y).trace / (k : ℂ))) • 1

/-- PDF p.16, (51): firstCoordinatePinching off the first one-dimensional coordinate. -/
def firstCoordinatePinching (d : ℕ+) : Superop (Fin d) (Fin d) :=
  let P := pureDensity (ket (⟨0,d.pos⟩ : Fin d))
  fun X => P * X * P + (1 - P) * X * (1 - P)

/-- PDF p.29, (107): exact expression, allowed to be negative. -/
def hashingBound (N d : ℕ) (delta : ℝ) : ℝ :=
  Real.logb 2 d / N * (1 - 4 * Real.exp 1 * delta) - binEntropy2 (2 * Real.exp 1 * delta) / N

/-- PDF p.29: supremum over actual prime-dimensional codes; negative bounds
contribute zero to the nonnegative capacity lattice. -/
def hashingSupremum {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ N : ℕ+, ⨆ d : {d : ℕ // Nat.Prime d}, ⨆ C : TraceClassBlockCode T N d.val,
    ⨆ _h : C.error < ENNReal.ofReal (1 / (2 * Real.exp 1)),
      ENNReal.ofReal (hashingBound N d.val C.error.toReal)

/-- PDF pp.26--27: wasting one physical use or one requested output use. -/
def ErrorMonotone (delta : ℕ+ → ℕ+ → ℝ≥0∞) : Prop :=
  ∀ n m, delta (n + 1) m ≤ delta n m ∧ delta n m ≤ delta n (m + 1)

/-- PDF p.27, (101): tensor blocking is subadditivity. -/
def ErrorSubadditive (delta : ℕ+ → ℕ+ → ℝ≥0∞) : Prop :=
  ∀ n k m l, delta (n + k) (m + l) ≤ delta n m + delta k l

/-- PDF p.27, (102): finite multisets of available blocks, with repetitions.
Clipping at one makes the error finite even when no block packing is possible. -/
def blockingEnvelope (N : ℕ → ℕ+) (epsilon : ℕ → ℝ≥0) (n m : ℕ+) : ℝ≥0∞ :=
  min 1 (sInf {c : ℝ≥0∞ | ∃ blocks : List ℕ,
    (m : ℕ) ≤ (blocks.map (fun j => (N j : ℕ))).sum ∧
    (blocks.map (fun j => (N j : ℕ))).sum ≤ (n : ℕ) ∧
    c = (blocks.map (fun j => (epsilon j : ℝ≥0∞))).sum})

/-! Definitional sanity checks pin tensor powers, dimensions, sums, and zero endpoints.
They prove no paper result. -/

example (n m : ℕ → ℕ+) (a : ℕ) :
    rateRatio n m a = (m a : ℝ≥0∞) / (n a : ℝ≥0∞) := rfl

example {I J : Type} {T : Operation I J} {n d : ℕ} (C : TraceClassBlockCode T n d) (X : Matrix (Fin d) (Fin d) ℂ) :
    C.effective X = C.dec.val (traceClassChannelPower T n (C.enc.val X)) := rfl

example (S : QuantumSource) (R epsilon : ℝ) (n : ℕ)
    (h : S.typicalMass R epsilon n = 0) : S.typicalRestriction R epsilon n = 0 := by
  simp [QuantumSource.typicalRestriction, h]

example (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    classicalIdentity d X = Matrix.diagonal (Matrix.diag X) := rfl

example (d k : ℕ+) (epsilon : ℝ) (i : Fin (d + k : ℕ+)) (h : i.val < (d : ℕ)) :
    enlargedMixture d k epsilon i i = (((1 - epsilon) / (d : ℝ) : ℝ) : ℂ) := by
  unfold enlargedMixture
  rw [Matrix.diagonal_apply_eq, if_pos h]

example (N d : ℕ) : hashingBound N d 0 = Real.logb 2 d / N := by
  simp [hashingBound, binEntropy2]

example (N : ℕ → ℕ+) (epsilon : ℕ → ℝ≥0) (n m : ℕ+) :
    blockingEnvelope N epsilon n m ≤ 1 := min_le_left _ _

example (d : ℕ) (T : Superop (Fin d) (Fin d)) :
    compressedChannel (1 : Matrix (Fin d) (Fin d) ℂ) T = T := by
  funext X
  simp [compressedChannel]

example : (enlargedMixture 1 1 (1 / 2)).trace = 1 := by
  norm_num [enlargedMixture, Matrix.trace, Fin.sum_univ_two]

section HaarTwirlNorm

open scoped Matrix.Norms.L2Operator

end HaarTwirlNorm

end QAlgorithms.Papers.Independent.Gap20.P07


