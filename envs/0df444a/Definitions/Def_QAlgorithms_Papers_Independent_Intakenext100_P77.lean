-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P77
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:53:54.563908+00:00
-- url     : https://prove2.me/theorems/fad284f3-e2b2-4e3b-b7c2-7f29cb68b89b
-- title:
--   Definitions for A Proof of the Security of Quantum Key Distribution
-- statement:
--   The objects the formalized statements of *A Proof of the Security of Quantum Key Distribution* (arXiv:quant-ph/9912053) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `classicalMutualInfo`: PDF p.24: classical mutual information.
--   - `given`: PDF p.24: conditional weights. Null outcomes give zero weights and are used only with zero multiplier or excluded by positive probability.
--   - `mutualAt`: PDF p.24: information in one conditional experiment.
--   - `averagedConditionalInfo`: PDF p.24: averaged conditional information.
--   - `JointIndependent`: PDF p.24: joint independence, with possibly different finite alphabets.
--   - `previous`: PDF p.24: coordinates preceding i.
--   - `others`: PDF pp.24--25: all coordinates except i.
--   - `finiteMax`: PDF p.24: finite maximum. The empty default is excluded in applications by m>=1 and a normalized source law.
--   - `coordinateMaximum`: PDF p.24: maximum of averaged conditional coordinate information.
--   - `disclosureMaximum`: PDF p.24: maximum over positive-probability disclosures only.
--   - `measuredWeights`: PDF p.25: Born-rule joint weights of source label and measurement output.
--   - `ensembleAccessibleInfo`: PDF p.25, Eq.(31): accessible information about a function of the label. For the normalized ensembles used below the value set is nonempty (identity POVM) and bounded by the label entropy. No maximum attainment is assumed.
--   - `conditionalAccessible`: PDF p.25: accessible information after one positive disclosure.
--   - `quantumDisclosureMaximum`: PDF p.25, Eq.(33): maximum of separately optimized conditional values.
--   - `Probes`: PDF p.5: probe coefficient vectors, not normalized states individually.
--   - `character`: PDF pp.5--6: binary character as a complex sign.
--   - `attackProbes`: PDF p.14, Eq.(12): probes computed from U and a fixed initial probe state. The attack is fixed before Alice's input.
--   - `coherentBitSymmetrize`: PDF pp.5,14, Eqs.(2),(13): coherent symmetrization with a retained mask. Alice's input is uniform; Bob's output is not assumed uniform.
--   - `testProbability`: PDF pp.14--15: the actual probability of the test outcome. A fixed basis and partition are absorbed into U's coordinates, with test positions first.
--   - `conditionOnTest`: PDF p.15, Eq.(17): normalization computed from the same attack using zero as reference information input. Used only at positive-probability transcripts.
--   - `conditionedSymmetric`: PDF pp.5--6,14--15: the specific conditional symmetrized probes from U.
--   - `probeDensity`: PDF p.6, Section 3.1: Eve's mixed state after tracing Bob out.
--   - `errorPurification`: PDF p.6, Section 3.2: the specific error-labelled purification, c=i+j.
--   - `probeFourierComponent`: PDF p.6, Definition 3.1: Fourier coefficient 2^(-n); no eta-hat for zero eta.
--   - `fourierWeight`: PDF p.6: squared Fourier-component norm.
--   - `conjugateProbes`: PDF p.17, Appendix E: change both information input and output bases of this same conditional map; test bases stay fixed.
--   - `probeErrorProbability`: PDF p.7: error probabilities averaged over Alice's uniform inputs.
--   - `distanceToSpan`: PDF p.8: minimum distance to a disclosed span, which contains zero.
--   - `fourierTail`: PDF pp.8,19: boundary-inclusive tail; doubled integer weights avoid truncated division at odd distance.
--   - `conjugateTail`: PDF p.8, Eq.(7): conjugate-basis error tail, with equality included.
--   - `codeLaw`: PDF pp.17--18: uniform coset i0+C, parametrized bijectively by c in C. A basis of C-perp gives exactly the source's full-rank parity check matrix.
--   - `codeStates`: PDF pp.7,18,21: the source's purified states on the fixed syndrome coset. The error register is retained: rho_i = |phi_i><phi_i| in Section 3.4 and Appendix G, not the less informative mixed marginal probeDensity from Section 3.1.
--   - `maskParity`: PDF pp.7,17: binary parity dot product.
--   - `parityInformation`: PDF pp.8,18,22: accessible parity information in the error-labelled purification, with disclosed C-perp and syndrome. v outside C-perp ensures a fair, nonempty pair of parity classes.
--   - `disclosedSpan`: PDF p.8: ECC rows and all other PA rows disclosed for bit j.
--   - `IndependentPA`: PDF pp.3,8: joint PA independence modulo the ECC rows.
--   - `keyDistance`: PDF pp.8--9: minimum distance over key bits with all others disclosed. Only m>=1 is used below, excluding the syntactic empty default.
--   - `wholeKeyInformation`: PDF p.9, Eq.(8): whole-key accessible information in the error-labelled purification on the uniform syndrome coset; ECC and PA are fixed independently of the unknown coset element. This also upper-bounds the actual mixed probes.
--   - `BalancedPartition`: PDF pp.10,27: all balanced choices of information positions.
--   - `informationErrors`: PDF p.27: errors in the information positions.
--   - `testErrors`: PDF p.27: errors in the complementary test positions.
--   - `samplingDeviation`: PDF pp.10,27--28: joint deviation under any full-error-string law at fixed basis, and an independent uniform balanced partition.
--   - `PassWeights`: PDF p.28: subnormalized joint pass/transcript weights.
--   - `luckyProbability`: PDF pp.28--29: joint probability of passing and information >= a.
--   - `testOnlyConditioned`: PDF p.15, immediately before Eq.(18): symmetrize only the test mask, with the common normalization from the full symmetrization. Individual rows need not be normalized before information symmetrization; their uniform average is.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, https://arxiv.org/abs/quant-ph/9912053v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

/-! Statements from quant-ph/9912053v1. Page numbers are PDF pages.
Local conditional experiments are constructed from a unitary, never postulated
to satisfy the desired information bound. Deferred nodes are in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder
open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.
open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)
open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.24: classical mutual information. -/
def classicalMutualInfo {Omega X Y : Type} [Fintype Omega] [Fintype X] [Fintype Y]
    (p : Omega → ℝ) (Xvar : Omega → X) (Yvar : Omega → Y) : ℝ :=
  shannon (pushLaw p Xvar) + shannon (pushLaw p Yvar) -
    shannon (pushLaw p (fun w => (Xvar w, Yvar w)))

/-- PDF p.24: conditional weights. Null outcomes give zero weights and are
used only with zero multiplier or excluded by positive probability. -/
def given {Omega Z : Type} [Fintype Omega] (p : Omega → ℝ)
    (Zvar : Omega → Z) (z : Z) : Omega → ℝ :=
  fun w => if Zvar w = z then p w / pushLaw p Zvar z else 0

/-- PDF p.24: information in one conditional experiment. -/
def mutualAt {Omega X Y Z : Type} [Fintype Omega] [Fintype X] [Fintype Y]
    (p : Omega → ℝ) (Xvar : Omega → X) (Yvar : Omega → Y)
    (Zvar : Omega → Z) (z : Z) : ℝ :=
  classicalMutualInfo (given p Zvar z) Xvar Yvar

/-- PDF p.24: averaged conditional information. -/
def averagedConditionalInfo {Omega X Y Z : Type} [Fintype Omega] [Fintype X]
    [Fintype Y] [Fintype Z] (p : Omega → ℝ) (Xvar : Omega → X)
    (Yvar : Omega → Y) (Zvar : Omega → Z) : ℝ :=
  ∑ z, pushLaw p Zvar z * mutualAt p Xvar Yvar Zvar z

/-- PDF p.24: joint independence, with possibly different finite alphabets. -/
def JointIndependent {Omega : Type} [Fintype Omega] {m : ℕ}
    {A : Fin m → Type} [∀ i, Fintype (A i)] (p : Omega → ℝ)
    (key : (i : Fin m) → Omega → A i) : Prop :=
  ∀ a : (i : Fin m) → A i,
    pushLaw p (fun w i => key i w) a = ∏ i, pushLaw p (key i) (a i)

/-- PDF p.24: coordinates preceding i. -/
def previous {Omega : Type} {m : ℕ} {A : Fin m → Type}
    (key : (i : Fin m) → Omega → A i) (i : Fin m) (w : Omega) :
    (j : {j : Fin m // j < i}) → A j.val := fun j => key j.val w

/-- PDF pp.24--25: all coordinates except i. -/
def others {Omega : Type} {m : ℕ} {A : Fin m → Type}
    (key : (i : Fin m) → Omega → A i) (i : Fin m) (w : Omega) :
    (j : {j : Fin m // j ≠ i}) → A j.val := fun j => key j.val w

/-- PDF p.24: finite maximum. The empty default is excluded in applications by
m>=1 and a normalized source law. -/
def finiteMax (s : Finset ℝ) : ℝ := if h : s.Nonempty then s.max' h else 0

/-- PDF p.24: maximum of averaged conditional coordinate information. -/
def coordinateMaximum {Omega E : Type} [Fintype Omega] [Fintype E]
    {m : ℕ} {A : Fin m → Type} [∀ i, Fintype (A i)]
    (p : Omega → ℝ) (key : (i : Fin m) → Omega → A i) (eve : Omega → E) : ℝ :=
  finiteMax (Finset.univ.image fun i : Fin m =>
    averagedConditionalInfo p (key i) eve (others key i))

/-- PDF p.24: maximum over positive-probability disclosures only. -/
def disclosureMaximum {Omega E : Type} [Fintype Omega] [Fintype E]
    {m : ℕ} {A : Fin m → Type} [∀ i, Fintype (A i)]
    (p : Omega → ℝ) (key : (i : Fin m) → Omega → A i) (eve : Omega → E) : ℝ :=
  finiteMax (Finset.univ.biUnion fun i : Fin m =>
    ((Finset.univ.filter fun a => 0 < pushLaw p (others key i) a).image
      fun a => mutualAt p (key i) eve (others key i) a))

/-- PDF p.25: Born-rule joint weights of source label and measurement output. -/
def measuredWeights {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (p : X → ℝ) (rho : X → Matrix Q Q ℂ) (M : Measurement Q) :
    X × Fin M.outcomes → ℝ :=
  fun z => p z.1 * effectProb (M.effect z.2) (rho z.1)

/-- PDF p.25, Eq.(31): accessible information about a function of the label.
For the normalized ensembles used below the value set is nonempty (identity
POVM) and bounded by the label entropy. No maximum attainment is assumed. -/
def ensembleAccessibleInfo {X K Q : Type} [Fintype X] [Fintype K] [Fintype Q]
    [DecidableEq Q] (p : X → ℝ) (rho : X → Matrix Q Q ℂ) (key : X → K) : ℝ :=
  sSup {v | ∃ M : Measurement Q,
    v = classicalMutualInfo (measuredWeights p rho M) (fun z => key z.1) Prod.snd}

/-- PDF p.25: accessible information after one positive disclosure. -/
def conditionalAccessible {X K Z Q : Type} [Fintype X] [Fintype K]
    [Fintype Q] [DecidableEq Q] (p : X → ℝ) (rho : X → Matrix Q Q ℂ)
    (key : X → K) (disclosed : X → Z) (z : Z) : ℝ :=
  ensembleAccessibleInfo (given p disclosed z) rho key

/-- PDF p.25, Eq.(33): maximum of separately optimized conditional values. -/
def quantumDisclosureMaximum {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    {m : ℕ} {A : Fin m → Type} [∀ i, Fintype (A i)]
    (p : X → ℝ) (rho : X → Matrix Q Q ℂ)
    (key : (i : Fin m) → X → A i) : ℝ :=
  finiteMax (Finset.univ.biUnion fun i : Fin m =>
    ((Finset.univ.filter fun a => 0 < pushLaw p (others key i) a).image
      fun a => conditionalAccessible p rho (key i) (others key i) a))

/-- PDF p.5: probe coefficient vectors, not normalized states individually. -/
abbrev Probes (n : ℕ) (Q : Type) := Qubits n → Qubits n → EuclideanSpace ℂ Q

/-- PDF pp.5--6: binary character as a complex sign. -/
def character {n : ℕ} (x y : Qubits n) : ℂ := if dotBits x y then -1 else 1

/-- PDF p.14, Eq.(12): probes computed from U and a fixed initial probe state.
The attack is fixed before Alice's input. -/
def attackProbes {n d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Qubits n) ℂ) (e0 : Fin d) : Probes n (Fin d) :=
  fun i j => WithLp.toLp 2 fun q => (U : Matrix _ _ ℂ) (q, j) (e0, i)

/-- PDF pp.5,14, Eqs.(2),(13): coherent symmetrization with a retained mask.
Alice's input is uniform; Bob's output is not assumed uniform. -/
def coherentBitSymmetrize {n : ℕ} {Q : Type} (E : Probes n Q) : Probes n (Qubits n × Q) :=
  fun i j => WithLp.toLp 2 fun z =>
    ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) * character (i + j) z.1 *
      E (i + z.1) (j + z.1) z.2

/-- PDF pp.14--15: the actual probability of the test outcome. A fixed basis
and partition are absorbed into U's coordinates, with test positions first. -/
def testProbability {n : ℕ} {Q : Type} [Fintype Q] (E : Probes (n + n) Q)
    (iT jT iI : Qubits n) : ℝ :=
  ∑ jI, ‖E (Fin.append iT iI) (Fin.append jT jI)‖ ^ 2

/-- PDF p.15, Eq.(17): normalization computed from the same attack using zero
as reference information input. Used only at positive-probability transcripts. -/
def conditionOnTest {n : ℕ} {Q : Type} [Fintype Q] (E : Probes (n + n) Q)
    (iT jT : Qubits n) : Probes n Q :=
  fun iI jI => ((Real.sqrt (testProbability E iT jT (fun _ => false)))⁻¹ : ℂ) •
    E (Fin.append iT iI) (Fin.append jT jI)

/-- PDF pp.5--6,14--15: the specific conditional symmetrized probes from U. -/
def conditionedSymmetric {n d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ)
    (e0 : Fin d) (iT jT : Qubits n) : Probes n (Qubits (n + n) × Fin d) :=
  conditionOnTest (coherentBitSymmetrize (attackProbes U e0)) iT jT

/-- PDF p.6, Section 3.1: Eve's mixed state after tracing Bob out. -/
def probeDensity {n : ℕ} {Q : Type} (E : Probes n Q) (i : Qubits n) : Matrix Q Q ℂ :=
  fun q r => ∑ j, E i j q * conj (E i j r)

/-- PDF p.6, Section 3.2: the specific error-labelled purification, c=i+j. -/
def errorPurification {n : ℕ} {Q : Type} (E : Probes n Q) (i : Qubits n) :
    EuclideanSpace ℂ (Q × Qubits n) := WithLp.toLp 2 fun z => E i (i + z.2) z.1

/-- PDF p.6, Definition 3.1: Fourier coefficient 2^(-n); no eta-hat for zero eta. -/
def probeFourierComponent {n : ℕ} {Q : Type} (E : Probes n Q) (l : Qubits n) :
    EuclideanSpace ℂ (Q × Qubits n) :=
  (((2 : ℝ) ^ n)⁻¹ : ℂ) • ∑ i, character l i • errorPurification E i

/-- PDF p.6: squared Fourier-component norm. -/
def fourierWeight {n : ℕ} {Q : Type} [Fintype Q] (E : Probes n Q)
    (l : Qubits n) : ℝ := ‖probeFourierComponent E l‖ ^ 2

/-- PDF p.17, Appendix E: change both information input and output bases of
this same conditional map; test bases stay fixed. -/
def conjugateProbes {n : ℕ} {Q : Type} (E : Probes n Q) : Probes n Q :=
  fun k l => (((2 : ℝ) ^ n)⁻¹ : ℂ) •
    ∑ i, ∑ j, (character i k * character j l) • E i j

/-- PDF p.7: error probabilities averaged over Alice's uniform inputs. -/
def probeErrorProbability {n : ℕ} {Q : Type} [Fintype Q] (E : Probes n Q)
    (c : Qubits n) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ i, ‖E i (i + c)‖ ^ 2

/-- PDF p.8: minimum distance to a disclosed span, which contains zero. -/
def distanceToSpan {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun w : S => hammingWeight (bitsOfZMod (v + w.val)))

/-- PDF pp.8,19: boundary-inclusive tail; doubled integer weights avoid
truncated division at odd distance. -/
def fourierTail {n : ℕ} {Q : Type} [Fintype Q] (E : Probes n Q) (dist : ℕ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => dist ≤ 2 * hammingWeight l), fourierWeight E l

/-- PDF p.8, Eq.(7): conjugate-basis error tail, with equality included. -/
def conjugateTail {n : ℕ} {Q : Type} [Fintype Q] (E : Probes n Q) (dist : ℕ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => dist ≤ 2 * hammingWeight c),
    probeErrorProbability (conjugateProbes E) c

/-- PDF pp.17--18: uniform coset i0+C, parametrized bijectively by c in C.
A basis of C-perp gives exactly the source's full-rank parity check matrix. -/
def codeLaw {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : C → ℝ :=
  fun _ => (Fintype.card C : ℝ)⁻¹

/-- PDF pp.7,18,21: the source's purified states on the fixed syndrome coset.
The error register is retained: rho_i = |phi_i><phi_i| in Section 3.4 and Appendix G,
not the less informative mixed marginal probeDensity from Section 3.1. -/
def codeStates {n : ℕ} {Q : Type} (E : Probes n Q)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (i0 : Fin n → ZMod 2) :
    C → Matrix (Q × Qubits n) (Q × Qubits n) ℂ :=
  fun c => pureDensity (errorPurification E (bitsOfZMod (i0 + c.val)))

/-- PDF pp.7,17: binary parity dot product. -/
def maskParity {n : ℕ} (v x : Fin n → ZMod 2) : Bool := decide (x ⬝ᵥ v = 1)

/-- PDF pp.8,18,22: accessible parity information in the error-labelled
purification, with disclosed C-perp and syndrome. v outside C-perp ensures
a fair, nonempty pair of parity classes. -/
def parityInformation {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (E : Probes n Q) (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (i0 v : Fin n → ZMod 2) : ℝ :=
  ensembleAccessibleInfo (codeLaw C) (codeStates E C i0) (fun c => maskParity v (i0 + c.val))

/-- PDF p.8: ECC rows and all other PA rows disclosed for bit j. -/
def disclosedSpan {n m : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (V : Fin m → Fin n → ZMod 2) (j : Fin m) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  binDual C ⊔ Submodule.span (ZMod 2) {v | ∃ k : Fin m, k ≠ j ∧ V k = v}

/-- PDF pp.3,8: joint PA independence modulo the ECC rows. -/
def IndependentPA {n m : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (V : Fin m → Fin n → ZMod 2) : Prop :=
  ∀ z : Fin m → ZMod 2, (∑ j, z j • V j) ∈ binDual C → z = 0

/-- PDF pp.8--9: minimum distance over key bits with all others disclosed.
Only m>=1 is used below, excluding the syntactic empty default. -/
def keyDistance {n m : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (V : Fin m → Fin n → ZMod 2) : ℕ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.inf' h (fun j => distanceToSpan (disclosedSpan C V j) (V j)) else 0

/-- PDF p.9, Eq.(8): whole-key accessible information in the error-labelled
purification on the uniform syndrome coset; ECC and PA are fixed independently
of the unknown coset element. This also upper-bounds the actual mixed probes. -/
def wholeKeyInformation {n m : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (E : Probes n Q) (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (i0 : Fin n → ZMod 2) (V : Fin m → Fin n → ZMod 2) : ℝ :=
  ensembleAccessibleInfo (codeLaw C) (codeStates E C i0) (fun c j => maskParity (V j) (i0 + c.val))

/-- PDF pp.10,27: all balanced choices of information positions. -/
abbrev BalancedPartition (n : ℕ) := {s : Finset (Fin (n + n)) // s.card = n}

/-- PDF p.27: errors in the information positions. -/
def informationErrors {n : ℕ} (s : BalancedPartition n) (c : Qubits (n + n)) : ℕ :=
  (s.val.filter fun q => c q = true).card

/-- PDF p.27: errors in the complementary test positions. -/
def testErrors {n : ℕ} (s : BalancedPartition n) (c : Qubits (n + n)) : ℕ :=
  ((Finset.univ \ s.val).filter fun q => c q = true).card

/-- PDF pp.10,27--28: joint deviation under any full-error-string law at fixed
basis, and an independent uniform balanced partition. -/
def samplingDeviation {n : ℕ} (p : Law (Qubits (n + n))) (allowed margin : ℝ) : ℝ :=
  (Fintype.card (BalancedPartition n) : ℝ)⁻¹ * ∑ s : BalancedPartition n, ∑ c,
    if (informationErrors s c : ℝ) ≥ n * (allowed + margin) ∧
        (testErrors s c : ℝ) ≤ n * allowed then p.prob c else 0

/-- PDF p.28: subnormalized joint pass/transcript weights. -/
structure PassWeights (T : Type) [Fintype T] where
  weight : T → ℝ
  nonnegative : ∀ t, 0 ≤ weight t
  total_le_one : ∑ t, weight t ≤ 1

/-- PDF pp.28--29: joint probability of passing and information >= a. -/
def luckyProbability {T : Type} [Fintype T] (p : PassWeights T)
    (info : T → ℝ) (a : ℝ) : ℝ := ∑ t, if a ≤ info t then p.weight t else 0

/-- PDF p.24: null conditioning really has the stated zero convention. -/
example {Omega Z : Type} [Fintype Omega] (p : Omega → ℝ)
    (Zvar : Omega → Z) (z : Z) (h : pushLaw p Zvar z = 0) : given p Zvar z = 0 := by
  funext w
  simp [given, h]

/-- PDF p.25: the measurement optimization has an admissible one-outcome POVM. -/
example {Q : Type} [Fintype Q] [DecidableEq Q] :
    (trivialMeasurement Q).outcomes = 1 := rfl

/-- PDF p.6: c labels the error rather than Bob's measured bit. -/
example {n : ℕ} {Q : Type} (E : Probes n Q) (i c : Qubits n) (q : Q) :
    errorPurification E i (q, c) = E i (i + c) q := rfl

/-- PDF p.15, immediately before Eq.(18): symmetrize only the test mask, with
the common normalization from the full symmetrization. Individual rows need not
be normalized before information symmetrization; their uniform average is. -/
def testOnlyConditioned {n d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n) : Probes n (Qubits n × Fin d) :=
  fun iI jI => WithLp.toLp 2 fun z =>
    ((Real.sqrt (testProbability (coherentBitSymmetrize (attackProbes U e0))
      iT jT (fun _ => false)))⁻¹ : ℂ) *
    ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) * character (iT + jT) z.1 *
    attackProbes U e0 (Fin.append (iT + z.1) iI) (Fin.append (jT + z.1) jI) z.2

end QAlgorithms.Papers.Independent.Intakenext100.P77


