-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
-- name    : QAlgorithms_Papers_Independent_Dependency50_P48
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:37:12.12522+00:00
-- url     : https://prove2.me/theorems/34f7186f-8a02-4d71-b7c1-5e36e1602862
-- title:
--   Definitions for The private classical capacity and quantum capacity of a quantum channel
-- statement:
--   The objects the formalized statements of *The private classical capacity and quantum capacity of a quantum channel* (arXiv:quant-ph/0304127) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsDilation`: Section 3, pp.8–9: a rectangular Stinespring isometry.
--   - `receiver`: Section 3, p.9: Bob's part of the fixed dilation.
--   - `complement`: Section 3, p.9: Eve receives the entire complement of the same dilation.
--   - `coherentMaximum`: Equations (36),(53): optimize over all density matrices. The imported coherent information is evaluated on the receiver channel via its canonical purification, equivalent to H(B)-H(E) for normalized inputs and isometric U. For isometries on finite nonempty registers the set is nonempty and bounded; the theorem asserts attainment, rather than assuming a maximizing input.
--   - `coherentRate`: Equations (36),(53): per-use quantity. The n=0 term is unused.
--   - `regularizedCoherentInformation`: Blocking interpretation invoked after (6), p.4: positive blocks only.
--   - `Decomposition`: Equation (31), p.9: finite ensemble of normalized, possibly mixed states.
--   - `Decomposition.average`: Equation (31): the barycenter is computed from the ensemble.
--   - `coherentDecompositionCosts`: Equation (31): coherent-information costs of density decompositions of rho. Distinct from Information100.P80.decompositionCosts, which costs bipartite operator decompositions by products of spectral norms.
--   - `privateInformation`: Equation (31), p.9. For density rho and isometric U the cost set is nonempty and bounded. Attainment of its minimum is included in the (30) theorem.
--   - `privateMaximum`: Equation (30): both the input and its decomposition may be mixed.
--   - `privateRate`: Equation (30): private information per use of a positive-length block.
--   - `cqPower`: Section 2, pp.3–4: memoryless cq outputs, with Q:E grouped.
--   - `MarkovLaw`: Theorem 1: all finite joint laws of T and X, without a cardinality bound.
--   - `weightedHolevo`: Section 1, pp.2–3: Holevo information from unnormalized cq blocks. Zero-mass labels contribute zero, so their conditional state is immaterial.
--   - `cqAdvantage`: Theorem 1: the output given (t,x) is W(x), independent of t. This constructs the Markov condition T→X→QE.
--   - `cqMaximum`: Theorem 1: finite-block objective; its attainment is asserted below.
--   - `cqRate`: Theorem 1, (6): cq objective per channel use.
--   - `PrivateTask`: Section 2: independent chosen message versus locally generated key.
--   - `WiretapProtocol`: Section 2, pp.3–4: private local randomness and a forward public transcript; Bob's final classical estimate is absorbed into the S-dependent POVM. The message/key marginal is uniform. No initial shared resource is a field. The accepted PrivateCode structures omit this public transcript and generated-key model, so they cannot replace this protocol.
--   - `WiretapProtocol.taskValid`: Section 2: message and randomness independent, or K a function of randomness.
--   - `WiretapProtocol.publicValid`: Section 2: an unassisted protocol has a constant public transcript.
--   - `WiretapProtocol.keyPublic`: Equations (3)–(5): the actual joint law of K and S.
--   - `WiretapProtocol.keyPublicEve`: Equation (5): classical KS blocks and Eve's entire complementary output.
--   - `WiretapProtocol.publicLeakage`: Equation (4): separate public leakage I(K;S).
--   - `WiretapProtocol.eveLeakage`: Equation (5): I(K;E|S)=H(KS)+H(SE)-H(S)-H(KSE).
--   - `WiretapProtocol.error`: Equation (3): Bob's actual probability of an incorrect message/key estimate.
--   - `WiretapProtocol.Good`: Sections 2–3: reliability and the two separate secrecy conditions. Quantum input validity allows all mixed, entangled block density matrices.
--   - `PrivateAchievable`: Section 2, p.4: every positive error/slack, then every sufficiently large positive blocklength, then a code of at least the requested rate.
--   - `cqCapacity`: Section 2: operational cq capacity, independent of the claimed formula.
--   - `quantumPrivateCapacity`: Section 3, p.9: operational private/key capacity, arbitrary mixed block inputs.
--   - `pureFidelity`: Equation (51) and Section 4: squared fidelity against a unit pure target.
--   - `PureGenerationCode`: Section 4, p.11: pure Alice-prepared bipartite input, CPTP Bob decoder. Distinct from Information100.P80.GenerationCode, whose input is a general mixed density matrix; this source explicitly chooses a pure preparation.
--   - `PureGenerationCode.fidelity`: Equation (35): squared fidelity to a normalized, arbitrary-dimensional target.
--   - `GenerationAchievable`: Section 4: unassisted entanglement-generation achievability.
--   - `generationCapacity`: Section 4: operational E, independent of the asserted regularization.
--   - `phaseSuperposition`: Lemma 4, p.10: equal-amplitude superposition with factor 1/sqrt(N).
--   - `fourierPhase`: Lemma 4: zero-based Fourier indices give the same complete residue system.
--   - `RealOverlap`: Printed complex inequalities are phase-aligned, real overlaps.
--   - `Typical`: Appendix A, p.16: strong typicality with the printed count tolerance.
--   - `wordProbability`: IID classical word law.
--   - `typicalMass`: Equation (11): probability mass of the typical set.
--   - `prunedProbability`: Section 2, p.6: pruned normalized law. All theorem uses give positive mass.
--   - `cqWord`: Appendix B: memoryless cq word output.
--   - `holevoInformation`: Section 1: I(X;Q) of the fixed normalized cq ensemble.
--   - `hswSize`: Appendix B, p.17: floor the exponential code size downward. For a negative nominal rate use the trivial one-message code.
--   - `hswExpectedError`: Appendix B: expectation over an IID pruned codebook and a uniform message.
--   - `block12`: Appendix C, pp.17–18: projector onto printed basis vectors 1,2 (Lean 0,1).
--   - `block34`: Appendix C: projector onto printed vectors 3,4 (Lean 2,3).
--   - `pi12`: Appendix C: uniform normalized density on the first two-dimensional block.
--   - `pi34`: Appendix C: uniform normalized density on the depolarized block.
--   - `separationChannel`: Appendix C: the explicit source channel, not a variable constrained by its goal.
--   - `separationDilation`: Appendix C: explicit dilation. One Kraus operator is the first-block projector; the four others are |a><b|/sqrt(2) on the second block.
--   - `perturbed12`: Appendix C: pi12-prime.
--   - `perturbed34`: Appendix C: pi34-prime, the negative coherent-information component.
--   - `IsometricCode`: Appendix D: orthonormal codewords, isometric encoder, CPTP decoder. The logical dimension is the same across a randomized code ensemble.
--   - `IsometricCode.logicalMap`: Appendix D, (59): logical map, leaving a separate reference untouched.
--   - `diagonalSchmidtVector`: Appendix D: general complex Schmidt coefficients in the displayed FIXED basis. Distinct from Information100.P03.schmidtVector, which constructs a vector from Schmidt probabilities and two arbitrary orthonormal families.
--   - `IsometricCode.fidelity`: Appendix D: squared entanglement fidelity at the maximally mixed logical input.
--   - `IsometricCode.density`: Appendix D: uniform codeword density V V†/k.
--   - `densityPower`: Appendix D: prescribed IID density, including off-diagonal entries.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, https://arxiv.org/abs/quant-ph/0304127v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Devetak, arXiv:quant-ph/0304127v6. Page numbers are PDF pages.
Accepted information primitives and paper-local operational models; arbitrary
positive logical dimensions; squared
fidelity. No identification with half-diamond operational capacity is asserted.
Compilation is pending the mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate
open Filter
open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)
attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}
variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]
variable [Fintype H] [DecidableEq H]

/-- Section 3, pp.8–9: a rectangular Stinespring isometry. -/
def IsDilation (U : Matrix (Q × E) P ℂ) : Prop := Uᴴ * U = 1

/-- Section 3, p.9: Bob's part of the fixed dilation. -/
def receiver (U : Matrix (Q × E) P ℂ) : Superop P Q :=
  fun rho => traceRight (U * rho * Uᴴ)

/-- Section 3, p.9: Eve receives the entire complement of the same dilation. -/
def complement (U : Matrix (Q × E) P ℂ) : Superop P E :=
  fun rho => traceLeft (U * rho * Uᴴ)

/-- Equations (36),(53): optimize over all density matrices. The imported
coherent information is evaluated on the receiver channel via its canonical
purification, equivalent to H(B)-H(E) for normalized inputs and isometric U. For isometries
on finite nonempty registers the set is nonempty and bounded; the theorem
asserts attainment, rather than assuming a maximizing input. -/
def coherentMaximum (U : Matrix (Q × E) P ℂ) : ℝ :=
  sSup {r | ∃ rho : Matrix P P ℂ, IsDensityMatrix rho ∧ r = coherentInformation (receiver U) rho}

/-- Equations (36),(53): per-use quantity. The n=0 term is unused. -/
def coherentRate (U : Matrix (Q × E) P ℂ) (n : ℕ) : ℝ :=
  coherentMaximum (dilationPower U n) / (n : ℝ)

/-- Blocking interpretation invoked after (6), p.4: positive blocks only. -/
def regularizedCoherentInformation (U : Matrix (Q × E) P ℂ) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧ r = coherentRate U n}

/-- Equation (31), p.9: finite ensemble of normalized, possibly mixed states. -/
structure Decomposition (A : Type*) [Fintype A] where
  size : ℕ
  positive : 0 < size
  probability : Fin size → ℝ
  nonnegative : ∀ j, 0 ≤ probability j
  normalized : ∑ j, probability j = 1
  state : Fin size → Matrix A A ℂ
  density : ∀ j, IsDensityMatrix (state j)

/-- Equation (31): the barycenter is computed from the ensemble. -/
def Decomposition.average (D : Decomposition P) : Matrix P P ℂ :=
  ∑ j, (D.probability j : ℂ) • D.state j

/-- Equation (31): coherent-information costs of density decompositions of rho.
Distinct from Information100.P80.decompositionCosts, which costs bipartite
operator decompositions by products of spectral norms. -/
def coherentDecompositionCosts (U : Matrix (Q × E) P ℂ) (rho : Matrix P P ℂ) : Set ℝ :=
  {r | ∃ D : Decomposition P, D.average = rho ∧
    r = ∑ j, D.probability j * coherentInformation (receiver U) (D.state j)}

/-- Equation (31), p.9. For density rho and isometric U the cost set is
nonempty and bounded. Attainment of its minimum is included in the (30) theorem. -/
def privateInformation (U : Matrix (Q × E) P ℂ) (rho : Matrix P P ℂ) : ℝ :=
  coherentInformation (receiver U) rho - sInf (coherentDecompositionCosts U rho)

/-- Equation (30): both the input and its decomposition may be mixed. -/
def privateMaximum (U : Matrix (Q × E) P ℂ) : ℝ :=
  sSup {r | ∃ rho : Matrix P P ℂ, IsDensityMatrix rho ∧ r = privateInformation U rho}

/-- Equation (30): private information per use of a positive-length block. -/
def privateRate (U : Matrix (Q × E) P ℂ) (n : ℕ) : ℝ :=
  privateMaximum (dilationPower U n) / (n : ℝ)

/-- Section 2, pp.3–4: memoryless cq outputs, with Q:E grouped. -/
def cqPower (W : X → Matrix (Q × E) (Q × E) ℂ) (n : ℕ) (x : Fin n → X) :
    Matrix ((Fin n → Q) × (Fin n → E)) ((Fin n → Q) × (Fin n → E)) ℂ :=
  fun be cf => ∏ i, W (x i) (be.1 i, be.2 i) (cf.1 i, cf.2 i)

/-- Theorem 1: all finite joint laws of T and X, without a cardinality bound. -/
structure MarkovLaw (A : Type*) [Fintype A] where
  auxiliarySize : ℕ
  positive : 0 < auxiliarySize
  joint : Fin auxiliarySize → A → ℝ
  nonnegative : ∀ t x, 0 ≤ joint t x
  normalized : ∑ t, ∑ x, joint t x = 1

/-- Section 1, pp.2–3: Holevo information from unnormalized cq blocks.
Zero-mass labels contribute zero, so their conditional state is immaterial. -/
def weightedHolevo {T A : Type*} [Fintype T] [Fintype A] [DecidableEq A]
    (mass : T → ℝ) (block : T → Matrix A A ℂ) : ℝ :=
  vnEntropy (∑ t, block t) - ∑ t, mass t * vnEntropy ((mass t : ℂ)⁻¹ • block t)

/-- Theorem 1: the output given (t,x) is W(x), independent of t.
This constructs the Markov condition T→X→QE. -/
def cqAdvantage (W : X → Matrix (Q × E) (Q × E) ℂ) (law : MarkovLaw X) : ℝ :=
  let mass := fun t => ∑ x, law.joint t x
  let joint := fun t => ∑ x, (law.joint t x : ℂ) • W x
  weightedHolevo mass (fun t => traceRight (joint t)) -
    weightedHolevo mass (fun t => traceLeft (joint t))

/-- Theorem 1: finite-block objective; its attainment is asserted below. -/
def cqMaximum (W : X → Matrix (Q × E) (Q × E) ℂ) : ℝ :=
  sSup {r | ∃ law : MarkovLaw X, r = cqAdvantage W law}

/-- Theorem 1, (6): cq objective per channel use. -/
def cqRate (W : X → Matrix (Q × E) (Q × E) ℂ) (n : ℕ) : ℝ :=
  cqMaximum (cqPower W n) / (n : ℝ)

/-- Section 2: independent chosen message versus locally generated key. -/
inductive PrivateTask where
  | message
  | key
  deriving DecidableEq

/-- Section 2, pp.3–4: private local randomness and a forward public transcript;
Bob's final classical estimate is absorbed into the S-dependent POVM.
The message/key marginal is uniform. No initial shared resource is a field.
The accepted PrivateCode structures omit this public transcript and generated-key
model, so they cannot replace this protocol. -/
structure WiretapProtocol (A B : Type*) [Fintype B] [DecidableEq B] where
  messages : ℕ
  messagesPositive : 0 < messages
  seeds : ℕ
  seedsPositive : 0 < seeds
  transcripts : ℕ
  transcriptsPositive : 0 < transcripts
  weight : Fin messages → Fin seeds → ℝ
  nonnegative : ∀ k m, 0 ≤ weight k m
  uniform : ∀ k, ∑ m, weight k m = (messages : ℝ)⁻¹
  input : Fin messages → Fin seeds → A
  transcript : Fin messages → Fin seeds → Fin transcripts
  decoder : Fin transcripts → Fin messages → Matrix B B ℂ
  measurement : ∀ s, IsPOVM (decoder s)

/-- Section 2: message and randomness independent, or K a function of randomness. -/
def WiretapProtocol.taskValid {A B : Type*} [Fintype B] [DecidableEq B]
    (C : WiretapProtocol A B) (task : PrivateTask) : Prop :=
  match task with
  | .message => ∃ p : Fin C.seeds → ℝ, (∀ m, 0 ≤ p m) ∧ (∑ m, p m = 1) ∧
      ∀ k m, C.weight k m = (C.messages : ℝ)⁻¹ * p m
  | .key => ∃ f : Fin C.seeds → Fin C.messages, ∀ k m, k ≠ f m → C.weight k m = 0

/-- Section 2: an unassisted protocol has a constant public transcript. -/
def WiretapProtocol.publicValid {A B : Type*} [Fintype B] [DecidableEq B]
    (C : WiretapProtocol A B) (assisted : Bool) : Prop :=
  assisted = true ∨ ∀ k m k2 m2, C.transcript k m = C.transcript k2 m2

/-- Equations (3)–(5): the actual joint law of K and S. -/
def WiretapProtocol.keyPublic {A B : Type*} [Fintype B] [DecidableEq B]
    (C : WiretapProtocol A B) : Fin C.messages × Fin C.transcripts → ℝ :=
  fun ks => ∑ m, if C.transcript ks.1 m = ks.2 then C.weight ks.1 m else 0

/-- Equation (5): classical KS blocks and Eve's entire complementary output. -/
def WiretapProtocol.keyPublicEve {A B F : Type*} [Fintype B] [DecidableEq B] [Fintype F]
    (C : WiretapProtocol A B) (W : A → Matrix (B × F) (B × F) ℂ) :
    Matrix ((Fin C.messages × Fin C.transcripts) × F)
      ((Fin C.messages × Fin C.transcripts) × F) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ m, if C.transcript a.1.1 m = a.1.2 then
      (C.weight a.1.1 m : ℂ) * traceLeft (W (C.input a.1.1 m)) a.2 b.2 else 0
  else 0

/-- Equation (4): separate public leakage I(K;S). -/
def WiretapProtocol.publicLeakage {A B : Type*} [Fintype B] [DecidableEq B]
    (C : WiretapProtocol A B) : ℝ :=
  let p := C.keyPublic
  shannon (fun k => ∑ s, p (k,s)) + shannon (fun s => ∑ k, p (k,s)) - shannon p

/-- Equation (5): I(K;E|S)=H(KS)+H(SE)-H(S)-H(KSE). -/
def WiretapProtocol.eveLeakage {A B F : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] (C : WiretapProtocol A B)
    (W : A → Matrix (B × F) (B × F) ℂ) : ℝ :=
  let joint := C.keyPublicEve W
  let regrouped : Matrix (Fin C.messages × (Fin C.transcripts × F))
      (Fin C.messages × (Fin C.transcripts × F)) ℂ :=
    fun a b => joint ((a.1,a.2.1),a.2.2) ((b.1,b.2.1),b.2.2)
  shannon C.keyPublic + vnEntropy (traceLeft regrouped) -
    shannon (fun s => ∑ k, C.keyPublic (k,s)) - vnEntropy joint

/-- Equation (3): Bob's actual probability of an incorrect message/key estimate. -/
def WiretapProtocol.error {A B F : Type*} [Fintype B] [DecidableEq B] [Fintype F]
    (C : WiretapProtocol A B) (W : A → Matrix (B × F) (B × F) ℂ) : ℝ :=
  ∑ k, ∑ m, C.weight k m *
    (1 - effectProb (C.decoder (C.transcript k m) k) (traceRight (W (C.input k m))))

/-- Sections 2–3: reliability and the two separate secrecy conditions.
Quantum input validity allows all mixed, entangled block density matrices. -/
def WiretapProtocol.Good {A B F : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] (C : WiretapProtocol A B)
    (W : A → Matrix (B × F) (B × F) ℂ) (allowed : A → Prop)
    (task : PrivateTask) (assisted : Bool) (eps : ℝ) : Prop :=
  C.taskValid task ∧ C.publicValid assisted ∧ (∀ k m, allowed (C.input k m)) ∧
    C.error W ≤ eps ∧ C.publicLeakage ≤ eps ∧ C.eveLeakage W ≤ eps

/-- Section 2, p.4: every positive error/slack, then every sufficiently large
positive blocklength, then a code of at least the requested rate. -/
def PrivateAchievable {A : ℕ → Type*}
    (W : (n : ℕ) → A n → Matrix ((Fin n → Q) × (Fin n → E))
      ((Fin n → Q) × (Fin n → E)) ℂ)
    (allowed : (n : ℕ) → A n → Prop) (task : PrivateTask) (assisted : Bool) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : WiretapProtocol (A n) (Fin n → Q),
      C.Good (W n) (allowed n) task assisted eps ∧
      r - delta ≤ Real.logb 2 (C.messages : ℝ) / (n : ℝ)

/-- Section 2: operational cq capacity, independent of the claimed formula. -/
def cqCapacity (W : X → Matrix (Q × E) (Q × E) ℂ)
    (task : PrivateTask) (assisted : Bool) : ℝ :=
  sSup {r | PrivateAchievable (fun n => cqPower W n) (fun _ _ => True) task assisted r}

/-- Section 3, p.9: operational private/key capacity, arbitrary mixed block inputs. -/
def quantumPrivateCapacity (U : Matrix (Q × E) P ℂ)
    (task : PrivateTask) (assisted : Bool) : ℝ :=
  sSup {r | PrivateAchievable
    (fun n (rho : Matrix (Fin n → P) (Fin n → P) ℂ) =>
      dilationPower U n * rho * (dilationPower U n)ᴴ)
    (fun _ rho => IsDensityMatrix rho) task assisted r}

/-- Equation (51) and Section 4: squared fidelity against a unit pure target. -/
def pureFidelity (psi : EuclideanSpace ℂ H) (rho : Matrix H H ℂ) : ℝ :=
  effectProb (pureDensity psi) rho

/-- Section 4, p.11: pure Alice-prepared bipartite input, CPTP Bob decoder.
Distinct from Information100.P80.GenerationCode, whose input is a general
mixed density matrix; this source explicitly chooses a pure preparation. -/
structure PureGenerationCode (A B : Type*) [Fintype A] [Fintype B] [DecidableEq B] where
  dimension : ℕ
  positive : 0 < dimension
  input : EuclideanSpace ℂ (Fin dimension × A)
  normalized : IsState input
  decoder : Superop B (Fin dimension)
  decoderChannel : IsChannel decoder

/-- Equation (35): squared fidelity to a normalized, arbitrary-dimensional target. -/
def PureGenerationCode.fidelity (C : PureGenerationCode P Q) (N : Superop P Q) : ℝ :=
  letI : NeZero C.dimension := ⟨Nat.ne_of_gt C.positive⟩
  pureFidelity (finiteMaxEntangled (Fin C.dimension))
    (idTensorSuperop (C.decoder ∘ N) (pureDensity C.input))

/-- Section 4: unassisted entanglement-generation achievability. -/
def GenerationAchievable (U : Matrix (Q × E) P ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : PureGenerationCode (Fin n → P) (Fin n → Q),
      1 - eps ≤ C.fidelity (receiver (dilationPower U n)) ∧
      r - delta ≤ Real.logb 2 (C.dimension : ℝ) / (n : ℝ)

/-- Section 4: operational E, independent of the asserted regularization. -/
def generationCapacity (U : Matrix (Q × E) P ℂ) : ℝ := sSup {r | GenerationAchievable U r}

/-- Lemma 4, p.10: equal-amplitude superposition with factor 1/sqrt(N). -/
def phaseSuperposition {N : ℕ} (v : Fin N → EuclideanSpace ℂ H) (gamma : Fin N → ℝ) :
    EuclideanSpace ℂ H :=
  ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • ∑ j, Complex.exp ((gamma j : ℂ) * Complex.I) • v j

/-- Lemma 4: zero-based Fourier indices give the same complete residue system. -/
def fourierPhase {N : ℕ} (s j : Fin N) : ℝ :=
  2 * Real.pi * (j : ℝ) * (s : ℝ) / (N : ℝ)

/-- Printed complex inequalities are phase-aligned, real overlaps. -/
def RealOverlap (a b : EuclideanSpace ℂ H) (lower : ℝ) : Prop :=
  (inner ℂ a b).im = 0 ∧ lower ≤ (inner ℂ a b).re

/-- Appendix A, p.16: strong typicality with the printed count tolerance. -/
def Typical (p : X → ℝ) (delta : ℝ) {n : ℕ} (x : Fin n → X) : Prop :=
  ∀ a, |((Finset.univ.filter (fun i => x i = a)).card : ℝ) - (n : ℝ) * p a| ≤ n * delta

/-- IID classical word law. -/
def wordProbability (p : X → ℝ) {n : ℕ} (x : Fin n → X) : ℝ := ∏ i, p (x i)

/-- Equation (11): probability mass of the typical set. -/
def typicalMass (p : X → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → X, if Typical p delta x then wordProbability p x else 0

/-- Section 2, p.6: pruned normalized law. All theorem uses give positive mass. -/
def prunedProbability (p : X → ℝ) (delta : ℝ) {n : ℕ} (x : Fin n → X) : ℝ :=
  if Typical p delta x then wordProbability p x / typicalMass p delta n else 0

/-- Appendix B: memoryless cq word output. -/
def cqWord (omega : X → Matrix Q Q ℂ) {n : ℕ} (x : Fin n → X) :
    Matrix (Fin n → Q) (Fin n → Q) ℂ := fun a b => ∏ i, omega (x i) (a i) (b i)

/-- Section 1: I(X;Q) of the fixed normalized cq ensemble. -/
def holevoInformation (p : X → ℝ) (omega : X → Matrix Q Q ℂ) : ℝ :=
  vnEntropy (∑ x, (p x : ℂ) • omega x) - ∑ x, p x * vnEntropy (omega x)

/-- Appendix B, p.17: floor the exponential code size downward. For a negative
nominal rate use the trivial one-message code. -/
def hswSize (information c cprime delta : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊Real.rpow 2 ((n : ℝ) * (information - 2 * (c + cprime * delta) * delta))⌋₊

/-- Appendix B: expectation over an IID pruned codebook and a uniform message. -/
def hswExpectedError (p : X → ℝ) (omega : X → Matrix Q Q ℂ) (delta : ℝ)
    (n nu : ℕ) (Y : (Fin nu → Fin n → X) → Fin nu →
      Matrix (Fin n → Q) (Fin n → Q) ℂ) : ℝ :=
  ∑ book : Fin nu → Fin n → X, (∏ s, prunedProbability p delta (book s)) *
    ((nu : ℝ)⁻¹ * ∑ s, (1 - effectProb (Y book s) (cqWord omega (book s))))

/-- Appendix C, pp.17–18: projector onto printed basis vectors 1,2 (Lean 0,1). -/
def block12 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun j => if j.val < 2 then 1 else 0

/-- Appendix C: projector onto printed vectors 3,4 (Lean 2,3). -/
def block34 : Matrix (Fin 4) (Fin 4) ℂ := 1 - block12

/-- Appendix C: uniform normalized density on the first two-dimensional block. -/
def pi12 : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • block12

/-- Appendix C: uniform normalized density on the depolarized block. -/
def pi34 : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • block34

/-- Appendix C: the explicit source channel, not a variable constrained by its goal. -/
def separationChannel : Superop (Fin 4) (Fin 4) :=
  fun rho => block12 * rho * block12 + (block34 * rho * block34).trace • pi34

/-- Appendix C: explicit dilation. One Kraus operator is the first-block
projector; the four others are |a><b|/sqrt(2) on the second block. -/
def separationDilation : Matrix (Fin 4 × Fin 5) (Fin 4) ℂ :=
  fun be a => if be.2.val = 0 then
    (if be.1.val < 2 ∧ be.1 = a then 1 else 0)
  else if be.1.val = 2 + (be.2.val - 1) / 2 ∧ a.val = 2 + (be.2.val - 1) % 2 then
    ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- Appendix C: pi12-prime. -/
def perturbed12 (eps : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 - eps : ℝ) : ℂ) • pi12 + (eps : ℂ) • pi34

/-- Appendix C: pi34-prime, the negative coherent-information component. -/
def perturbed34 (eps : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 - eps : ℝ) : ℂ) • pi34 + (eps : ℂ) • pi12

/-- Appendix D: orthonormal codewords, isometric encoder, CPTP decoder.
The logical dimension is the same across a randomized code ensemble. -/
structure IsometricCode (A B : Type*) [Fintype A] [Fintype B] [DecidableEq B] (k : ℕ) where
  encoding : Matrix A (Fin k) ℂ
  isometry : encodingᴴ * encoding = 1
  decoder : Superop B (Fin k)
  decoderChannel : IsChannel decoder

/-- Appendix D, (59): logical map, leaving a separate reference untouched. -/
def IsometricCode.logicalMap {k : ℕ} (C : IsometricCode P Q k) (N : Superop P Q) :
    Superop (Fin k) (Fin k) := C.decoder ∘ N ∘ conjSuperop C.encoding

/-- Appendix D: general complex Schmidt coefficients in the displayed FIXED basis.
Distinct from Information100.P03.schmidtVector, which constructs a vector from
Schmidt probabilities and two arbitrary orthonormal families. -/
def diagonalSchmidtVector {k : ℕ} (alpha : Fin k → ℂ) : EuclideanSpace ℂ (Fin k × Fin k) :=
  WithLp.toLp 2 fun ab => if ab.1 = ab.2 then alpha ab.1 else 0

/-- Appendix D: squared entanglement fidelity at the maximally mixed logical input. -/
def IsometricCode.fidelity {k : ℕ} (C : IsometricCode P Q k) (hk : 0 < k)
    (N : Superop P Q) : ℝ :=
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let phi := finiteMaxEntangled (Fin k)
  pureFidelity phi (idTensorSuperop (C.logicalMap N) (pureDensity phi))

/-- Appendix D: uniform codeword density V V†/k. -/
def IsometricCode.density {k : ℕ} (C : IsometricCode P Q k) : Matrix P P ℂ :=
  ((k : ℂ)⁻¹) • (C.encoding * C.encodingᴴ)

/-- Appendix D: prescribed IID density, including off-diagonal entries. -/
def densityPower (rho : Matrix P P ℂ) (n : ℕ) : Matrix (Fin n → P) (Fin n → P) ℂ :=
  fun a b => ∏ i, rho (a i) (b i)

/-! Sanity examples for the paper-local definition groups. -/

example (U : Matrix (Q × E) P ℂ) (a : Fin 0 → P)
    (be : (Fin 0 → Q) × (Fin 0 → E)) : dilationPower U 0 be a = 1 := by
  simp [dilationPower]

example (p : X → ℝ) (x : Fin 0 → X) : wordProbability p x = 1 := by simp [wordProbability]

example : shannon (fun _ : Unit => (1 : ℝ)) = 0 := by simp [shannon]

example (v : Fin 1 → EuclideanSpace ℂ H) : phaseSuperposition v (fun _ => 0) = v 0 := by
  simp [phaseSuperposition]

example : block12 0 0 = 1 ∧ block12 2 2 = 0 := by norm_num [block12, Matrix.diagonal]

example : separationDilation (0, 0) 0 = 1 := by simp [separationDilation]

example : perturbed12 0 = pi12 := by simp [perturbed12]

example {k : ℕ} (alpha : Fin k → ℂ) (j : Fin k) :
    diagonalSchmidtVector alpha (j,j) = alpha j := by simp [diagonalSchmidtVector]

example (rho : Matrix P P ℂ) (a b : Fin 1 → P) :
    densityPower rho 1 a b = rho (a 0) (b 0) := by simp [densityPower]

example (D : Decomposition P) : D.average = ∑ j, (D.probability j : ℂ) • D.state j := rfl

example (p : X → ℝ) (delta : ℝ) (n : ℕ) (h : typicalMass p delta n = 0)
    (x : Fin n → X) : prunedProbability p delta x = 0 := by simp [prunedProbability, h]

/-! Statements. Proposition 7 and the computability claim are deferred in HARD.md. -/

end QAlgorithms.Papers.Independent.Dependency50.P48


