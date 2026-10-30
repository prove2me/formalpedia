-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41
-- name    : QAlgorithms_Papers_Independent_Advance50_P41
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:04:28.73581+00:00
-- url     : https://prove2.me/theorems/90e3bda7-7146-467e-b9c4-e63a790ff1e5
-- title:
--   Definitions for Entanglement-Assisted Quantum Data Compression
-- statement:
--   The objects the formalized statements of *Entanglement-Assisted Quantum Data Compression* (arXiv:1901.06346) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProductPureSource`: PDF p.1, (1): data for a countably indexed product-pure source. `Valid` removes null letters and requires normalized vectors.
--   - `ProductPureSource.Valid`: PDF p.1: supported probabilities are strictly positive; no H(X) premise.
--   - `ProductPureSource.joint`: PDF p.1, (1): the joint pure source vector on A,C.
--   - `ProductPureSource.adjacent`: PDF p.2, Definition 2: nonorthogonality of supported joint vectors.
--   - `IrreducibleLabel`: PDF p.2: the canonical component label is the equivalence closure of nonorthogonality, rather than an arbitrary readable function of X.
--   - `ProductPureSource.label`: PDF p.2, (3): the canonical label y(x).
--   - `ProductPureSource.componentProbability`: PDF p.2: probability of an occupied component.
--   - `ProductPureSource.conditionalProbability`: PDF p.2: conditional component law; division is used only at positive component mass in the structural theorem.
--   - `ProductPureSource.fiberSpan`: PDF p.2: span of a fiber of a labeling h.
--   - `ProductPureSource.IsDecomposition`: PDF p.2, Definition 2: every fiber is nonempty and irreducible, and spans of distinct fibers are orthogonal. Surjectivity excludes empty labels.
--   - `ProductPureSource.Irreducible`: PDF p.2, Definition 2: a nonempty ensemble cannot split orthogonally.
--   - `ProductPureSource.averageA`: PDF pp.1,2: actual average density of A.
--   - `ProductPureSource.averageAC`: PDF pp.1,2: actual average density of AC.
--   - `ProductPureSource.blockC`: PDF p.2: the y diagonal block of the canonical CY marginal. Blocks are subnormalized; their entropies already include -q(y)log q(y).
--   - `ProductPureSource.blockA`: PDF p.2: the y diagonal block of the canonical AY marginal.
--   - `ProductPureSource.blockAC`: PDF p.2: the y diagonal block of the canonical ACY marginal.
--   - `ProductPureSource.entropyA`: PDF p.1: entropy of A in bits.
--   - `ProductPureSource.entropyY`: PDF p.2: Shannon entropy of the canonical finite occupied label Y. For valid sources the orthogonal nonzero component spans imply finite Y, even when X is infinite. This is not an assumption on H(X).
--   - `ProductPureSource.entropyCY`: PDF p.2: entropy of the actual block-diagonal CY marginal, in bits.
--   - `ProductPureSource.entropyAY`: PDF p.2: entropy of the actual block-diagonal AY marginal, in bits.
--   - `ProductPureSource.entropyACY`: PDF p.2: entropy of the actual block-diagonal ACY marginal, in bits.
--   - `ProductPureSource.quantumCorner`: PDF p.2, Theorem 3: communication corner computed from the source.
--   - `ProductPureSource.entanglementCorner`: PDF p.2, Theorem 3: simultaneous entanglement-consumption corner.
--   - `ProductPureSource.Blind`: PDF p.2: blind means identical pure densities, allowing global phases.
--   - `ProductPureSource.Visible`: PDF p.2: visible side information is an orthonormal encoding of X.
--   - `independentDiscreteLaw`: PDF p.1: the actual independent product of two discrete probability laws.
--   - `productSource`: PDF p.1: product source, with A1,A2 regrouped and C1,C2 regrouped.
--   - `ProductPureSource.wordProbability`: PDF p.1: probability of an n-letter memoryless input word.
--   - `ProductPureSource.wordVector`: PDF p.1: the complete A^n C^n pure target, registers grouped by party.
--   - `PreservedSideQuantumCode`: PDF pp.1,2, Section II: arbitrary CPTP encoder and decoder, fixed independently of the inaccessible word; actual positive resource dimensions. The side register is retained by Alice. n is a positive block in sequences.
--   - `PreservedSideQuantumCode.quantumRate`: PDF pp.1,2: quantum cost is the actual log-dimension per source letter.
--   - `PreservedSideQuantumCode.entanglementRate`: PDF p.2: initial consumed entanglement, with no output-ebit subtraction.
--   - `PreservedSideQuantumCode.input`: PDF pp.1,2: source together with Alice's and Bob's Bell halves. The input order is ((A^n,C^n),A0),B0.
--   - `PreservedSideQuantumCode.output`: PDF p.2, (2): actual decoded joint Ahat^n Chat^n state. Bob's B0 is untouched during encoding; Chat^n is untouched during decoding.
--   - `PreservedSideQuantumCode.fidelity`: PDF p.2, (2): average ROOT fidelity of the complete X,A,C output.
--   - `QuantumCodeSequence`: PDF p.2: one code for every positive block length; n indexes length n+1.
--   - `ProductPureSource.OptimalQuantumCorner`: PDF p.2: minimum quantum rate with unlimited initial entanglement and simultaneous attainment of the stated consumption rate. The converse imposes no convergence or bound on the entanglement rate.
--   - `ProductPureSource.SumRateConverse`: PDF pp.4,5: sum-rate weak converse for any successful finite-rate sequence.
--   - `Extraction`: PDF p.3, Definition 4: finite Stinespring isometries, with the input and reconstructed output dimensions A,C fixed.
--   - `Extraction.letter`: PDF p.3: the output state on Ahat,Chat,W for a source letter.
--   - `Extraction.retained`: PDF p.3: discard W, retaining the full reconstructed A,C pair.
--   - `Extraction.fidelity`: PDF p.3: fidelity constraint in Definition 4, including epsilon>=1.
--   - `Extraction.objective`: PDF p.3: I(X:Chat W) as a finite-output Holevo entropy difference. This avoids forming H(X)-H(X|Chat W) on countable alphabets.
--   - `extractionValues`: PDF p.3: the bounded-environment optimization-value set. Its nonemptiness, boundedness, exact maximum and equivalence to arbitrary finite environments are conclusions of `definition4_attainment`, not assumed source fields.
--   - `extractionInformation`: PDF p.3, Definition 4: real supremum on the compact bounded-environment model. Under Valid and eps>=0 the value set is nonempty and bounded above; this guard is established in the accompanying attainment theorem.
--   - `IsFiniteRectangularInstrument`: PDF p.5, modified model: a finite CP instrument. Joint Kraus normalization makes each branch trace-nonincreasing and the sum trace-preserving.
--   - `BlindClassicalCode`: PDF p.5, Theorem 8 model: Alice receives a blind A-source, extracts its canonical Y locally, and retains Y^n. The instrument acts on A^n A0; its classical outcome alone is sent. Bob decodes his Bell half conditionally. There is no quantum message and no classical-alphabet dimension cap.
--   - `BlindClassicalCode.classicalRate`: PDF p.5: actual classical bits per source letter.
--   - `BlindClassicalCode.entanglementRate`: PDF p.5: actual initial entanglement consumed per source letter.
--   - `BlindClassicalCode.input`: PDF p.5: blind input A^n,A0,B0; only preshared entanglement at Bob.
--   - `BlindClassicalCode.output`: PDF p.5: sum of genuine quantum-instrument branches, decoded using Bob's entangled half; output order Ahat^n,Yhat^n.
--   - `BlindClassicalCode.target`: PDF p.5: complete AY target, with the canonical component word retained.
--   - `BlindClassicalCode.fidelity`: PDF p.5: same average joint root-fidelity criterion as Section II.
--   - `BlindClassicalAchievable`: PDF p.5: actual classical/entanglement rates converge along all positive block lengths; no budget interpretation is substituted.
--   - `separationPlus`: PDF p.5: |+> in the separation example. Reindex the accepted Fin-2 plus state on the Bool computational basis, false=0 and true=1.
--   - `examplePsi`: PDF p.5: source-letter A vectors 0,1,+.
--   - `separationSideVectors`: PDF p.5: original side vectors 0,0,+.
--   - `exampleModifiedSigma`: PDF p.5: transformed side vectors 0,1,+.
--   - `exampleWeights`: PDF p.5: probabilities 1/2-t,1/2-t,2t.
--   - `separationLaw`: PDF p.5: the normalized law on the source's open parameter interval.
--   - `exampleOriginal`: PDF p.5: the original three-letter source.
--   - `exampleModified`: PDF p.5: the three-letter source after the local controlled-NOT.
--   - `exampleDensity`: PDF p.5: a finite coefficient average for the explicit parameter family, including t=0 for computing the one-sided entropy limit.
--   - `exampleOriginalRate`: PDF p.5: (S(A)+S(AC)-S(C))/2 for the original ensemble.
--   - `exampleModifiedRate`: PDF p.5: (S(A)+S(ACprime)-S(Cprime))/2 after controlled-NOT.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, https://arxiv.org/abs/1901.06346v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

/-!
Khanian and Winter, Entanglement-Assisted Quantum Data Compression,
arXiv:1901.06346v1. PDF pages are used throughout.
Only pinned accepted modules are imported. New definitions are paper-local.
Theorem 6 is deferred: its unrestricted half-spaces conflict with the
actual-dimension operational definition in Section II. No source correction
or net-entanglement convention is imposed here. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter
open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Accepted
export QAlgorithms.Papers.Independent.Renew46.P44
  (DiscreteInputLaw discreteStateAverage)
export QAlgorithms.Papers.Independent.Dependency50.P19
  (first associate flip IsIso)
end Accepted

/-- PDF p.1, (1): data for a countably indexed product-pure source.
`Valid` removes null letters and requires normalized vectors. -/
structure ProductPureSource (X A C : Type) where
  law : Accepted.DiscreteInputLaw X
  psi : X → EuclideanSpace ℂ A
  sigma : X → EuclideanSpace ℂ C

variable {X A C : Type} [Fintype A] [Fintype C]

/-- PDF p.1: supported probabilities are strictly positive; no H(X) premise. -/
def ProductPureSource.Valid (s : ProductPureSource X A C) : Prop :=
  (∀ x, 0 < s.law.weight x) ∧
  (∀ x, IsState (s.psi x)) ∧ (∀ x, IsState (s.sigma x))

/-- PDF p.1, (1): the joint pure source vector on A,C. -/
def ProductPureSource.joint (s : ProductPureSource X A C) (x : X) : EuclideanSpace ℂ (A × C) :=
  tensorVec (s.psi x) (s.sigma x)

/-- PDF p.2, Definition 2: nonorthogonality of supported joint vectors. -/
def ProductPureSource.adjacent (s : ProductPureSource X A C) (x z : X) : Prop :=
  inner ℂ (s.joint x) (s.joint z) ≠ 0

/-- PDF p.2: the canonical component label is the equivalence closure of
nonorthogonality, rather than an arbitrary readable function of X. -/
def IrreducibleLabel (s : ProductPureSource X A C) :=
  Quotient (Relation.EqvGen.setoid s.adjacent)

/-- PDF p.2, (3): the canonical label y(x). -/
def ProductPureSource.label (s : ProductPureSource X A C) (x : X) : IrreducibleLabel s :=
  Quotient.mk _ x

/-- PDF p.2: probability of an occupied component. -/
def ProductPureSource.componentProbability (s : ProductPureSource X A C) (y : IrreducibleLabel s) : ℝ :=
  ∑' x, if s.label x = y then s.law.weight x else 0

/-- PDF p.2: conditional component law; division is used only at positive
component mass in the structural theorem. -/
def ProductPureSource.conditionalProbability (s : ProductPureSource X A C) (y : IrreducibleLabel s) (x : X) : ℝ :=
  if s.label x = y then s.law.weight x / s.componentProbability y else 0

/-- PDF p.2: span of a fiber of a labeling h. -/
def ProductPureSource.fiberSpan (s : ProductPureSource X A C) {Y : Type} (h : X → Y) (y : Y) :
    Submodule ℂ (EuclideanSpace ℂ (A × C)) :=
  Submodule.span ℂ {v | ∃ x, h x = y ∧ s.joint x = v}

/-- PDF p.2, Definition 2: every fiber is nonempty and irreducible, and
spans of distinct fibers are orthogonal. Surjectivity excludes empty labels. -/
def ProductPureSource.IsDecomposition (s : ProductPureSource X A C) {Y : Type} (h : X → Y) : Prop :=
  Function.Surjective h ∧
  (∀ y, ∀ u v : {x // h x = y},
    Relation.EqvGen (fun a b : {x // h x = y} => s.adjacent a.val b.val) u v) ∧
  (∀ y z, y ≠ z → ∀ u ∈ s.fiberSpan h y, ∀ v ∈ s.fiberSpan h z,
    inner ℂ u v = 0)

/-- PDF p.2, Definition 2: a nonempty ensemble cannot split orthogonally. -/
def ProductPureSource.Irreducible (s : ProductPureSource X A C) : Prop :=
  ∀ x z, s.label x = s.label z

/-- PDF pp.1,2: actual average density of A. -/
def ProductPureSource.averageA (s : ProductPureSource X A C) : Matrix A A ℂ :=
  Accepted.discreteStateAverage (fun x => pureDensity (s.psi x)) s.law

/-- PDF pp.1,2: actual average density of AC. -/
def ProductPureSource.averageAC (s : ProductPureSource X A C) : Matrix (A × C) (A × C) ℂ :=
  Accepted.discreteStateAverage (fun x => pureDensity (s.joint x)) s.law

/-- PDF p.2: the y diagonal block of the canonical CY marginal.
Blocks are subnormalized; their entropies already include -q(y)log q(y). -/
def ProductPureSource.blockC (s : ProductPureSource X A C) (y : IrreducibleLabel s) : Matrix C C ℂ :=
  Accepted.discreteStateAverage
    (fun x => if s.label x = y then pureDensity (s.sigma x) else 0) s.law

/-- PDF p.2: the y diagonal block of the canonical AY marginal. -/
def ProductPureSource.blockA (s : ProductPureSource X A C) (y : IrreducibleLabel s) : Matrix A A ℂ :=
  Accepted.discreteStateAverage
    (fun x => if s.label x = y then pureDensity (s.psi x) else 0) s.law

/-- PDF p.2: the y diagonal block of the canonical ACY marginal. -/
def ProductPureSource.blockAC (s : ProductPureSource X A C) (y : IrreducibleLabel s) : Matrix (A × C) (A × C) ℂ :=
  Accepted.discreteStateAverage
    (fun x => if s.label x = y then pureDensity (s.joint x) else 0) s.law

/-- PDF p.1: entropy of A in bits. -/
def ProductPureSource.entropyA (s : ProductPureSource X A C) : ℝ := vnEntropy s.averageA

/-- PDF p.2: Shannon entropy of the canonical finite occupied label Y.
For valid sources the orthogonal nonzero component spans imply finite Y,
even when X is infinite. This is not an assumption on H(X). -/
def ProductPureSource.entropyY (s : ProductPureSource X A C) : ℝ :=
  ∑' y : IrreducibleLabel s, -s.componentProbability y * Real.logb 2 (s.componentProbability y)

/-- PDF p.2: entropy of the actual block-diagonal CY marginal, in bits. -/
def ProductPureSource.entropyCY (s : ProductPureSource X A C) : ℝ :=
  ∑' y : IrreducibleLabel s, vnEntropy (s.blockC y)

/-- PDF p.2: entropy of the actual block-diagonal AY marginal, in bits. -/
def ProductPureSource.entropyAY (s : ProductPureSource X A C) : ℝ :=
  ∑' y : IrreducibleLabel s, vnEntropy (s.blockA y)

/-- PDF p.2: entropy of the actual block-diagonal ACY marginal, in bits. -/
def ProductPureSource.entropyACY (s : ProductPureSource X A C) : ℝ :=
  ∑' y : IrreducibleLabel s, vnEntropy (s.blockAC y)

/-- PDF p.2, Theorem 3: communication corner computed from the source. -/
def ProductPureSource.quantumCorner (s : ProductPureSource X A C) : ℝ :=
  (s.entropyA + s.entropyACY - s.entropyCY) / 2

/-- PDF p.2, Theorem 3: simultaneous entanglement-consumption corner. -/
def ProductPureSource.entanglementCorner (s : ProductPureSource X A C) : ℝ :=
  (s.entropyA - s.entropyACY + s.entropyCY) / 2

/-- PDF p.2: blind means identical pure densities, allowing global phases. -/
def ProductPureSource.Blind (s : ProductPureSource X A C) : Prop :=
  ∀ x z, pureDensity (s.sigma x) = pureDensity (s.sigma z)

/-- PDF p.2: visible side information is an orthonormal encoding of X. -/
def ProductPureSource.Visible (s : ProductPureSource X A C) : Prop :=
  ∀ x z, x ≠ z → inner ℂ (s.sigma x) (s.sigma z) = 0

/-- PDF p.1: the actual independent product of two discrete probability laws. -/
def independentDiscreteLaw {X1 X2 : Type} (p : Accepted.DiscreteInputLaw X1)
    (q : Accepted.DiscreteInputLaw X2) : Accepted.DiscreteInputLaw (X1 × X2) where
  weight := fun x => p.weight x.1 * q.weight x.2
  nonnegative := fun x => mul_nonneg (p.nonnegative x.1) (q.nonnegative x.2)
  summable := p.summable.mul_of_nonneg q.summable p.nonnegative q.nonnegative
  total := by
    simpa only [p.total, q.total, one_mul] using
      (p.summable.tsum_mul_tsum q.summable
        (p.summable.mul_of_nonneg q.summable p.nonnegative q.nonnegative)).symm

/-- PDF p.1: product source, with A1,A2 regrouped and C1,C2 regrouped. -/
def productSource {X1 X2 A1 A2 C1 C2 : Type}
    (s : ProductPureSource X1 A1 C1) (t : ProductPureSource X2 A2 C2) :
    ProductPureSource (X1 × X2) (A1 × A2) (C1 × C2) where
  law := independentDiscreteLaw s.law t.law
  psi := fun x => tensorVec (s.psi x.1) (t.psi x.2)
  sigma := fun x => tensorVec (s.sigma x.1) (t.sigma x.2)

/-- PDF p.1: probability of an n-letter memoryless input word. -/
def ProductPureSource.wordProbability (s : ProductPureSource X A C) {n : ℕ} (x : Fin n → X) : ℝ :=
  ∏ i, s.law.weight (x i)

/-- PDF p.1: the complete A^n C^n pure target, registers grouped by party. -/
def ProductPureSource.wordVector (s : ProductPureSource X A C) {n : ℕ} (x : Fin n → X) :
    EuclideanSpace ℂ ((Fin n → A) × (Fin n → C)) :=
  tensorVec (WithLp.toLp 2 fun a => ∏ i, s.psi (x i) (a i))
    (WithLp.toLp 2 fun c => ∏ i, s.sigma (x i) (c i))

/-- PDF pp.1,2, Section II: arbitrary CPTP encoder and decoder, fixed
independently of the inaccessible word; actual positive resource dimensions.
The side register is retained by Alice. n is a positive block in sequences. -/
structure PreservedSideQuantumCode (A C : Type) [Fintype A] [Fintype C] (n : ℕ) where
  K : ℕ
  messageDimension : ℕ
  K_positive : 0 < K
  message_positive : 0 < messageDimension
  message_cap : messageDimension ≤ Fintype.card A ^ n
  encoder : Superop (((Fin n → A) × (Fin n → C)) × Fin K)
    ((Fin n → C) × Fin messageDimension)
  decoder : Superop (Fin messageDimension × Fin K) (Fin n → A)
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder

/-- PDF pp.1,2: quantum cost is the actual log-dimension per source letter. -/
def PreservedSideQuantumCode.quantumRate {n : ℕ} (P : PreservedSideQuantumCode A C n) : ℝ :=
  Real.logb 2 P.messageDimension / (n : ℝ)

/-- PDF p.2: initial consumed entanglement, with no output-ebit subtraction. -/
def PreservedSideQuantumCode.entanglementRate {n : ℕ} (P : PreservedSideQuantumCode A C n) : ℝ :=
  Real.logb 2 P.K / (n : ℝ)

/-- PDF pp.1,2: source together with Alice's and Bob's Bell halves.
The input order is ((A^n,C^n),A0),B0. -/
def PreservedSideQuantumCode.input {n : ℕ} (P : PreservedSideQuantumCode A C n) (s : ProductPureSource X A C)
    (x : Fin n → X) :
    EuclideanSpace ℂ ((((Fin n → A) × (Fin n → C)) × Fin P.K) × Fin P.K) :=
  letI : NeZero P.K := ⟨Nat.ne_of_gt P.K_positive⟩
  WithLp.toLp 2 fun u => s.wordVector x u.1.1 *
    finiteMaxEntangled (Fin P.K) (u.1.2, u.2)

/-- PDF p.2, (2): actual decoded joint Ahat^n Chat^n state. Bob's B0
is untouched during encoding; Chat^n is untouched during decoding. -/
def PreservedSideQuantumCode.output {n : ℕ} (P : PreservedSideQuantumCode A C n) (s : ProductPureSource X A C)
    (x : Fin n → X) :
    Matrix ((Fin n → A) × (Fin n → C)) ((Fin n → A) × (Fin n → C)) ℂ :=
  Accepted.flip (idTensorSuperop P.decoder
    (Accepted.associate (Accepted.first P.encoder (pureDensity (P.input s x)))))

/-- PDF p.2, (2): average ROOT fidelity of the complete X,A,C output. -/
def PreservedSideQuantumCode.fidelity {n : ℕ} (P : PreservedSideQuantumCode A C n) (s : ProductPureSource X A C) : ℝ :=
  ∑' x : Fin n → X, s.wordProbability x *
    rootFidelity (pureDensity (s.wordVector x)) (P.output s x)

/-- PDF p.2: one code for every positive block length; n indexes length n+1. -/
abbrev QuantumCodeSequence (A C : Type) [Fintype A] [Fintype C] :=
  (n : ℕ) → PreservedSideQuantumCode A C (n + 1)

/-- PDF p.2: minimum quantum rate with unlimited initial entanglement and
simultaneous attainment of the stated consumption rate. The converse imposes
no convergence or bound on the entanglement rate. -/
def ProductPureSource.OptimalQuantumCorner (s : ProductPureSource X A C) (q e : ℝ) : Prop :=
  (∀ P : QuantumCodeSequence A C, ∀ r : ℝ,
    Tendsto (fun n => (P n).fidelity s) atTop (nhds 1) →
    Tendsto (fun n => (P n).quantumRate) atTop (nhds r) → q ≤ r) ∧
  (∃ P : QuantumCodeSequence A C,
    Tendsto (fun n => (P n).fidelity s) atTop (nhds 1) ∧
    Tendsto (fun n => (P n).quantumRate) atTop (nhds q) ∧
    Tendsto (fun n => (P n).entanglementRate) atTop (nhds e))

/-- PDF pp.4,5: sum-rate weak converse for any successful finite-rate sequence. -/
def ProductPureSource.SumRateConverse (s : ProductPureSource X A C) : Prop :=
  ∀ P : QuantumCodeSequence A C, ∀ q e : ℝ,
    Tendsto (fun n => (P n).fidelity s) atTop (nhds 1) →
    Tendsto (fun n => (P n).quantumRate) atTop (nhds q) →
    Tendsto (fun n => (P n).entanglementRate) atTop (nhds e) →
    s.entropyA ≤ q + e

/-- PDF p.3, Definition 4: finite Stinespring isometries, with the input
and reconstructed output dimensions A,C fixed. -/
structure Extraction (A C : Type) [Fintype A] [Fintype C] where
  environmentDimension : ℕ
  environment_positive : 0 < environmentDimension
  isometry : Matrix (A × (C × Fin environmentDimension)) (A × C) ℂ
  isometry_columns : Accepted.IsIso isometry

/-- PDF p.3: the output state on Ahat,Chat,W for a source letter. -/
def Extraction.letter (V : Extraction A C) (s : ProductPureSource X A C) (x : X) :
    Matrix (A × (C × Fin V.environmentDimension)) (A × (C × Fin V.environmentDimension)) ℂ :=
  conjSuperop V.isometry (pureDensity (s.joint x))

/-- PDF p.3: discard W, retaining the full reconstructed A,C pair. -/
def Extraction.retained (V : Extraction A C) (s : ProductPureSource X A C) (x : X) :
    Matrix (A × C) (A × C) ℂ :=
  fun a b => ∑ w, V.letter s x (a.1, (a.2, w)) (b.1, (b.2, w))

/-- PDF p.3: fidelity constraint in Definition 4, including epsilon>=1. -/
def Extraction.fidelity (V : Extraction A C) (s : ProductPureSource X A C) : ℝ :=
  ∑' x, s.law.weight x * rootFidelity (pureDensity (s.joint x)) (V.retained s x)

/-- PDF p.3: I(X:Chat W) as a finite-output Holevo entropy difference.
This avoids forming H(X)-H(X|Chat W) on countable alphabets. -/
def Extraction.objective (V : Extraction A C) (s : ProductPureSource X A C) : ℝ :=
  let rho := fun x => traceLeft (V.letter s x)
  vnEntropy (Accepted.discreteStateAverage rho s.law) -
    ∑' x, s.law.weight x * vnEntropy (rho x)

/-- PDF p.3: the bounded-environment optimization-value set. Its nonemptiness,
boundedness, exact maximum and equivalence to arbitrary finite environments
are conclusions of `definition4_attainment`, not assumed source fields. -/
def extractionValues (s : ProductPureSource X A C) (eps : ℝ) : Set ℝ :=
  {v | ∃ V : Extraction A C,
    V.environmentDimension ≤ Fintype.card A ^ 2 * Fintype.card C ^ 2 ∧
    1 - eps ≤ V.fidelity s ∧ v = V.objective s}

/-- PDF p.3, Definition 4: real supremum on the compact bounded-environment
model. Under Valid and eps>=0 the value set is nonempty and bounded above;
this guard is established in the accompanying attainment theorem. -/
def extractionInformation (s : ProductPureSource X A C) (eps : ℝ) : ℝ :=
  sSup (extractionValues s eps)

/-- PDF p.5, modified model: a finite CP instrument. Joint Kraus normalization
makes each branch trace-nonincreasing and the sum trace-preserving. -/
def IsFiniteRectangularInstrument {I O M : Type} [Fintype I] [Fintype O] [Fintype M]
    (T : M → Superop I O) : Prop :=
  ∃ r : M → ℕ, ∃ B : (m : M) → Fin (r m) → Matrix O I ℂ,
    (∑ m, ∑ j, (B m j)ᴴ * B m j = 1) ∧
    ∀ m rho, T m rho = krausApply (B m) rho

/-- PDF p.5, Theorem 8 model: Alice receives a blind A-source, extracts its
canonical Y locally, and retains Y^n. The instrument acts on A^n A0;
its classical outcome alone is sent. Bob decodes his Bell half conditionally.
There is no quantum message and no classical-alphabet dimension cap. -/
structure BlindClassicalCode (s : ProductPureSource X A Unit) (n : ℕ) where
  K : ℕ
  messageDimension : ℕ
  K_positive : 0 < K
  message_positive : 0 < messageDimension
  labelSize : ℕ
  labelEquivalence : IrreducibleLabel s ≃ Fin (labelSize + 1)
  instrument : Fin messageDimension →
    Superop ((Fin n → A) × Fin K) (Fin n → Fin (labelSize + 1))
  instrument_valid : IsFiniteRectangularInstrument instrument
  decoder : Fin messageDimension → Superop (Fin K) (Fin n → A)
  decoder_channel : ∀ m, IsChannel (decoder m)

/-- PDF p.5: actual classical bits per source letter. -/
def BlindClassicalCode.classicalRate {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n) : ℝ :=
  Real.logb 2 P.messageDimension / (n : ℝ)

/-- PDF p.5: actual initial entanglement consumed per source letter. -/
def BlindClassicalCode.entanglementRate {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n) : ℝ :=
  Real.logb 2 P.K / (n : ℝ)

/-- PDF p.5: blind input A^n,A0,B0; only preshared entanglement at Bob. -/
def BlindClassicalCode.input {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n)
    (x : Fin n → X) : EuclideanSpace ℂ (((Fin n → A) × Fin P.K) × Fin P.K) :=
  letI : NeZero P.K := ⟨Nat.ne_of_gt P.K_positive⟩
  WithLp.toLp 2 fun u => (∏ i, s.psi (x i) (u.1.1 i)) *
    finiteMaxEntangled (Fin P.K) (u.1.2, u.2)

/-- PDF p.5: sum of genuine quantum-instrument branches, decoded using
Bob's entangled half; output order Ahat^n,Yhat^n. -/
def BlindClassicalCode.output {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n)
    (x : Fin n → X) :
    Matrix ((Fin n → A) × (Fin n → Fin (P.labelSize + 1)))
      ((Fin n → A) × (Fin n → Fin (P.labelSize + 1))) ℂ :=
  ∑ m, Accepted.flip (idTensorSuperop (P.decoder m)
    (Accepted.first (P.instrument m) (pureDensity (P.input x))))

/-- PDF p.5: complete AY target, with the canonical component word retained. -/
def BlindClassicalCode.target {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n)
    (x : Fin n → X) :
    EuclideanSpace ℂ ((Fin n → A) × (Fin n → Fin (P.labelSize + 1))) :=
  tensorVec (WithLp.toLp 2 fun a => ∏ i, s.psi (x i) (a i))
    (ket (fun i => P.labelEquivalence (s.label (x i))))

/-- PDF p.5: same average joint root-fidelity criterion as Section II. -/
def BlindClassicalCode.fidelity {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n) : ℝ :=
  ∑' x : Fin n → X, s.wordProbability x *
    rootFidelity (pureDensity (P.target x)) (P.output x)

/-- PDF p.5: actual classical/entanglement rates converge along all positive
block lengths; no budget interpretation is substituted. -/
def BlindClassicalAchievable (s : ProductPureSource X A Unit) (c e : ℝ) : Prop :=
  ∃ P : (n : ℕ) → BlindClassicalCode s (n + 1),
    Tendsto (fun n => (P n).fidelity) atTop (nhds 1) ∧
    Tendsto (fun n => (P n).classicalRate) atTop (nhds c) ∧
    Tendsto (fun n => (P n).entanglementRate) atTop (nhds e)

/-- PDF p.5: |+> in the separation example. Reindex the accepted Fin-2
plus state on the Bool computational basis, false=0 and true=1. -/
def separationPlus : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun b =>
    QAlgorithms.Papers.Independent.Frontier30.P01.plusVector (if b then 1 else 0)

/-- PDF p.5: source-letter A vectors 0,1,+. -/
def examplePsi : Fin 3 → EuclideanSpace ℂ Bool :=
  ![ket false, ket true, separationPlus]

/-- PDF p.5: original side vectors 0,0,+. -/
def separationSideVectors : Fin 3 → EuclideanSpace ℂ Bool :=
  ![ket false, ket false, separationPlus]

/-- PDF p.5: transformed side vectors 0,1,+. -/
def exampleModifiedSigma : Fin 3 → EuclideanSpace ℂ Bool := examplePsi

/-- PDF p.5: probabilities 1/2-t,1/2-t,2t. -/
def exampleWeights (t : ℝ) : Fin 3 → ℝ := ![1 / 2 - t, 1 / 2 - t, 2 * t]

/-- PDF p.5: the normalized law on the source's open parameter interval. -/
def separationLaw (t : Set.Ioo (0 : ℝ) (1 / 2)) : Accepted.DiscreteInputLaw (Fin 3) where
  weight := exampleWeights t.val
  nonnegative := by
    intro i
    have h0 := t.property.1
    have h1 := t.property.2
    fin_cases i <;> simp [exampleWeights] <;> linarith
  summable := (hasSum_fintype _).summable
  total := by
    rw [tsum_fintype]
    simp [exampleWeights, Fin.sum_univ_three] <;> ring

/-- PDF p.5: the original three-letter source. -/
def exampleOriginal (t : Set.Ioo (0 : ℝ) (1 / 2)) : ProductPureSource (Fin 3) Bool Bool :=
  ⟨separationLaw t, examplePsi, separationSideVectors⟩

/-- PDF p.5: the three-letter source after the local controlled-NOT. -/
def exampleModified (t : Set.Ioo (0 : ℝ) (1 / 2)) : ProductPureSource (Fin 3) Bool Bool :=
  ⟨separationLaw t, examplePsi, exampleModifiedSigma⟩

/-- PDF p.5: a finite coefficient average for the explicit parameter family,
including t=0 for computing the one-sided entropy limit. -/
def exampleDensity (t : ℝ) (v : Fin 3 → EuclideanSpace ℂ (Bool × Bool)) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ∑ x, (exampleWeights t x : ℂ) • pureDensity (v x)

/-- PDF p.5: (S(A)+S(AC)-S(C))/2 for the original ensemble. -/
def exampleOriginalRate (t : ℝ) : ℝ :=
  let rho := exampleDensity t (fun x => tensorVec (examplePsi x) (separationSideVectors x))
  (vnEntropy (traceRight rho) + vnEntropy rho - vnEntropy (traceLeft rho)) / 2

/-- PDF p.5: (S(A)+S(ACprime)-S(Cprime))/2 after controlled-NOT. -/
def exampleModifiedRate (t : ℝ) : ℝ :=
  let rho := exampleDensity t (fun x => tensorVec (examplePsi x) (exampleModifiedSigma x))
  (vnEntropy (traceRight rho) + vnEntropy rho - vnEntropy (traceLeft rho)) / 2

/-! Definition sanity checks. These do not prove any of the paper's results. -/

example (s : ProductPureSource X A C) (x : X) : s.label x = s.label x := rfl

example (s : ProductPureSource X A C) {y : IrreducibleLabel s} {x : X} (h : s.label x ≠ y) :
    s.conditionalProbability y x = 0 := by
  simp [ProductPureSource.conditionalProbability, h]

example (s : ProductPureSource X A C) (x : Fin 0 → X) : s.wordProbability x = 1 := by
  simp [ProductPureSource.wordProbability]

example {n : ℕ} (P : PreservedSideQuantumCode A C n) (h : P.messageDimension = 1) :
    P.quantumRate = 0 := by
  simp [PreservedSideQuantumCode.quantumRate, h]

example {n : ℕ} (P : PreservedSideQuantumCode A C n) (h : P.K = 1) :
    P.entanglementRate = 0 := by
  simp [PreservedSideQuantumCode.entanglementRate, h]

example {s : ProductPureSource X A Unit} {n : ℕ} (P : BlindClassicalCode s n)
    (h : P.messageDimension = 1) : P.classicalRate = 0 := by
  simp [BlindClassicalCode.classicalRate, h]

example (s : ProductPureSource X A C) :
    s.quantumCorner + s.entanglementCorner = s.entropyA := by
  unfold ProductPureSource.quantumCorner ProductPureSource.entanglementCorner
  ring

example : separationPlus false = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := rfl

example (t : ℝ) : exampleWeights t 2 = 2 * t := rfl

example {X1 X2 : Type} (p : Accepted.DiscreteInputLaw X1)
    (q : Accepted.DiscreteInputLaw X2) (x : X1 × X2) :
    (independentDiscreteLaw p q).weight x = p.weight x.1 * q.weight x.2 := rfl

example (t : Set.Ioo (0 : ℝ) (1 / 2)) :
    (exampleOriginal t).psi = (exampleModified t).psi := rfl

/-! Headline results: one theorem per stated plan node. -/

end QAlgorithms.Papers.Independent.Advance50.P41


