-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36
-- name    : QAlgorithms_Papers_Independent_Renew46_P36
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T22:02:11.346177+00:00
-- url     : https://prove2.me/theorems/f8ac6340-5e66-4443-97db-f7b963607cbd
-- title:
--   Definitions for The capacity of a quantum channel for simultaneous transmission of classical and quantum information
-- statement:
--   The objects the formalized statements of *The capacity of a quantum channel for simultaneous transmission of classical and quantum information* (arXiv:quant-ph/0311131) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Scenario`: PDF pp.1--3: the three unassisted operational scenarios.
--   - `Decoder`: PDF p.2: a rectangular CP instrument; the sum, rather than each branch, is trace preserving. No side channel or preshared resource is a field.
--   - `Decoder.branch`: PDF p.2: subnormalized output for one classical outcome.
--   - `Decoder.total`: PDF p.2: unconditional quantum output of the decoding instrument.
--   - `SimultaneousTransmissionCode`: PDF p.2: one encoder per message, with an arbitrary positive logical dimension.
--   - `SimultaneousTransmissionCode.classicalSuccess`: PDF p.2: probability of correctly decoding j on the specified logical input.
--   - `SimultaneousTransmissionCode.effective`: PDF p.2: the effective logical quantum channel when the outcome is forgotten.
--   - `SimultaneousTransmissionCode.GoodIa`: PDF p.2, scenario Ia: BOTH conditions for every message and every pure input.
--   - `SimultaneousTransmissionCode.GoodIb`: PDF p.2, scenario Ib: every message, with an untouched logical reference. Classical success uses the maximally mixed marginal of Phi.
--   - `SimultaneousGenerationCode`: PDF p.3, scenario II: message-dependent pure preparation in Alice's lab. The reference has exactly the target dimension; no initial shared entanglement.
--   - `SimultaneousGenerationCode.Good`: PDF p.3, (3): every-message classical correctness and squared generation fidelity.
--   - `HasCode`: PDF pp.2--3: existence of a code with the specified integer sizes and error.
--   - `simultaneousOperationalRegion`: PDF pp.2--4: all sufficiently large positive block lengths, for every error and rate tolerance. Integer sizes give rate lower bounds, with both axes included.
--   - `operationalClassicalAxisCapacity`: PDF p.4: the classical capacity defined independently of entropy formulas, as the operational classical axis. Positive finite registers make this supremum nonempty (zero rate) and bounded (by log2(dim A)).
--   - `ensembleInput`: PDF p.3: the transmitted input density constructed from the purification.
--   - `classicalInformation`: PDF pp.3--4: I(X;B) in bits, using the accepted entropy formula and the outputs of this same ensemble. The reference is left untouched by pureOutputs.
--   - `conditionalCoherentInformation`: PDF pp.3--4: I(A>B X)=sum p_x[H(B)_x-H(AB)_x]. The accepted formula uses the conditional-entropy sign fixed by pp.6--7 and 13--14, correcting p.3.
--   - `cqOneLetterRegion`: PDF p.4, (6): downward rectangles from a single common ensemble.
--   - `boundedAlphabetRegion`: PDF pp.4,15: the same region with an explicit alphabet bound.
--   - `cqClosedRegularization`: PDF pp.2,4,7: closed regularization. The printed (5) omits closure; limiting achievability and the arbitrary-delta converse require it.
--   - `sharingTriangle`: PDF p.4: downward time-sharing triangle, without division by either capacity. This includes zero quantum capacity and a one-dimensional input.
--   - `flaggedErasure`: PDF p.5: an orthogonal erasure flag, distinct from every input basis vector.
--   - `wordDensity`: PDF p.8: the ordered product density rho_{x^n}; no permutation is hidden.
--   - `inputCoherentInformation`: PDF pp.3,8: input coherent information, independent of the chosen purification.
--   - `RandomQuantumCode`: PDF pp.7--8: a finite random quantum code with common positive logical size. Every realization is a CPTP encoder/decoder pair; its error is tested below. Randomness is internal to Proposition 5, not an extra capacity resource.
--   - `RandomQuantumCode.average`: PDF p.8, (12)--(14): average code density, with maximally mixed logical input.
--   - `RandomQuantumCode.GoodType`: PDF pp.8--10: the per-realization entanglement-fidelity guarantee explicitly used on p.10 for all m,alpha, plus the ensemble-type trace norm bound.
--   - `dephasingFunctional`: PDF p.14: f_lambda for a dephasing channel. All input ensembles are allowed; in particular a product-register ensemble need not have product density operators. For unit environment vectors and nonempty finite registers, the set is nonempty, bounded, and its supremum is attained by compactness and finite alphabet reduction.
--   - `productEnvironment`: PDF p.14: environmental vectors of the tensor-product dephasing channel.
--   - `qubitCorner`: PDF p.15, corrected to the p.14 channel: binary-ensemble achievable corner. Printed: 16*p*(1-p); changed: 4*p*(2-p), because phase-flip probability is p/2. At complete dephasing p=1 this gives zero quantum rate, whereas the printed expression gives h2(mu). Independent moderation of this correction is required.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, https://arxiv.org/abs/quant-ph/0311131v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

/-!
Devetak--Shor, arXiv:quant-ph/0311131v3. Finite nonzero registers only.
The accepted paper imports supply audited definitions, as permitted by the
independent-paper override. No result from them is assumed as a hypothesis.
Compilation is pending the requested batch handoff.

Repair provenance: use accepted DynamicPureEnsemble, Ensemble, maximallyEntangled,
piSuperop and inclusive Dependency50.P07.Typical directly. The qubit channel is
Information100.P27.qubitDephasing (1-p), since its parameter attenuates coherences.
SimultaneousTransmissionCode and SimultaneousGenerationCode include a classical
message and a common CP decoding instrument; accepted P80 codes have no classical
message or instrument (and P80 generation allows mixed preparations). The local
simultaneousOperationalRegion is a nonnegative two-rate region, unlike the accepted
multiway classical capacityRegion. Its operationalClassicalAxisCapacity is an
asymptotic vanishing-error axis, unlike P62's zero-error graph classicalCapacity.
cqOneLetterRegion and cqClosedRegularization have two coordinates and bounds (6),
unlike the accepted scalar simulation region and signed three-resource region.
These distinct objects retain complete local bodies rather than substituting a
namesake with different mathematical content. No frozen declaration is changed.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)
open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)
open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)
open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)
open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)
open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)
open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)
open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}
variable [Fintype A] [Fintype B] [Fintype E]
variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- PDF pp.1--3: the three unassisted operational scenarios. -/
inductive Scenario where
  | Ia
  | Ib
  | II
  deriving DecidableEq

/-- PDF p.2: a rectangular CP instrument; the sum, rather than each branch,
is trace preserving. No side channel or preshared resource is a field. -/
structure Decoder (I O : Type) [Fintype I] [Fintype O] (m : ℕ) where
  count : Fin m → ℕ
  kraus : (j : Fin m) → Fin (count j) → Matrix O I ℂ
  complete : ∑ j, ∑ t, (kraus j t)ᴴ * kraus j t = 1

/-- PDF p.2: subnormalized output for one classical outcome. -/
def Decoder.branch {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (D : Decoder I O m) (j : Fin m) : Superop I O :=
  krausApply (D.kraus j)

/-- PDF p.2: unconditional quantum output of the decoding instrument. -/
def Decoder.total {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (D : Decoder I O m) : Superop I O := fun X => ∑ j, D.branch j X

/-- PDF p.2: one encoder per message, with an arbitrary positive logical dimension. -/
structure SimultaneousTransmissionCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  messages : ℕ
  logical : ℕ
  messagesPositive : 0 < messages
  logicalPositive : 0 < logical
  encoder : Fin messages → Superop (Fin logical) (Fin n → A)
  encoderChannel : ∀ j, IsChannel (encoder j)
  decoder : Decoder (Fin n → B) (Fin logical) messages

/-- PDF p.2: probability of correctly decoding j on the specified logical input. -/
def SimultaneousTransmissionCode.classicalSuccess {n : ℕ} (C : SimultaneousTransmissionCode A B n)
    (N : Superop A B) (j : Fin C.messages)
    (rho : Matrix (Fin C.logical) (Fin C.logical) ℂ) : ℝ :=
  (C.decoder.branch j ((piSuperop (fun _ : Fin n => N)) (C.encoder j rho))).trace.re

/-- PDF p.2: the effective logical quantum channel when the outcome is forgotten. -/
def SimultaneousTransmissionCode.effective {n : ℕ} (C : SimultaneousTransmissionCode A B n)
    (N : Superop A B) (j : Fin C.messages) : Superop (Fin C.logical) (Fin C.logical) :=
  C.decoder.total ∘ (piSuperop (fun _ : Fin n => N)) ∘ C.encoder j

/-- PDF p.2, scenario Ia: BOTH conditions for every message and every pure input. -/
def SimultaneousTransmissionCode.GoodIa {n : ℕ} (C : SimultaneousTransmissionCode A B n)
    (N : Superop A B) (epsilon : ℝ) : Prop :=
  ∀ j, ∀ v : EuclideanSpace ℂ (Fin C.logical), ‖v‖ = 1 →
    1 - epsilon ≤ C.classicalSuccess N j (pureDensity v) ∧
    1 - epsilon ≤ squaredFidelity (pureDensity v) (C.effective N j (pureDensity v))

/-- PDF p.2, scenario Ib: every message, with an untouched logical reference.
Classical success uses the maximally mixed marginal of Phi. -/
def SimultaneousTransmissionCode.GoodIb {n : ℕ} (C : SimultaneousTransmissionCode A B n)
    (N : Superop A B) (epsilon : ℝ) : Prop :=
  ∀ j, 1 - epsilon ≤ C.classicalSuccess N j (maximallyMixed C.logical) ∧
    1 - epsilon ≤ squaredFidelity (maximallyEntangled C.logical)
      (idTensorSuperop (C.effective N j) (maximallyEntangled C.logical))

/-- PDF p.3, scenario II: message-dependent pure preparation in Alice's lab.
The reference has exactly the target dimension; no initial shared entanglement. -/
structure SimultaneousGenerationCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  messages : ℕ
  logical : ℕ
  messagesPositive : 0 < messages
  logicalPositive : 0 < logical
  preparation : Fin messages → EuclideanSpace ℂ (Fin logical × (Fin n → A))
  normalized : ∀ j, ‖preparation j‖ = 1
  decoder : Decoder (Fin n → B) (Fin logical) messages

/-- PDF p.3, (3): every-message classical correctness and squared generation fidelity. -/
def SimultaneousGenerationCode.Good {n : ℕ} (C : SimultaneousGenerationCode A B n)
    (N : Superop A B) (epsilon : ℝ) : Prop :=
  ∀ j,
    1 - epsilon ≤
      (C.decoder.branch j ((piSuperop (fun _ : Fin n => N)) (traceLeft (pureDensity (C.preparation j))))).trace.re ∧
    1 - epsilon ≤ squaredFidelity (maximallyEntangled C.logical)
      (idTensorSuperop (C.decoder.total ∘ (piSuperop (fun _ : Fin n => N))) (pureDensity (C.preparation j)))

/-- PDF pp.2--3: existence of a code with the specified integer sizes and error. -/
def HasCode (s : Scenario) (N : Superop A B) (n : ℕ) (epsilon : ℝ) (m k : ℕ) : Prop :=
  match s with
  | .Ia => ∃ C : SimultaneousTransmissionCode A B n,
      C.messages = m ∧ C.logical = k ∧ C.GoodIa N epsilon
  | .Ib => ∃ C : SimultaneousTransmissionCode A B n,
      C.messages = m ∧ C.logical = k ∧ C.GoodIb N epsilon
  | .II => ∃ C : SimultaneousGenerationCode A B n,
      C.messages = m ∧ C.logical = k ∧ C.Good N epsilon

/-- PDF pp.2--4: all sufficiently large positive block lengths, for every error
and rate tolerance. Integer sizes give rate lower bounds, with both axes included. -/
def simultaneousOperationalRegion (s : Scenario) (N : Superop A B) : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧
    ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ m k : ℕ,
        HasCode s N n epsilon m k ∧
        v.1 - delta ≤ Real.logb 2 (m : ℝ) / (n : ℝ) ∧
        v.2 - delta ≤ Real.logb 2 (k : ℝ) / (n : ℝ)}

/-- PDF p.4: the classical capacity defined independently of entropy formulas,
as the operational classical axis. Positive finite registers make this supremum
nonempty (zero rate) and bounded (by log2(dim A)). -/
def operationalClassicalAxisCapacity (N : Superop A B) : ℝ :=
  sSup {r : ℝ | (r, 0) ∈ simultaneousOperationalRegion .Ia N}

/-- PDF p.3: the transmitted input density constructed from the purification. -/
def ensembleInput (P : DynamicPureEnsemble A) (x : Fin P.ensemble.size) : Matrix A A ℂ :=
  traceLeft (pureDensity (P.ensemble.vector x))

/-- PDF pp.3--4: I(X;B) in bits, using the accepted entropy formula and the
outputs of this same ensemble. The reference is left untouched by pureOutputs. -/
def classicalInformation (N : Superop A B) (P : DynamicPureEnsemble A) : ℝ :=
  cqHolevoBits P.ensemble.prob (pureOutputs N P)

/-- PDF pp.3--4: I(A>B X)=sum p_x[H(B)_x-H(AB)_x]. The accepted formula
uses the conditional-entropy sign fixed by pp.6--7 and 13--14, correcting p.3. -/
def conditionalCoherentInformation (N : Superop A B) (P : DynamicPureEnsemble A) : ℝ :=
  conditionalCoherent P.ensemble.prob (pureOutputs N P)

/-- PDF p.4, (6): downward rectangles from a single common ensemble. -/
def cqOneLetterRegion (N : Superop A B) : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ ∃ P : DynamicPureEnsemble A,
    v.1 ≤ classicalInformation N P ∧ v.2 ≤ conditionalCoherentInformation N P}

/-- PDF pp.4,15: the same region with an explicit alphabet bound. -/
def boundedAlphabetRegion (N : Superop A B) (bound : ℕ) : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ ∃ P : DynamicPureEnsemble A, P.ensemble.size ≤ bound ∧
    v.1 ≤ classicalInformation N P ∧ v.2 ≤ conditionalCoherentInformation N P}

/-- PDF pp.2,4,7: closed regularization. The printed (5) omits closure;
limiting achievability and the arbitrary-delta converse require it. -/
def cqClosedRegularization (N : Superop A B) : Set (ℝ × ℝ) :=
  closure {v | ∃ l : ℕ, 0 < l ∧ (l : ℝ) • v ∈ cqOneLetterRegion ((piSuperop (fun _ : Fin l => N)))}

/-- PDF p.4: downward time-sharing triangle, without division by either capacity.
This includes zero quantum capacity and a one-dimensional input. -/
def sharingTriangle (C Q : ℝ) : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    v.1 ≤ t * C ∧ v.2 ≤ (1 - t) * Q}

/-- PDF p.5: an orthogonal erasure flag, distinct from every input basis vector. -/
def flaggedErasure (p : ℝ) : Superop A (Option A) :=
  fun X i j => match i, j with
    | some a, some b => (1 - (p : ℂ)) * X a b
    | none, none => (p : ℂ) * X.trace
    | _, _ => 0

/-- PDF p.8: the ordered product density rho_{x^n}; no permutation is hidden. -/
def wordDensity {n : ℕ} (P : Ensemble A) (word : Fin n → Fin P.size) :
    Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun a b => ∏ i, P.state (word i) (a i) (b i)

/-- PDF pp.3,8: input coherent information, independent of the chosen purification. -/
def inputCoherentInformation (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  let out := idTensorSuperop N (pureDensity (canonicalPurification rho))
  vnEntropy (traceLeft out) - vnEntropy out

/-- PDF pp.7--8: a finite random quantum code with common positive logical size.
Every realization is a CPTP encoder/decoder pair; its error is tested below.
Randomness is internal to Proposition 5, not an extra capacity resource. -/
structure RandomQuantumCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  logical : ℕ
  logicalPositive : 0 < logical
  seeds : ℕ
  seedsPositive : 0 < seeds
  weight : Fin seeds → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  totalWeight : ∑ a, weight a = 1
  encoder : Fin seeds → Superop (Fin logical) (Fin n → A)
  decoder : Fin seeds → Superop (Fin n → B) (Fin logical)
  encoderChannel : ∀ a, IsChannel (encoder a)
  decoderChannel : ∀ a, IsChannel (decoder a)

/-- PDF p.8, (12)--(14): average code density, with maximally mixed logical input. -/
def RandomQuantumCode.average {n : ℕ} (C : RandomQuantumCode A B n) :
    Matrix (Fin n → A) (Fin n → A) ℂ :=
  ∑ a, (C.weight a : ℂ) • C.encoder a (maximallyMixed C.logical)

/-- PDF pp.8--10: the per-realization entanglement-fidelity guarantee explicitly
used on p.10 for all m,alpha, plus the ensemble-type trace norm bound. -/
def RandomQuantumCode.GoodType {n : ℕ} (C : RandomQuantumCode A B n)
    (N : Superop A B) (P : Ensemble A) (word : Fin n → Fin P.size)
    (epsilon : ℝ) : Prop :=
  (∀ a, 1 - epsilon ≤ squaredFidelity (maximallyEntangled C.logical)
    (idTensorSuperop (C.decoder a ∘ (piSuperop (fun _ : Fin n => N)) ∘ C.encoder a)
      (maximallyEntangled C.logical))) ∧
  traceNorm (C.average - wordDensity P word) ≤ epsilon

/-- PDF p.14: f_lambda for a dephasing channel. All input ensembles are allowed;
in particular a product-register ensemble need not have product density operators.
For unit environment vectors and nonempty finite registers, the set is nonempty,
bounded, and its supremum is attained by compactness and finite alphabet reduction. -/
def dephasingFunctional (env : A → EuclideanSpace ℂ E) (lambda : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ P : Ensemble A,
    z = vnEntropy (∑ x, (P.prob x : ℂ) • diagonalPart (P.state x)) +
      (lambda - 1) * (∑ x, P.prob x * vnEntropy (diagonalPart (P.state x))) -
      lambda * (∑ x, P.prob x *
        vnEntropy (complementaryChannel (dephasingIsometry env) (P.state x)))}

/-- PDF p.14: environmental vectors of the tensor-product dephasing channel. -/
def productEnvironment (env1 : A1 → EuclideanSpace ℂ E1)
    (env2 : A2 → EuclideanSpace ℂ E2) : (A1 × A2) → EuclideanSpace ℂ (E1 × E2) :=
  fun a => WithLp.toLp 2 fun e => env1 a.1 e.1 * env2 a.2 e.2

/-- PDF p.15, corrected to the p.14 channel: binary-ensemble achievable corner.
Printed: 16*p*(1-p); changed: 4*p*(2-p), because phase-flip probability is p/2.
At complete dephasing p=1 this gives zero quantum rate, whereas the printed
expression gives h2(mu). Independent moderation of this correction is required. -/
def qubitCorner (p mu : ℝ) : ℝ × ℝ :=
  (1 - binEntropy2 mu,
    binEntropy2 mu - binEntropy2 ((1 + Real.sqrt (1 - 4 * p * (2 - p) * mu * (1 - mu))) / 2))

/-- PDF p.2: squaring the root fidelity fixes the normalization convention. -/
example : squaredFidelity (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 1 := by
  simp [squaredFidelity, rootFidelity, cfc_one]

/-- PDF p.2: a CP branch takes the zero operator to zero. -/
example {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (D : Decoder I O m) (j : Fin m) : D.branch j 0 = 0 := by
  simp [Decoder.branch, krausApply]

/-- PDF p.2: a dimension-one mixed logical input is the identity state. -/
example : maximallyMixed 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [maximallyMixed]

/-- PDF p.2, (2): dimension-one entanglement is a product state. -/
example : maximallyEntangled 1 (0, 0) (0, 0) = 1 := by
  simp [maximallyEntangled, finiteMaxEntangled, pureDensity]

/-- PDF p.8: the empty tensor product is the scalar identity, not a zero state. -/
example (P : Ensemble A) (w : Fin 0 → Fin P.size) (a b : Fin 0 → A) :
    wordDensity P w a b = 1 := by
  simp [wordDensity]

/-- PDF p.8: inclusive typicality includes the length-zero word. Codes themselves
are required at positive lengths by the proposition and capacity definitions. -/
example (P : Ensemble A) (delta : ℝ) (w : Fin 0 → Fin P.size) : Typical P.prob 0 delta w := by
  intro x
  simp [Typical]

/-- PDF p.5: the erasure flag has no coherent off-diagonal entry with a signal. -/
example (p : ℝ) (X : Matrix A A ℂ) (a : A) : flaggedErasure p X none (some a) = 0 := rfl

/-- PDF p.5: at zero erasure, the signal block is exactly the input. -/
example (X : Matrix A A ℂ) (a b : A) : flaggedErasure 0 X (some a) (some b) = X a b := by
  simp [flaggedErasure]

/-- PDF p.14: the product dilation preserves the order of environmental factors. -/
example (env1 : A1 → EuclideanSpace ℂ E1) (env2 : A2 → EuclideanSpace ℂ E2)
    (a : A1) (b : A2) (e : E1) (f : E2) :
    productEnvironment env1 env2 (a, b) (e, f) = env1 a e * env2 b f := rfl

/-- PDF pp.14--15: the parameter endpoints are identity and complete dephasing. -/
example (X : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitDephasing 1 X = X ∧
    qubitDephasing 0 X = diagonalPart X := by
  constructor <;> ext i j <;> by_cases h : i = j <;>
    simp [qubitDephasing, diagonalPart, h]

/-- PDF p.2: forgetting the classical output sums the actual CP branches. -/
example {I O : Type} [Fintype I] [Fintype O] {m : ℕ}
    (D : Decoder I O m) (X : Matrix I I ℂ) : D.total X = ∑ j, D.branch j X := rfl

/-- PDF pp.2--4: negative rate coordinates are excluded operationally. -/
example (s : Scenario) (N : Superop A B) (v : ℝ × ℝ)
    (h : v ∈ simultaneousOperationalRegion s N) : 0 ≤ v.1 ∧ 0 ≤ v.2 := ⟨h.1, h.2.1⟩

/-- PDF pp.2,4,7: limiting rates are retained by the closed regularization. -/
example (N : Superop A B) : IsClosed (cqClosedRegularization N) := isClosed_closure

/-- PDF p.4: a vanishing quantum capacity leaves only the classical axis. -/
example (C : ℝ) (v : ℝ × ℝ) (h : v ∈ sharingTriangle C 0) : v.2 = 0 := by
  rcases h with ⟨_, hq, t, _, _, _, ht⟩
  simp only [mul_zero] at ht
  exact le_antisymm ht hq

/-- PDF p.3: the reference trace is taken from the normalized input ensemble. -/
example (P : DynamicPureEnsemble A) (x : Fin P.ensemble.size) :
    ensembleInput P x = traceLeft (pureDensity (P.ensemble.vector x)) := rfl

/-- PDF pp.3,8: the coherent-information sign is output entropy minus joint entropy. -/
example (N : Superop A B) (rho : Matrix A A ℂ) :
    inputCoherentInformation N rho =
      vnEntropy (traceLeft (idTensorSuperop N (pureDensity (canonicalPurification rho)))) -
        vnEntropy (idTensorSuperop N (pureDensity (canonicalPurification rho))) := rfl

/-- PDF p.15: the classical endpoint is (1,0) at every dephasing weight. -/
example (p : ℝ) : qubitCorner p 0 = (1, 0) := by
  simp [qubitCorner, binEntropy2]

end QAlgorithms.Papers.Independent.Renew46.P36


