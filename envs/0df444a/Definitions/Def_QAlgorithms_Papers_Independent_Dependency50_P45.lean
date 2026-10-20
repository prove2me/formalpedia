-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
-- name    : QAlgorithms_Papers_Independent_Dependency50_P45
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:59:54.938621+00:00
-- url     : https://prove2.me/theorems/40659820-8fad-4e70-a8cf-4135f3c7909b
-- title:
--   Definitions for Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem
-- statement:
--   The objects the formalized statements of *Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem* (arXiv:quant-ph/0106052) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropyExchange`: PDF pp.6--10: entropy exchange in bits, using a canonical purification.
--   - `inputMutualInfo`: PDF Eq.(9), p.9: the single-input mutual information.
--   - `maximalMutualInfo`: PDF pp.23--24: maximum objective represented by its supremum. For CPTP maps on nonzero finite spaces the feasible values are nonempty and bounded. Theorem 1 below explicitly includes attainment.
--   - `resourceCopies`: PDF pp.4--5,13: e copies of a fixed pure resource, Bob first.
--   - `standardEbit`: PDF p.8: the standard ebit resource.
--   - `AssistedCode`: PDF pp.4--5,8,21: block code with unlimited copies of a fixed resource. Arbitrary local CPTP encoders include ancillary preparation and discarding. Collective POVM decoding includes Bob's local processing. No other communication.
--   - `encodedState`: PDF p.21: joint state after Alice's encoding, before the channel.
--   - `codeSuccess`: PDF Eq.(1): individual message success after n channel uses, without postselection.
--   - `inputMarginal`: PDF p.27: i-th marginal of a possibly entangled input density matrix.
--   - `codeCost`: PDF p.27: input cost averaged over messages and uses. n=0 is unused in rates.
--   - `AchievableWith`: PDF pp.4--5,8: operational achievable rate, optionally cost constrained. A single code and a message-independent resource precede every-message success.
--   - `resourceCapacity`: PDF pp.8,13: operational capacity for unlimited copies of the fixed resource.
--   - `constrainedCapacity`: PDF p.27: operational capacity with a linear average-input constraint.
--   - `IsSpectralData`: PDF pp.14--15: chosen orthonormal spectral data; zero eigenvalues are allowed.
--   - `typicalWords`: PDF p.15, Eq.(27): supported words satisfying all strict frequency tolerances.
--   - `eigenWord`: PDF p.15: tensor product of chosen eigenvectors.
--   - `typicalProjector`: PDF p.15: the actual frequency-typical orthogonal projector.
--   - `typicalState`: PDF p.15: projector divided by dimension; empty-space default is zero.
--   - `rectangularAct`: PDF p.14, Eq.(22): rectangular Kraus action, from input A to output B. The frozen `act` has square domain, so it is not used for these operators.
--   - `krausWord`: PDF pp.14,16, Eqs.(22),(31): normalized product Kraus output. The theorem excludes zero-probability individual Kraus outputs.
--   - `squareRootVector`: PDF p.19: projected square-root measurement vector, inverse only on support.
--   - `squareRootPOVM`: PDF p.19: POVM completion; none is failure outside the projected ensemble support.
--   - `dampingInput`: PDF p.34: the diagonal family rho_x.
--   - `dampingEAObjective`: PDF p.34: Eq.(9) at the fixed diagonal input, in binary entropy form.
--   - `dampingSignal`: PDF p.34, Eq.(89): the two pure signals with opposite off-diagonal signs.
--   - `dampingHolevoObjective`: PDF p.34: Holevo information of the equiprobable symmetric signal pair.
--   - `holevoCapacity`: PDF p.8, Eq.(8): single-use Holevo capacity over all finite ensembles.
--   - `MaximizesOnUnit`: PDF pp.34--35: actual attaining maximizer on the closed unit interval.
--   - `DMC`: PDF pp.35--36: a finite classical memoryless transition kernel.
--   - `blockProb`: PDF p.36: tensor power transition probabilities, including the empty block.
--   - `shannonCapacity`: PDF p.7: Shannon capacity as maximum single-letter mutual information in bits. For finite nonempty alphabets this set is nonempty, bounded, and attains its supremum.
--   - `RandomTape`: PDF p.36: an independent fair Bernoulli tape shared before any channel input.
--   - `tapeMeasure`: PDF p.36: the actual product probability measure of the fair tape.
--   - `ReverseProtocol`: PDF pp.36--39: deterministic conditional on the tape. Bob's only input is the forward bit string and the tape. Prefix-free messages prohibit free length signaling. All event fibers are measurable; no probability uses a nonmeasurable map.
--   - `reverseProb`: PDF Eq.(91), p.36: induced transition probability, including the whole random tape.
--   - `overflow`: PDF Eq.(92), p.36: worst-input communication overflow probability. For finite nonempty X the supremum is a maximum of probabilities in [0,1].
--   - `ChannelSimulation`: PDF pp.6,37,39: a shared-randomness protocol using a deterministic budget m of a source channel to produce n target outputs; no noiseless side channel.
--   - `simulatedProb`: PDF p.39: simulated probability, integrating shared randomness and actual channel noise.
--   - `UnitSimulation`: PDF p.39, Corollary 1: achieve unit asymptotic simulation efficiency. Uniform total variation convergence is equivalent to the classical fidelity criterion. The capacity-zero case is allowed; this asserts achievability, not optimality of rate one.
--   - `switchedChannel`: PDF p.3: the specified three-to-two-qubit switched channel as an explicit map. The switch is measured and discarded. In branch one the first remaining data qubit is retained and the other is replaced by I/2. Its full Q=Q2=1, C=CE=2 statement is deferred because interactive Q2 semantics are absent.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, https://arxiv.org/abs/quant-ph/0106052v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

/-!
Bennett--Shor--Smolin--Thapliyal, arXiv:quant-ph/0106052v2 (PDF pages).
Capacities below are operational suprema, never entropy formulas by definition.
Infinite-dimensional Gaussian channels and interactive two-way assistance are deferred.
-/

noncomputable section

open scoped ComplexConjugate Matrix
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF pp.6--10: entropy exchange in bits, using a canonical purification. -/
def entropyExchange {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  let e := Fintype.equivFin A
  let rhoFin : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℂ :=
    fun i j => rho (e.symm i) (e.symm j)
  let psi : EuclideanSpace ℂ (A × A) :=
    WithLp.toLp 2 fun z => canonicalPurification rhoFin (e z.1, e z.2)
  vnEntropy (idTensorSuperop (R := A) N (pureDensity psi))

/-- PDF Eq.(9), p.9: the single-input mutual information. -/
def inputMutualInfo {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  vnEntropy rho + vnEntropy (N rho) - entropyExchange N rho

/-- PDF pp.23--24: maximum objective represented by its supremum.
For CPTP maps on nonzero finite spaces the feasible values are nonempty and bounded.
Theorem 1 below explicitly includes attainment. -/
def maximalMutualInfo {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ v = inputMutualInfo N rho}

/-- PDF pp.4--5,13: e copies of a fixed pure resource, Bob first. -/
def resourceCopies {I J : Type*} (psi : EuclideanSpace ℂ (J × I)) (e : ℕ) :
    EuclideanSpace ℂ ((Fin e → J) × (Fin e → I)) :=
  WithLp.toLp 2 fun z => ∏ j, psi (z.1 j, z.2 j)

/-- PDF p.8: the standard ebit resource. -/
def standardEbit : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun z => if z.1 = z.2 then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF pp.4--5,8,21: block code with unlimited copies of a fixed resource.
Arbitrary local CPTP encoders include ancillary preparation and discarding.
Collective POVM decoding includes Bob's local processing. No other communication. -/
structure AssistedCode (I J A B : Type*) [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] (n k : ℕ) where
  e : ℕ
  encode : Qubits k → Superop (Fin e → I) (Fin n → A)
  encode_channel : ∀ x, IsChannel (encode x)
  measurement : Qubits k → Matrix ((Fin e → J) × (Fin n → B))
    ((Fin e → J) × (Fin n → B)) ℂ
  measurement_povm : IsPOVM measurement

/-- PDF p.21: joint state after Alice's encoding, before the channel. -/
def encodedState {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] {n k : ℕ}
    (psi : EuclideanSpace ℂ (J × I)) (P : AssistedCode I J A B n k) (x : Qubits k) :=
  idTensorSuperop (R := Fin P.e → J) (P.encode x) (pureDensity (resourceCopies psi P.e))

/-- PDF Eq.(1): individual message success after n channel uses, without postselection. -/
def codeSuccess {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] {n k : ℕ}
    (psi : EuclideanSpace ℂ (J × I)) (N : Superop A B)
    (P : AssistedCode I J A B n k) (x : Qubits k) : ℝ :=
  effectProb (P.measurement x)
    (idTensorSuperop (R := Fin P.e → J) (piSuperop (fun _ : Fin n => N))
      (encodedState psi P x))

/-- PDF p.27: i-th marginal of a possibly entangled input density matrix. -/
def inputMarginal {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (rho : Matrix (Fin n → A) (Fin n → A) ℂ) (i : Fin n) : Matrix A A ℂ :=
  Matrix.of fun a b => ∑ z : Fin n → A,
    if z i = a then rho z (Function.update z i b) else 0

/-- PDF p.27: input cost averaged over messages and uses. n=0 is unused in rates. -/
def codeCost {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] {n k : ℕ}
    (psi : EuclideanSpace ℂ (J × I)) (G : Matrix A A ℂ)
    (P : AssistedCode I J A B n k) : ℝ :=
  (∑ x : Qubits k, ∑ i : Fin n,
    (G * inputMarginal (traceLeft (encodedState psi P x)) i).trace.re) /
      ((n : ℝ) * (2 : ℝ) ^ k)

/-- PDF pp.4--5,8: operational achievable rate, optionally cost constrained.
A single code and a message-independent resource precede every-message success. -/
def AchievableWith {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] (psi : EuclideanSpace ℂ (J × I)) (N : Superop A B)
    (allowed : {n k : ℕ} → AssistedCode I J A B n k → Prop) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ,
    ∀ n ≥ n0, 0 < n → ∃ k : ℕ, (R - delta) * n ≤ k ∧
      ∃ P : AssistedCode I J A B n k, allowed P ∧ ∀ x, 1 - eps ≤ codeSuccess psi N P x

/-- PDF pp.8,13: operational capacity for unlimited copies of the fixed resource. -/
def resourceCapacity {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] (psi : EuclideanSpace ℂ (J × I)) (N : Superop A B) : ℝ :=
  sSup {R | AchievableWith psi N (fun {_ _} _ => True) R}

/-- PDF p.27: operational capacity with a linear average-input constraint. -/
def constrainedCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (G : Matrix A A ℂ) (S : ℝ) : ℝ :=
  sSup {R | AchievableWith standardEbit N (fun {_ _} P => codeCost standardEbit G P ≤ S) R}

/-- PDF pp.14--15: chosen orthonormal spectral data; zero eigenvalues are allowed. -/
def IsSpectralData {A : Type*} [Fintype A] [DecidableEq A]
    (rho : Matrix A A ℂ) (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) : Prop :=
  (∀ a, 0 ≤ lam a) ∧ ∑ a, lam a = 1 ∧
    rho = (U : Matrix A A ℂ) * Matrix.diagonal (fun a => (lam a : ℂ)) *
      (U : Matrix A A ℂ)ᴴ

/-- PDF p.15, Eq.(27): supported words satisfying all strict frequency tolerances. -/
def typicalWords {A : Type*} [Fintype A] [DecidableEq A]
    (lam : A → ℝ) (n : ℕ) (delta : ℝ) : Finset (Fin n → A) :=
  Finset.univ.filter fun z => (∀ i, 0 < lam (z i)) ∧
    ∀ a, 0 < lam a → |((Finset.univ.filter fun i : Fin n => z i = a).card : ℝ) - n * lam a| < n * delta

/-- PDF p.15: tensor product of chosen eigenvectors. -/
def eigenWord {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) {n : ℕ} (z : Fin n → A) : EuclideanSpace ℂ (Fin n → A) :=
  WithLp.toLp 2 fun x => ∏ i, (U : Matrix A A ℂ) (x i) (z i)

/-- PDF p.15: the actual frequency-typical orthogonal projector. -/
def typicalProjector {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (n : ℕ) (delta : ℝ) :
    Matrix (Fin n → A) (Fin n → A) ℂ :=
  ∑ z ∈ typicalWords lam n delta, pureDensity (eigenWord U z)

/-- PDF p.15: projector divided by dimension; empty-space default is zero. -/
def typicalState {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (n : ℕ) (delta : ℝ) :=
  (((typicalWords lam n delta).card : ℂ)⁻¹) • typicalProjector U lam n delta

/-- PDF p.14, Eq.(22): rectangular Kraus action, from input A to output B.
The frozen `act` has square domain, so it is not used for these operators. -/
def rectangularAct {A B : Type*} [Fintype A]
    (E : Matrix B A ℂ) (v : EuclideanSpace ℂ A) : EuclideanSpace ℂ B :=
  WithLp.toLp 2 (E.mulVec (WithLp.ofLp v))

/-- PDF pp.14,16, Eqs.(22),(31): normalized product Kraus output.
The theorem excludes zero-probability individual Kraus outputs. -/
def krausWord {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (E : K → Matrix B A ℂ)
    {n : ℕ} (alpha : Fin n → A) (beta : Fin n → K) : EuclideanSpace ℂ (Fin n → B) :=
  WithLp.toLp 2 fun y => ∏ j,
    let v : EuclideanSpace ℂ B := rectangularAct (E (beta j)) (WithLp.toLp 2 fun a =>
      (U : Matrix A A ℂ) a (alpha j))
    v (y j) / (‖v‖ : ℂ)

/-- PDF p.19: projected square-root measurement vector, inverse only on support. -/
def squareRootVector {O D : Type*} [Fintype O] [Fintype D] [DecidableEq D]
    (t : O → EuclideanSpace ℂ D) (P : Matrix D D ℂ) (i : O) : EuclideanSpace ℂ D :=
  let phi : Matrix D D ℂ := ∑ j, pureDensity (act P (t j))
  act (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) phi) (act P (t i))

/-- PDF p.19: POVM completion; none is failure outside the projected ensemble support. -/
def squareRootPOVM {O D : Type*} [Fintype O] [Fintype D] [DecidableEq D]
    (t : O → EuclideanSpace ℂ D) (P : Matrix D D ℂ) : Option O → Matrix D D ℂ
  | some i => pureDensity (squareRootVector t P i)
  | none => 1 - ∑ j, pureDensity (squareRootVector t P j)

/-- PDF p.34: the diagonal family rho_x. -/
def dampingInput (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 - x : ℝ) : ℂ), 0; 0, (x : ℂ)]

/-- PDF p.34: Eq.(9) at the fixed diagonal input, in binary entropy form. -/
def dampingEAObjective (p x : ℝ) : ℝ :=
  binEntropy2 x + binEntropy2 ((1 - p) * x) - binEntropy2 (p * x)

/-- PDF p.34, Eq.(89): the two pure signals with opposite off-diagonal signs. -/
def dampingSignal (x : ℝ) (positive : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  let off : ℂ := if positive then (Real.sqrt (x * (1 - x)) : ℂ)
    else -(Real.sqrt (x * (1 - x)) : ℂ)
  !![((1 - x : ℝ) : ℂ), off; off, (x : ℂ)]

/-- PDF p.34: Holevo information of the equiprobable symmetric signal pair. -/
def dampingHolevoObjective (p x : ℝ) : ℝ :=
  vnEntropy (dampingChannel p 1 (dampingInput x)) -
    (vnEntropy (dampingChannel p 1 (dampingSignal x true)) +
      vnEntropy (dampingChannel p 1 (dampingSignal x false))) / 2

/-- PDF p.8, Eq.(8): single-use Holevo capacity over all finite ensembles. -/
def holevoCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup {v | ∃ (m : ℕ) (q : Fin m → ℝ) (rho : Fin m → Matrix A A ℂ),
    (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧ (∀ j, IsDensityMatrix (rho j)) ∧
    v = vnEntropy (N (∑ j, (q j : ℂ) • rho j)) - ∑ j, q j * vnEntropy (N (rho j))}

/-- PDF pp.34--35: actual attaining maximizer on the closed unit interval. -/
def MaximizesOnUnit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, f y ≤ f x

/-- PDF pp.35--36: a finite classical memoryless transition kernel. -/
structure DMC (X Y : Type*) [Fintype Y] where
  prob : X → Y → ℝ
  nonnegative : ∀ x y, 0 ≤ prob x y
  normalized : ∀ x, ∑ y, prob x y = 1

/-- PDF p.36: tensor power transition probabilities, including the empty block. -/
def blockProb {X Y : Type*} [Fintype Y] (N : DMC X Y) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  ∏ i, N.prob (x i) (y i)

/-- PDF p.7: Shannon capacity as maximum single-letter mutual information in bits.
For finite nonempty alphabets this set is nonempty, bounded, and attains its supremum. -/
def shannonCapacity {X Y : Type*} [Fintype X] [Fintype Y] (N : DMC X Y) : ℝ :=
  sSup {v | ∃ q : X → ℝ, (∀ x, 0 ≤ q x) ∧ (∑ x, q x = 1) ∧
    v = mutualInfoBits (fun xy : X × Y => q xy.1 * N.prob xy.1 xy.2)}

/-- PDF p.36: an independent fair Bernoulli tape shared before any channel input. -/
abbrev RandomTape := ℕ → Bool

/-- PDF p.36: the actual product probability measure of the fair tape. -/
def tapeMeasure : Measure RandomTape :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- PDF pp.36--39: deterministic conditional on the tape. Bob's only input is the
forward bit string and the tape. Prefix-free messages prohibit free length signaling.
All event fibers are measurable; no probability uses a nonmeasurable map. -/
structure ReverseProtocol (X Y : Type*) (n : ℕ) where
  send : RandomTape → (Fin n → X) → List Bool
  receive : RandomTape → List Bool → (Fin n → Y)
  send_measurable : ∀ x s, MeasurableSet {r | send r x = s}
  receive_measurable : ∀ s y, MeasurableSet {r | receive r s = y}
  prefix_free : ∀ r x x', (send r x).IsPrefix (send r x') → send r x = send r x'

/-- PDF Eq.(91), p.36: induced transition probability, including the whole random tape. -/
def reverseProb {X Y : Type*} {n : ℕ} (P : ReverseProtocol X Y n)
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  (tapeMeasure {r | P.receive r (P.send r x) = y}).toReal

/-- PDF Eq.(92), p.36: worst-input communication overflow probability.
For finite nonempty X the supremum is a maximum of probabilities in [0,1]. -/
def overflow {X Y : Type*} [Fintype X] {n : ℕ}
    (P : ReverseProtocol X Y n) (threshold : ℝ) : ℝ :=
  sSup (Set.range fun x : Fin n → X =>
    (tapeMeasure {r | threshold < ((P.send r x).length : ℝ)}).toReal)

/-- PDF pp.6,37,39: a shared-randomness protocol using a deterministic budget m
of a source channel to produce n target outputs; no noiseless side channel. -/
structure ChannelSimulation (X Y U V : Type*) (m n : ℕ) where
  encode : RandomTape → (Fin n → U) → (Fin m → X)
  decode : RandomTape → (Fin m → Y) → (Fin n → V)
  encode_measurable : ∀ u x, MeasurableSet {r | encode r u = x}
  decode_measurable : ∀ y v, MeasurableSet {r | decode r y = v}

/-- PDF p.39: simulated probability, integrating shared randomness and actual channel noise. -/
def simulatedProb {X Y U V : Type*} [Fintype Y] {m n : ℕ}
    (N : DMC X Y) (P : ChannelSimulation X Y U V m n)
    (u : Fin n → U) (v : Fin n → V) : ℝ :=
  ∫ r, ∑ y : Fin m → Y,
    if P.decode r y = v then blockProb N m (P.encode r u) y else 0 ∂tapeMeasure

/-- PDF p.39, Corollary 1: achieve unit asymptotic simulation efficiency.
Uniform total variation convergence is equivalent to the classical fidelity criterion.
The capacity-zero case is allowed; this asserts achievability, not optimality of rate one. -/
def UnitSimulation {X Y U V : Type*} [Fintype Y] [Fintype U] [Fintype V]
    (N : DMC X Y) (M : DMC U V) : Prop :=
  ∃ m : ℕ → ℕ, ∃ P : (n : ℕ) → ChannelSimulation X Y U V (m n) n,
    Tendsto (fun n => (m n : ℝ) / n) atTop (nhds 1) ∧
    Tendsto (fun n => sSup (Set.range fun u : Fin n → U =>
      tvDist (simulatedProb N (P n) u) (blockProb M n u))) atTop (nhds 0)

example {X Y : Type*} [Fintype Y] (N : DMC X Y)
    (x : Fin 0 → X) (y : Fin 0 → Y) : blockProb N 0 x y = 1 := by
  simp [blockProb]

example : IsProbabilityMeasure tapeMeasure := by
  unfold tapeMeasure
  infer_instance

/-- PDF p.3: the specified three-to-two-qubit switched channel as an explicit map.
The switch is measured and discarded. In branch one the first remaining data
qubit is retained and the other is replaced by I/2. Its full Q=Q2=1, C=CE=2
statement is deferred because interactive Q2 semantics are absent. -/
def switchedChannel : Superop (Bool × (Bool × Bool)) (Bool × Bool) :=
  fun rho => Matrix.of fun u v =>
    (if u = v then rho (false, u) (false, u) else 0) +
      (if u.2 = v.2 then (∑ b : Bool, rho (true, (u.1, b)) (true, (v.1, b))) / 2 else 0)

example : canonicalPurification (1 : Matrix (Fin 1) (Fin 1) ℂ) (0, 0) = 1 := by
  simp [canonicalPurification, cfc_one]

example : standardEbit (false, true) = 0 := by
  simp [standardEbit]

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (rho : Matrix A A ℂ) :
    inputMutualInfo N rho = vnEntropy rho + vnEntropy (N rho) - entropyExchange N rho := rfl

example {A : Type*} [Fintype A] [DecidableEq A] (lam : A → ℝ)
    (delta : ℝ) (z : Fin 1 → A) (hz : lam (z 0) = 0) :
    z ∉ typicalWords lam 1 delta := by
  intro h
  have hpos : 0 < lam (z 0) := (Finset.mem_filter.mp h).2.1 0
  rw [hz] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

example {A B : Type*} [Fintype A] (E : Matrix B A ℂ)
    (v : EuclideanSpace ℂ A) (b : B) :
    rectangularAct E v b = ∑ a, E b a * v a := rfl

example {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (n : ℕ) (delta : ℝ)
    (h : typicalWords lam n delta = ∅) : typicalState U lam n delta = 0 := by
  simp [typicalState, h]

/-! Sanity examples for local definitions, not proofs of paper results. -/

example {I J : Type*} (psi : EuclideanSpace ℂ (J × I))
    (z : (Fin 0 → J) × (Fin 0 → I)) : resourceCopies psi 0 z = 1 := by
  simp [resourceCopies]

example : dampingInput 0 = !![(1 : ℂ), 0; 0, 0] := by
  simp [dampingInput]

example : dampingEAObjective 0 0 = 0 := by
  simp [dampingEAObjective, binEntropy2]

example {O D : Type*} [Fintype O] [Fintype D] [DecidableEq D]
    (t : O → EuclideanSpace ℂ D) (P : Matrix D D ℂ) :
    squareRootPOVM t P none = 1 - ∑ j, pureDensity (squareRootVector t P j) := rfl

end QAlgorithms.Papers.Independent.Dependency50.P45


