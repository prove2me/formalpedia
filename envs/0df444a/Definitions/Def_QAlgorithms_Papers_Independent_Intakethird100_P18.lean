-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P18
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P18
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:27:51.671233+00:00
-- url     : https://prove2.me/theorems/b3360924-b48d-4c2b-8c63-039246aac59f
-- title:
--   Definitions for On the role of coherent attacks in a type of strategic problem related to quantum key distribution
-- statement:
--   The objects the formalized statements of *On the role of coherent attacks in a type of strategic problem related to quantum key distribution* (arXiv:quant-ph/0110089) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LocalProtocol`: PDF pp.1–3: one local prepare-and-measure protocol, including local sifting. The three independent draws are the secret raw symbol, Alice's preparation choice, and Bob's measurement choice. Public announcements depend only on the last two choices. All retained ideal signals decode correctly; all errors in an attack are consequently channel errors, including Eve's action.
--   - `QkdLabel`: PDF pp.1–3: a local secret symbol and the two local settings.
--   - `qkdRetainedMass`: PDF p.2: probability of retaining a local signal under basis reconciliation; this is basis sifting, not a disturbance test or an acceptance event.
--   - `qkdLabelWeight`: PDF pp.2–3: the actual normalized distribution of a retained local input.
--   - `Inputs`: PDF pp.1–3: independent retained local inputs; the local distributions may differ.
--   - `Raw`: PDF pp.1–3: the entire raw string.
--   - `Public`: PDF pp.2–3: publicly revealed settings, with no secret raw symbols.
--   - `Signal`: PDF pp.1–3: computational coordinates on the tensor product signal register.
--   - `qkdInputWeight`: PDF p.3: actual ensemble probability of the independent local inputs.
--   - `inputAmplitude`: PDF pp.1–2: Alice's independent joint signal is the tensor product of the local normalized preparations. No identical-distribution assumption is made.
--   - `publicInput`: PDF p.2: the public basis/sifting announcement associated with an input.
--   - `rawInput`: PDF pp.2,5: the secret raw string is not public conditioning information.
--   - `JointSpace`: PDF p.2: finite signal register tensored with an arbitrary Hilbert ancilla, represented as a finite Hilbert direct sum of copies of the ancilla.
--   - `AncillaPOVM`: PDF p.2: arbitrary-outcome POVM on an arbitrary Hilbert ancilla. The scalar measures are pinned on every measurable set by the Born formula; their being measures expresses weak countable additivity of the operator POVM. They are not free probability kernels or an assumed information interface. Normalization makes the law of a unit vector a probability measure.
--   - `Attack`: PDF pp.2–3: an unrestricted coherent attack. The ancilla dimension and POVM outcome space are arbitrary. The initial ancilla and joint unitary do not depend on the secret input or on unrevealed settings. The delayed final POVM may depend on the public announcement, but not on any secret raw symbol.
--   - `qkdOutputState`: PDF p.2: the unitary output on Alice's tensor product and Eve's fixed probe.
--   - `qkdOutcomeLaw`: PDF pp.2–3: Eve's Born outcome law after tracing out Bob's signal register. The sum over Bob's computational coordinates is the partial trace; Eve can choose any joint POVM on her retained probe after the announcement.
--   - `bobCorrect`: PDF pp.2–3: probability that Bob's independent local measurement reads the correct raw symbol at coordinate i. The Kronecker deltas leave other signals untouched. This computes the local Born probability from the actual output.
--   - `qkdDisturbance`: PDF pp.2–4: the entire vector of ensemble-average local raw-symbol errors. No scalar mean, finite test sample, or passing-test conditioning replaces it.
--   - `qkdShannonBits`: PDF pp.3,5: Shannon entropy in bits, with 0 log 0 = 0.
--   - `priorMass`: PDF pp.3,5: subprobability mass of a raw word and public announcement, computed from Alice's independent ensemble and the protocol's local sifting.
--   - `publicMass`: PDF p.3: probability of a public configuration; zero-probability configurations have zero contribution to the average information.
--   - `qkdJointOutcome`: PDF pp.3,5: the joint submeasure of a secret raw word and Eve's outcome, with a specified public announcement. Every weight uses the actual ensemble.
--   - `publicOutcome`: PDF pp.3,5: Eve's outcome submeasure for a fixed public announcement.
--   - `posterior`: PDF p.5, eqs.(0.3),(0.5): the posterior raw-word probabilities given Eve's outcome and only the public announcement. Radon–Nikodym derivatives allow arbitrary measurable POVM outcome spaces; null outcomes do not affect averages.
--   - `experimentInformation`: PDF pp.3,5–6: ensemble-average total classical Shannon information about the whole raw string. It is H(raw|public) minus H(raw|public,Eve outcome), averaging both configurations and outcomes. This is measured classical information, not Holevo information or a final secret-key rate.
--   - `qkdInformation`: PDF p.3: Eve's information in the physical attack, using its computed Born law.
--   - `qkdOneSite`: PDF p.4: the single-signal protocol associated with one coordinate.
--   - `SingleAttack`: PDF p.4: a physical individual attack on one signal.
--   - `singleDisturbance`: PDF p.4: disturbance of a single-signal attack.
--   - `OptimalAt`: PDF p.4: being individually optimal at the exact prescribed disturbance. The comparison ranges over every physical single-signal attack, with arbitrary probe and delayed POVM. This predicate asserts optimality, not existence.
--   - `QkdFeasible`: PDF pp.3–4: a disturbance vector is feasible precisely when some physical attack on this protocol induces it. No numerical interval is substituted.
--   - `ProductAttack`: PDF pp.3–4, eq.(0.2): product of individual attacks, represented by the local unitaries, independent initial probes, and local POVMs. Both stages factor.
--   - `singleLaw`: PDF pp.3–4: the local Born law of one factor in a product attack.
--   - `qkdProductLaw`: PDF pp.3–4: actual joint outcome law of the tensor product attacking scheme. The finite product measure preserves every local outcome and announcement; there is no joint measurement substituted for the individual measurements.
--   - `productDisturbance`: PDF pp.3–4: local errors of the operational tensor product scheme.
--   - `productInformation`: PDF pp.3–5: the product scheme's information is computed from its product Born law and posterior entropy, rather than defined to be the sum.
-- source:
--   On the role of coherent attacks in a type of strategic problem related to quantum key distribution, arXiv:quant-ph/0110089v6, https://arxiv.org/abs/quant-ph/0110089v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Wang, arXiv:quant-ph/0110089v6, PDF pp.1–7.

The protocol describes independent finite signal ensembles and local sifting.
An attack has an arbitrary complete Hilbert ancilla and an arbitrary measurable
POVM outcome space. Its interaction is fixed before the secret input is drawn;
only its final POVM can depend on the public local announcements. The product
scheme is represented by its actual local physical attacks and the product of
their Born laws. It does not require a choice of coordinates on their tensor
product ancilla. All information quantities concern the raw string, in bits.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P18

/-- PDF pp.1–3: one local prepare-and-measure protocol, including local sifting.
The three independent draws are the secret raw symbol, Alice's preparation
choice, and Bob's measurement choice. Public announcements depend only on the
last two choices. All retained ideal signals decode correctly; all errors in
an attack are consequently channel errors, including Eve's action. -/
structure LocalProtocol where
  rawSize : ℕ
  prepSize : ℕ
  bobSize : ℕ
  publicSize : ℕ
  dimension : ℕ
  raw_pos : 0 < rawSize
  prep_pos : 0 < prepSize
  bob_pos : 0 < bobSize
  public_pos : 0 < publicSize
  dimension_pos : 0 < dimension
  rawWeight : Fin rawSize → ℝ
  prepWeight : Fin prepSize → ℝ
  bobWeight : Fin bobSize → ℝ
  raw_nonneg : ∀ x, 0 ≤ rawWeight x
  prep_nonneg : ∀ a, 0 ≤ prepWeight a
  bob_nonneg : ∀ b, 0 ≤ bobWeight b
  raw_total : ∑ x, rawWeight x = 1
  prep_total : ∑ a, prepWeight a = 1
  bob_total : ∑ b, bobWeight b = 1
  prepare : Fin rawSize → Fin prepSize → EuclideanSpace ℂ (Fin dimension)
  prepare_unit : ∀ x a, QAlgorithms.IsState (prepare x a)
  bobPOVM : Fin bobSize → Fin rawSize → Matrix (Fin dimension) (Fin dimension) ℂ
  bob_valid : ∀ b, QAlgorithms.IsPOVM (bobPOVM b)
  keep : Fin prepSize → Fin bobSize → Bool
  announce : Fin prepSize → Fin bobSize → Fin publicSize
  retained_positive : 0 < ∑ a, ∑ b,
    if keep a b then prepWeight a * bobWeight b else 0
  ideal_correct : ∀ x a b, keep a b = true →
    QAlgorithms.effectProb (bobPOVM b x) (QAlgorithms.pureDensity (prepare x a)) = 1

/-- PDF pp.1–3: a local secret symbol and the two local settings. -/
abbrev QkdLabel (P : LocalProtocol) :=
  Fin P.rawSize × Fin P.prepSize × Fin P.bobSize

/-- PDF p.2: probability of retaining a local signal under basis reconciliation;
this is basis sifting, not a disturbance test or an acceptance event. -/
def qkdRetainedMass (P : LocalProtocol) : ℝ :=
  ∑ a, ∑ b, if P.keep a b then P.prepWeight a * P.bobWeight b else 0

/-- PDF pp.2–3: the actual normalized distribution of a retained local input. -/
def qkdLabelWeight (P : LocalProtocol) (l : QkdLabel P) : ℝ :=
  if P.keep l.2.1 l.2.2 then
    P.rawWeight l.1 * P.prepWeight l.2.1 * P.bobWeight l.2.2 / qkdRetainedMass P
  else 0

/-- PDF pp.1–3: independent retained local inputs; the local distributions may differ. -/
abbrev Inputs {n : ℕ} (P : Fin n → LocalProtocol) := ∀ i, QkdLabel (P i)

/-- PDF pp.1–3: the entire raw string. -/
abbrev Raw {n : ℕ} (P : Fin n → LocalProtocol) := ∀ i, Fin (P i).rawSize

/-- PDF pp.2–3: publicly revealed settings, with no secret raw symbols. -/
abbrev Public {n : ℕ} (P : Fin n → LocalProtocol) := ∀ i, Fin (P i).publicSize

/-- PDF pp.1–3: computational coordinates on the tensor product signal register. -/
abbrev Signal {n : ℕ} (P : Fin n → LocalProtocol) := ∀ i, Fin (P i).dimension

/-- PDF p.3: actual ensemble probability of the independent local inputs. -/
def qkdInputWeight {n : ℕ} (P : Fin n → LocalProtocol) (l : Inputs P) : ℝ :=
  ∏ i, qkdLabelWeight (P i) (l i)

/-- PDF pp.1–2: Alice's independent joint signal is the tensor product of the
local normalized preparations. No identical-distribution assumption is made. -/
def inputAmplitude {n : ℕ} (P : Fin n → LocalProtocol) (l : Inputs P)
    (z : Signal P) : ℂ :=
  ∏ i, (P i).prepare (l i).1 (l i).2.1 (z i)

/-- PDF p.2: the public basis/sifting announcement associated with an input. -/
def publicInput {n : ℕ} (P : Fin n → LocalProtocol) (l : Inputs P) : Public P :=
  fun i => (P i).announce (l i).2.1 (l i).2.2

/-- PDF pp.2,5: the secret raw string is not public conditioning information. -/
def rawInput {n : ℕ} (P : Fin n → LocalProtocol) (l : Inputs P) : Raw P :=
  fun i => (l i).1

/-- PDF p.2: finite signal register tensored with an arbitrary Hilbert ancilla,
represented as a finite Hilbert direct sum of copies of the ancilla. -/
abbrev JointSpace {n : ℕ} (P : Fin n → LocalProtocol) (E : Type)
    [NormedAddCommGroup E] := PiLp 2 (fun _ : Signal P => E)

/-- PDF p.2: arbitrary-outcome POVM on an arbitrary Hilbert ancilla.
The scalar measures are pinned on every measurable set by the Born formula;
their being measures expresses weak countable additivity of the operator POVM.
They are not free probability kernels or an assumed information interface.
Normalization makes the law of a unit vector a probability measure. -/
structure AncillaPOVM (E O : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [MeasurableSpace O] where
  effect : Set O → E →L[ℂ] E
  positive : ∀ B, MeasurableSet B → ∀ v,
    (inner ℂ v (effect B v)).im = 0 ∧ 0 ≤ (inner ℂ v (effect B v)).re
  normalized : effect Set.univ = ContinuousLinearMap.id ℂ E
  law : E → Measure O
  born : ∀ v B, MeasurableSet B →
    law v B = ENNReal.ofReal (inner ℂ v (effect B v)).re

/-- PDF pp.2–3: an unrestricted coherent attack. The ancilla dimension and
POVM outcome space are arbitrary. The initial ancilla and joint unitary do not
depend on the secret input or on unrevealed settings. The delayed final POVM
may depend on the public announcement, but not on any secret raw symbol. -/
structure Attack {n : ℕ} (P : Fin n → LocalProtocol) where
  Ancilla : Type
  [ancillaNorm : NormedAddCommGroup Ancilla]
  [ancillaInner : InnerProductSpace ℂ Ancilla]
  [ancillaComplete : CompleteSpace Ancilla]
  initial : Ancilla
  initial_unit : ‖initial‖ = 1
  unitary : JointSpace P Ancilla ≃ₗᵢ[ℂ] JointSpace P Ancilla
  Outcome : Type
  [outcomeMeasurable : MeasurableSpace Outcome]
  measurement : Public P → AncillaPOVM Ancilla Outcome

attribute [instance] Attack.ancillaNorm Attack.ancillaInner Attack.ancillaComplete
attribute [instance] Attack.outcomeMeasurable

/-- PDF p.2: the unitary output on Alice's tensor product and Eve's fixed probe. -/
def qkdOutputState {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P)
    (l : Inputs P) : JointSpace P A.Ancilla :=
  A.unitary (WithLp.toLp 2 (fun z => inputAmplitude P l z • A.initial))

/-- PDF pp.2–3: Eve's Born outcome law after tracing out Bob's signal register.
The sum over Bob's computational coordinates is the partial trace; Eve can
choose any joint POVM on her retained probe after the announcement. -/
def qkdOutcomeLaw {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P)
    (l : Inputs P) (c : Public P) : Measure A.Outcome :=
  ∑ z : Signal P, (A.measurement c).law (qkdOutputState A l z)

/-- PDF pp.2–3: probability that Bob's independent local measurement reads the
correct raw symbol at coordinate i. The Kronecker deltas leave other signals
untouched. This computes the local Born probability from the actual output. -/
def bobCorrect {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P)
    (l : Inputs P) (i : Fin n) : ℝ :=
  (∑ z : Signal P, ∑ w : Signal P,
    if ∀ j, j ≠ i → z j = w j then
      (P i).bobPOVM (l i).2.2 (l i).1 (z i) (w i) *
        inner ℂ (qkdOutputState A l z) (qkdOutputState A l w)
    else 0).re

/-- PDF pp.2–4: the entire vector of ensemble-average local raw-symbol errors.
No scalar mean, finite test sample, or passing-test conditioning replaces it. -/
def qkdDisturbance {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P) : Fin n → ℝ :=
  fun i => ∑ l : Inputs P, qkdInputWeight P l * (1 - bobCorrect A l i)

/-- PDF pp.3,5: Shannon entropy in bits, with 0 log 0 = 0. -/
def qkdShannonBits {X : Type} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * (Real.log (p x) / Real.log 2)

/-- PDF pp.3,5: subprobability mass of a raw word and public announcement,
computed from Alice's independent ensemble and the protocol's local sifting. -/
def priorMass {n : ℕ} (P : Fin n → LocalProtocol) (c : Public P) (x : Raw P) : ℝ :=
  ∑ l : Inputs P,
    if publicInput P l = c ∧ rawInput P l = x then qkdInputWeight P l else 0

/-- PDF p.3: probability of a public configuration; zero-probability configurations
have zero contribution to the average information. -/
def publicMass {n : ℕ} (P : Fin n → LocalProtocol) (c : Public P) : ℝ :=
  ∑ x : Raw P, priorMass P c x

/-- PDF pp.3,5: the joint submeasure of a secret raw word and Eve's outcome,
with a specified public announcement. Every weight uses the actual ensemble. -/
def qkdJointOutcome {n : ℕ} (P : Fin n → LocalProtocol) {O : Type}
    [MeasurableSpace O] (law : Inputs P → Public P → Measure O)
    (c : Public P) (x : Raw P) : Measure O :=
  ∑ l : Inputs P,
    if publicInput P l = c ∧ rawInput P l = x then
      ENNReal.ofReal (qkdInputWeight P l) • law l c
    else 0

/-- PDF pp.3,5: Eve's outcome submeasure for a fixed public announcement. -/
def publicOutcome {n : ℕ} (P : Fin n → LocalProtocol) {O : Type}
    [MeasurableSpace O] (law : Inputs P → Public P → Measure O)
    (c : Public P) : Measure O :=
  ∑ x : Raw P, qkdJointOutcome P law c x

/-- PDF p.5, eqs.(0.3),(0.5): the posterior raw-word probabilities given Eve's
outcome and only the public announcement. Radon–Nikodym derivatives allow
arbitrary measurable POVM outcome spaces; null outcomes do not affect averages. -/
def posterior {n : ℕ} (P : Fin n → LocalProtocol) {O : Type}
    [MeasurableSpace O] (law : Inputs P → Public P → Measure O)
    (c : Public P) (y : O) (x : Raw P) : ℝ :=
  ((qkdJointOutcome P law c x).rnDeriv (publicOutcome P law c) y).toReal

/-- PDF pp.3,5–6: ensemble-average total classical Shannon information about
the whole raw string. It is H(raw|public) minus H(raw|public,Eve outcome),
averaging both configurations and outcomes. This is measured classical
information, not Holevo information or a final secret-key rate. -/
def experimentInformation {n : ℕ} (P : Fin n → LocalProtocol) {O : Type}
    [MeasurableSpace O] (law : Inputs P → Public P → Measure O) : ℝ :=
  ∑ c : Public P,
    (publicMass P c * qkdShannonBits (fun x => priorMass P c x / publicMass P c) -
      ∫ y, qkdShannonBits (posterior P law c y) ∂(publicOutcome P law c))

/-- PDF p.3: Eve's information in the physical attack, using its computed Born law. -/
def qkdInformation {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P) : ℝ :=
  experimentInformation P (qkdOutcomeLaw A)

/-- PDF p.4: the single-signal protocol associated with one coordinate. -/
def qkdOneSite (P : LocalProtocol) : Fin 1 → LocalProtocol := fun _ => P

/-- PDF p.4: a physical individual attack on one signal. -/
abbrev SingleAttack (P : LocalProtocol) := Attack (qkdOneSite P)

/-- PDF p.4: disturbance of a single-signal attack. -/
def singleDisturbance {P : LocalProtocol} (A : SingleAttack P) : ℝ :=
  qkdDisturbance A 0

/-- PDF p.4: being individually optimal at the exact prescribed disturbance.
The comparison ranges over every physical single-signal attack, with arbitrary
probe and delayed POVM. This predicate asserts optimality, not existence. -/
def OptimalAt (P : LocalProtocol) (d : ℝ) (A : SingleAttack P) : Prop :=
  singleDisturbance A = d ∧
    ∀ B : SingleAttack P, singleDisturbance B = d → qkdInformation B ≤ qkdInformation A

/-- PDF pp.3–4: a disturbance vector is feasible precisely when some physical
attack on this protocol induces it. No numerical interval is substituted. -/
def QkdFeasible {n : ℕ} (P : Fin n → LocalProtocol) (d : Fin n → ℝ) : Prop :=
  ∃ A : Attack P, qkdDisturbance A = d

/-- PDF pp.3–4, eq.(0.2): product of individual attacks, represented by the local
unitaries, independent initial probes, and local POVMs. Both stages factor. -/
abbrev ProductAttack {n : ℕ} (P : Fin n → LocalProtocol) :=
  ∀ i, SingleAttack (P i)

/-- PDF pp.3–4: the local Born law of one factor in a product attack. -/
def singleLaw {P : LocalProtocol} (A : SingleAttack P) (l : QkdLabel P)
    (c : Fin P.publicSize) : Measure A.Outcome :=
  qkdOutcomeLaw A (fun _ => l) (fun _ => c)

/-- PDF pp.3–4: actual joint outcome law of the tensor product attacking scheme.
The finite product measure preserves every local outcome and announcement;
there is no joint measurement substituted for the individual measurements. -/
def qkdProductLaw {n : ℕ} {P : Fin n → LocalProtocol} (A : ProductAttack P)
    (l : Inputs P) (c : Public P) : Measure (∀ i, (A i).Outcome) :=
  Measure.pi (fun i => singleLaw (A i) (l i) (c i))

/-- PDF pp.3–4: local errors of the operational tensor product scheme. -/
def productDisturbance {n : ℕ} {P : Fin n → LocalProtocol}
    (A : ProductAttack P) : Fin n → ℝ :=
  fun i => singleDisturbance (A i)

/-- PDF pp.3–5: the product scheme's information is computed from its product
Born law and posterior entropy, rather than defined to be the sum. -/
def productInformation {n : ℕ} {P : Fin n → LocalProtocol}
    (A : ProductAttack P) : ℝ :=
  experimentInformation P (qkdProductLaw A)

/-- Sanity check for PDF p.5: a deterministic distribution has zero uncertainty. -/
example : qkdShannonBits (fun _ : Unit => (1 : ℝ)) = 0 := by
  simp [qkdShannonBits]

/-- Sanity check: a zero-probability symbol contributes zero, without log singularities. -/
example : (0 : ℝ) * (Real.log 0 / Real.log 2) = 0 := by
  simp

/-- Sanity check: arbitrary-outcome POVM laws really use the normalized Born rule. -/
example {E O : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [MeasurableSpace O] (M : AncillaPOVM E O) (v : E) :
    M.law v Set.univ = ENNReal.ofReal (inner ℂ v v).re := by
  rw [M.born v Set.univ MeasurableSet.univ, M.normalized]
  rfl

/-- Sanity check: an empty measurable event has zero outcome probability. -/
example {E O : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [MeasurableSpace O] (M : AncillaPOVM E O) (v : E) : M.law v ∅ = 0 := by
  exact measure_empty

/-- Sanity check: the physical interaction preserves norms on the whole joint space. -/
example {n : ℕ} {P : Fin n → LocalProtocol} (A : Attack P)
    (v : JointSpace P A.Ancilla) : ‖A.unitary v‖ = ‖v‖ := by
  exact A.unitary.norm_map v

end QAlgorithms.Papers.Independent.Intakethird100.P18


