-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02
-- name    : QAlgorithms_Papers_Independent_Support50_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:06:14.34463+00:00
-- url     : https://prove2.me/theorems/cb9a88e1-9660-4f00-897c-910d8bf74f86
-- title:
--   Definitions for Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions
-- statement:
--   The objects the formalized statements of *Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions* (arXiv:quant-ph/0501045) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `independentPairs`: Reindex two independent reference/input pairs as (references, inputs), pp.5–7, (8).
--   - `macPower`: Memoryless MAC power with each sender's n inputs grouped together, pp.5–7.
--   - `bellPair`: Product of two Bell targets, regrouped as (references, receiver outputs), p.7.
--   - `cqInput`: Alice's input and Bob's independent reference/input state in (7), p.8.
--   - `cqMessageTarget`: Joint classical label/pure quantum target, with reference first, pp.6–7,23.
--   - `dephaseClassicalRegister`: Dephase the decoder's classical register, making its output an instrument, pp.5–6.
--   - `pureEnsembleAverage`: The average state, p.4.
--   - `CQMacData`: Data of (7), p.8: one Alice ensemble and one independent pure Bob pair.
--   - `CQMacData.output`: Conditional BC states from that same input data, (7), p.8.
--   - `CQMacData.averageOutput`: Average BC output of (7), p.8.
--   - `CQMacData.classical`: I(X;C) of (7), pp.4,8.
--   - `CQMacData.conditionalCoherent`: I_c(B coherent-to CX), evaluated on the SAME state (7), pp.4,8.
--   - `CQMacData.sideClassical`: I(X;BC) of (7), p.30.
--   - `CQMacData.coherent`: I_c(B coherent-to C) of the averaged BC state, p.30.
--   - `QQData`: Data of (8), p.8: independent pure reference/input pairs, with arbitrary references.
--   - `QQData.output`: The actual ABC output in (8), reference pair grouped first, p.8.
--   - `QQData.bobOutput`: BC marginal computed by tracing Alice's reference from that output, p.8.
--   - `QQData.aliceOutput`: AC marginal computed by tracing Bob's reference from that output, p.8.
--   - `QQData.aliceConditional`: I_c(A coherent-to BC), p.8.
--   - `QQData.bobConditional`: I_c(B coherent-to AC), p.8.
--   - `QQData.sumCoherent`: I_c(AB coherent-to C), p.8.
--   - `QQData.aliceCoherent`: I_c(A coherent-to C), p.30.
--   - `QQData.bobCoherent`: I_c(B coherent-to C), p.30.
--   - `Nonnegative`: Nonnegative operational rate pairs, pp.5–8.
--   - `CQMacData.Rectangle`: Boundary-inclusive rectangle from a fixed state (7), pp.7–8,13. Correction: replace the printed strict signs BEFORE closure; the replacer edge otherwise excludes (0,0). This does not claim equality of the strict and closed unions.
--   - `cqOne`: CQ one-use region; optional cap on the alphabet, pp.8,36.
--   - `QQData.Pentagon`: One-state qq pentagon with ALL three constraints, pp.8,18. The same disclosed non-strict boundary correction as for Theorem 1 is used.
--   - `qqOne`: QQ one-use pentagon union, p.8.
--   - `qqRectangles`: Earlier qq rectangle union, on the SAME product inputs (8), p.30.
--   - `cqPentagons`: Alternative cq pentagons on a single state (7), p.30.
--   - `regularized`: Positive-block regularization, with multiplication avoiding division at k=0, pp.7–8,30.
--   - `CQGeneration`: CQ generation code, pp.5–6, (1)–(2): separate pure preparations and joint decoder. A final dephasing in `cqDecoded` makes the classical output an instrument.
--   - `cqDecoded`: Apply the one n-use joint channel and decoder while leaving Bob's reference untouched, then read the classical decoder output, pp.5–7.
--   - `CQGeneration.Good`: Uniform-message average of a JOINT classical/Bell fidelity, (1)–(2), p.6.
--   - `CQTransmission`: CQ entanglement transmission, pp.6–7: local CPTP encoder on a Bell half only.
--   - `CQTransmission.Good`: Transmission success (3)–(4), pp.6–7; reference is never acted on by the encoder.
--   - `CQStrong`: CQ strong transmission, p.23: local stochastic classical preparations, one fixed quantum encoder and one fixed joint decoder. Mixed message states represent finite private random pure preparations after discarding Alice's private seed. No seed is available to Charlie except through the charged n channel uses.
--   - `CQStrong.Good`: Maximal JOINT error for every classical message and every reference/input pure state, (36), p.23. Correction: test the ORIGINAL message, as the inverse cyclic relabeling on p.25 does. The printed arbitrary f(m) target would permit a constant f.
--   - `QQGeneration`: QQ generation code, p.7, (5); the sender preparations are independent.
--   - `QQGeneration.Good`: One fidelity against the PRODUCT Bell target, (5), p.7.
--   - `QQTransmission`: QQ transmission code, (6), p.7; two individually local CPTP encoders, no reference access or pre-shared sender/decoder resources.
--   - `QQTransmission.decoded`: Encoders act only on the two input halves; channel and decoder act jointly, p.7.
--   - `QQTransmission.Good`: One simultaneous fidelity, not separate marginal fidelities, (6), p.7.
--   - `QQTransmission.Strong`: Strong qq transmission, (37), pp.23–24: all independent external references, allowing arbitrary entanglement WITHIN each pair, and one product-target fidelity.
--   - `operationalRegion`: Closed region from actual integer-rank codes with vanishing error and arbitrary asymptotic rate slack, pp.6–7. Positive n,m,k guard all logs, divisions, and targets. The code predicate contains its existential code BEFORE its universal input tests.
--   - `MACScenario`: The three operational tasks, pp.5–7,23–24.
--   - `cqMacCapacity`: Closed operational CQ region for the chosen task, pp.5–7,23.
--   - `qqMacCapacity`: Closed operational Q region for the chosen task, pp.5–7,23–24.
--   - `optimizedSum`: Optimized sum information over exactly product purifications (8), p.30. For finite positive physical dimensions and CPTP N, this set is nonempty and bounded; reference compression bounds their dimensions and gives attainment.
--   - `controlledErasure`: Corrected controlled-erasure channel of §7.1, PDF p.32. Printed N0=sum_j |flag><0,j| and Ni=|i><1,i| are NOT TP and dephase Bob. The prose and N(tau tensor rho)=tau00|flag><flag|+tau11 rho instead specify K_j=|flag><0,j| and ONE L=sum_j |j><1,j|. This entry formula implements those Kraus operators, retaining transfer-sector coherences.
--   - `collectivePhaseOperator`: Collective phase flip Z tensor Z, §7.2, PDF p.34.
--   - `collectivePhase`: The convex mixture (1-p)rho+p(Z tensor Z)rho(Z tensor Z), p.34.
--   - `inputCoherent`: Channel coherent information using the SAME isometric extension for both outputs, §7.3, PDF p.35. For density rho this equals the purification definition.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, https://arxiv.org/abs/quant-ph/0501045v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

/-!
Yard–Devetak–Hayden, arXiv:quant-ph/0501045v3. Page numbers are PDF pages.
All registers are finite, dimensions in statements are positive, entropy is in bits,
fidelity is squared Uhlmann fidelity, and trace distance is the FULL trace norm.
The operational code definitions below are independent of the information regions.
Operator matrices, normalized pure ensembles, and Bell densities reuse accepted primitives.
Paper-specific MAC definitions have names distinct from unrelated frozen concepts.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)
open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Reindex two independent reference/input pairs as (references, inputs), pp.5–7, (8). -/
def independentPairs (rho : Op (R × A)) (tau : Op (S × B)) : Op ((R × S) × (A × B)) :=
  fun i j => rho (i.1.1, i.2.1) (j.1.1, j.2.1) * tau (i.1.2, i.2.2) (j.1.2, j.2.2)

/-- Memoryless MAC power with each sender's n inputs grouped together, pp.5–7. -/
def macPower (N : Superop (A × B) C) (n : ℕ) :
    Superop ((Fin n → A) × (Fin n → B)) (Fin n → C) :=
  fun rho => piSuperop (fun _ : Fin n => N)
    (fun x y => rho ((fun k => (x k).1), (fun k => (x k).2))
      ((fun k => (y k).1), (fun k => (y k).2)))

/-- Product of two Bell targets, regrouped as (references, receiver outputs), p.7. -/
def bellPair (a b : ℕ) : Op ((Fin a × Fin b) × (Fin a × Fin b)) :=
  independentPairs (epr a) (epr b)

/-- Alice's input and Bob's independent reference/input state in (7), p.8. -/
def cqInput (rho : Op A) (tau : Op (R × B)) : Op (R × (A × B)) :=
  fun i j => rho i.2.1 j.2.1 * tau (i.1,i.2.2) (j.1,j.2.2)

/-- Joint classical label/pure quantum target, with reference first, pp.6–7,23. -/
def cqMessageTarget {m : ℕ} (s : Fin m) (rho : Op (R × I)) : Op (R × (Fin m × I)) :=
  fun i j => if i.2.1 = s ∧ j.2.1 = s then rho (i.1,i.2.2) (j.1,j.2.2) else 0

/-- Dephase the decoder's classical register, making its output an instrument, pp.5–6. -/
def dephaseClassicalRegister {m : ℕ} (rho : Op (R × (Fin m × I))) : Op (R × (Fin m × I)) :=
  fun i j => if i.2.1 = j.2.1 then rho i j else 0

/-- The average state, p.4. -/
def pureEnsembleAverage (P : PureEnsemble A) : Op A :=
  ∑ x, (P.weight x : ℂ) • pureDensity (P.vector x)

/-- Data of (7), p.8: one Alice ensemble and one independent pure Bob pair. -/
structure CQMacData (A B : Type*) [Fintype A] [Fintype B] where
  ensemble : PureEnsemble A
  bobRank : ℕ
  bobPositive : 0 < bobRank
  bob : EuclideanSpace ℂ (Fin bobRank × B)
  bobUnit : IsState bob

/-- Conditional BC states from that same input data, (7), p.8. -/
def CQMacData.output (D : CQMacData A B) (N : Superop (A × B) C)
    (x : Fin D.ensemble.count) : Op (Fin D.bobRank × C) :=
  idTensorSuperop N (cqInput (pureDensity (D.ensemble.vector x)) (pureDensity D.bob))

/-- Average BC output of (7), p.8. -/
def CQMacData.averageOutput (D : CQMacData A B) (N : Superop (A × B) C) : Op (Fin D.bobRank × C) :=
  ∑ x, (D.ensemble.weight x : ℂ) • D.output N x

/-- I(X;C) of (7), pp.4,8. -/
def CQMacData.classical (D : CQMacData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (traceLeft (D.averageOutput N)) -
    ∑ x, D.ensemble.weight x * vnEntropy (traceLeft (D.output N x))

/-- I_c(B coherent-to CX), evaluated on the SAME state (7), pp.4,8. -/
def CQMacData.conditionalCoherent (D : CQMacData A B) (N : Superop (A × B) C) : ℝ :=
  ∑ x, D.ensemble.weight x *
    (vnEntropy (traceLeft (D.output N x)) - vnEntropy (D.output N x))

/-- I(X;BC) of (7), p.30. -/
def CQMacData.sideClassical (D : CQMacData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (D.averageOutput N) - ∑ x, D.ensemble.weight x * vnEntropy (D.output N x)

/-- I_c(B coherent-to C) of the averaged BC state, p.30. -/
def CQMacData.coherent (D : CQMacData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (traceLeft (D.averageOutput N)) - vnEntropy (D.averageOutput N)

/-- Data of (8), p.8: independent pure reference/input pairs, with arbitrary references. -/
structure QQData (A B : Type*) [Fintype A] [Fintype B] where
  aliceRank : ℕ
  alicePositive : 0 < aliceRank
  bobRank : ℕ
  bobPositive : 0 < bobRank
  alice : EuclideanSpace ℂ (Fin aliceRank × A)
  aliceUnit : IsState alice
  bob : EuclideanSpace ℂ (Fin bobRank × B)
  bobUnit : IsState bob

/-- The actual ABC output in (8), reference pair grouped first, p.8. -/
def QQData.output (D : QQData A B) (N : Superop (A × B) C) :
    Op ((Fin D.aliceRank × Fin D.bobRank) × C) :=
  idTensorSuperop N (independentPairs (pureDensity D.alice) (pureDensity D.bob))

/-- BC marginal computed by tracing Alice's reference from that output, p.8. -/
def QQData.bobOutput (D : QQData A B) (N : Superop (A × B) C) : Op (Fin D.bobRank × C) :=
  fun i j => ∑ a, D.output N ((a,i.1),i.2) ((a,j.1),j.2)

/-- AC marginal computed by tracing Bob's reference from that output, p.8. -/
def QQData.aliceOutput (D : QQData A B) (N : Superop (A × B) C) : Op (Fin D.aliceRank × C) :=
  fun i j => ∑ b, D.output N ((i.1,b),i.2) ((j.1,b),j.2)

/-- I_c(A coherent-to BC), p.8. -/
def QQData.aliceConditional (D : QQData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (D.bobOutput N) - vnEntropy (D.output N)

/-- I_c(B coherent-to AC), p.8. -/
def QQData.bobConditional (D : QQData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (D.aliceOutput N) - vnEntropy (D.output N)

/-- I_c(AB coherent-to C), p.8. -/
def QQData.sumCoherent (D : QQData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (traceLeft (D.output N)) - vnEntropy (D.output N)

/-- I_c(A coherent-to C), p.30. -/
def QQData.aliceCoherent (D : QQData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (traceLeft (D.output N)) - vnEntropy (D.aliceOutput N)

/-- I_c(B coherent-to C), p.30. -/
def QQData.bobCoherent (D : QQData A B) (N : Superop (A × B) C) : ℝ :=
  vnEntropy (traceLeft (D.output N)) - vnEntropy (D.bobOutput N)

/-- Nonnegative operational rate pairs, pp.5–8. -/
def Nonnegative (r : ℝ × ℝ) : Prop := 0 ≤ r.1 ∧ 0 ≤ r.2

/-- Boundary-inclusive rectangle from a fixed state (7), pp.7–8,13.
Correction: replace the printed strict signs BEFORE closure; the replacer edge
otherwise excludes (0,0). This does not claim equality of the strict and closed unions. -/
def CQMacData.Rectangle (D : CQMacData A B) (N : Superop (A × B) C) (r : ℝ × ℝ) : Prop :=
  Nonnegative r ∧ r.1 ≤ D.classical N ∧ r.2 ≤ D.conditionalCoherent N

/-- CQ one-use region; optional cap on the alphabet, pp.8,36. -/
def cqOne (N : Superop (A × B) C) (cap : Option ℕ := none) : Set (ℝ × ℝ) :=
  {r | ∃ D : CQMacData A B, (∀ b ∈ cap, D.ensemble.count ≤ b) ∧ D.Rectangle N r}

/-- One-state qq pentagon with ALL three constraints, pp.8,18.
The same disclosed non-strict boundary correction as for Theorem 1 is used. -/
def QQData.Pentagon (D : QQData A B) (N : Superop (A × B) C) (r : ℝ × ℝ) : Prop :=
  Nonnegative r ∧ r.1 ≤ D.aliceConditional N ∧ r.2 ≤ D.bobConditional N ∧
    r.1 + r.2 ≤ D.sumCoherent N

/-- QQ one-use pentagon union, p.8. -/
def qqOne (N : Superop (A × B) C) : Set (ℝ × ℝ) :=
  {r | ∃ D : QQData A B, D.Pentagon N r}

/-- Earlier qq rectangle union, on the SAME product inputs (8), p.30. -/
def qqRectangles (N : Superop (A × B) C) : Set (ℝ × ℝ) :=
  {r | Nonnegative r ∧ ∃ D : QQData A B,
    r.1 ≤ D.aliceCoherent N ∧ r.2 ≤ D.bobCoherent N}

/-- Alternative cq pentagons on a single state (7), p.30. -/
def cqPentagons (N : Superop (A × B) C) : Set (ℝ × ℝ) :=
  {r | Nonnegative r ∧ ∃ D : CQMacData A B, r.1 ≤ D.sideClassical N ∧
    r.2 ≤ D.conditionalCoherent N ∧ r.1 + r.2 ≤ D.classical N + D.conditionalCoherent N}

/-- Positive-block regularization, with multiplication avoiding division at k=0, pp.7–8,30. -/
def regularized (F : (n : ℕ) → Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {r | ∃ n : ℕ, 0 < n ∧ ((n : ℝ) * r.1, (n : ℝ) * r.2) ∈ F n}

/-- CQ generation code, pp.5–6, (1)–(2): separate pure preparations and joint decoder.
A final dephasing in `cqDecoded` makes the classical output an instrument. -/
structure CQGeneration (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (n m k : ℕ) where
  alice : Fin m → EuclideanSpace ℂ (Fin n → A)
  aliceUnit : ∀ s, IsState (alice s)
  bob : EuclideanSpace ℂ (Fin k × (Fin n → B))
  bobUnit : IsState bob
  decoder : Superop (Fin n → C) (Fin m × Fin k)
  decoderChannel : IsChannel decoder

/-- Apply the one n-use joint channel and decoder while leaving Bob's reference untouched,
then read the classical decoder output, pp.5–7. -/
def cqDecoded {n m k : ℕ} (N : Superop (A × B) C)
    (D : Superop (Fin n → C) (Fin m × Fin k))
    (rho : Op (Fin n → A)) (tau : Op (R × (Fin n → B))) :
    Op (R × (Fin m × Fin k)) :=
  dephaseClassicalRegister (idTensorSuperop D (idTensorSuperop (macPower N n) (cqInput rho tau)))

/-- Uniform-message average of a JOINT classical/Bell fidelity, (1)–(2), p.6. -/
def CQGeneration.Good {n m k : ℕ} (K : CQGeneration A B C n m k)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  1 - epsilon ≤ (m : ℝ)⁻¹ * ∑ s, squaredFidelity (cqMessageTarget s (epr k))
    (cqDecoded N K.decoder (pureDensity (K.alice s)) (pureDensity K.bob))

/-- CQ entanglement transmission, pp.6–7: local CPTP encoder on a Bell half only. -/
structure CQTransmission (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (n m k : ℕ) where
  alice : Fin m → EuclideanSpace ℂ (Fin n → A)
  aliceUnit : ∀ s, IsState (alice s)
  encoder : Superop (Fin k) (Fin n → B)
  encoderChannel : IsChannel encoder
  decoder : Superop (Fin n → C) (Fin m × Fin k)
  decoderChannel : IsChannel decoder

/-- Transmission success (3)–(4), pp.6–7; reference is never acted on by the encoder. -/
def CQTransmission.Good {n m k : ℕ} (K : CQTransmission A B C n m k)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  1 - epsilon ≤ (m : ℝ)⁻¹ * ∑ s, squaredFidelity (cqMessageTarget s (epr k))
    (cqDecoded N K.decoder (pureDensity (K.alice s)) (idTensorSuperop K.encoder (epr k)))

/-- CQ strong transmission, p.23: local stochastic classical preparations, one fixed
quantum encoder and one fixed joint decoder. Mixed message states represent finite
private random pure preparations after discarding Alice's private seed. No seed is
available to Charlie except through the charged n channel uses. -/
structure CQStrong (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (n m k : ℕ) where
  alice : Fin m → Op (Fin n → A)
  aliceDensity : ∀ s, IsDensityMatrix (alice s)
  encoder : Superop (Fin k) (Fin n → B)
  encoderChannel : IsChannel encoder
  decoder : Superop (Fin n → C) (Fin m × Fin k)
  decoderChannel : IsChannel decoder

/-- Maximal JOINT error for every classical message and every reference/input pure state,
(36), p.23. Correction: test the ORIGINAL message, as the inverse cyclic relabeling
on p.25 does. The printed arbitrary f(m) target would permit a constant f. -/
def CQStrong.Good {n m k : ℕ} (K : CQStrong A B C n m k)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  ∀ s, ∀ t : ℕ, 0 < t → ∀ psi : EuclideanSpace ℂ (Fin t × Fin k), IsState psi →
    1 - epsilon ≤ squaredFidelity (cqMessageTarget s (pureDensity psi))
      (cqDecoded N K.decoder (K.alice s) (idTensorSuperop K.encoder (pureDensity psi)))

/-- QQ generation code, p.7, (5); the sender preparations are independent. -/
structure QQGeneration (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (n a b : ℕ) where
  alice : EuclideanSpace ℂ (Fin a × (Fin n → A))
  aliceUnit : IsState alice
  bob : EuclideanSpace ℂ (Fin b × (Fin n → B))
  bobUnit : IsState bob
  decoder : Superop (Fin n → C) (Fin a × Fin b)
  decoderChannel : IsChannel decoder

/-- One fidelity against the PRODUCT Bell target, (5), p.7. -/
def QQGeneration.Good {n a b : ℕ} (K : QQGeneration A B C n a b)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  1 - epsilon ≤ squaredFidelity (bellPair a b)
    (idTensorSuperop K.decoder (idTensorSuperop (macPower N n)
      (independentPairs (pureDensity K.alice) (pureDensity K.bob))))

/-- QQ transmission code, (6), p.7; two individually local CPTP encoders,
no reference access or pre-shared sender/decoder resources. -/
structure QQTransmission (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (n a b : ℕ) where
  alice : Superop (Fin a) (Fin n → A)
  aliceChannel : IsChannel alice
  bob : Superop (Fin b) (Fin n → B)
  bobChannel : IsChannel bob
  decoder : Superop (Fin n → C) (Fin a × Fin b)
  decoderChannel : IsChannel decoder

/-- Encoders act only on the two input halves; channel and decoder act jointly, p.7. -/
def QQTransmission.decoded {n a b : ℕ} (K : QQTransmission A B C n a b)
    (N : Superop (A × B) C) (rho : Op (R × Fin a)) (tau : Op (S × Fin b)) :
    Op ((R × S) × (Fin a × Fin b)) :=
  idTensorSuperop K.decoder (idTensorSuperop (macPower N n)
    (independentPairs (idTensorSuperop K.alice rho) (idTensorSuperop K.bob tau)))

/-- One simultaneous fidelity, not separate marginal fidelities, (6), p.7. -/
def QQTransmission.Good {n a b : ℕ} (K : QQTransmission A B C n a b)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  1 - epsilon ≤ squaredFidelity (bellPair a b) (K.decoded N (epr a) (epr b))

/-- Strong qq transmission, (37), pp.23–24: all independent external references,
allowing arbitrary entanglement WITHIN each pair, and one product-target fidelity. -/
def QQTransmission.Strong {n a b : ℕ} (K : QQTransmission A B C n a b)
    (N : Superop (A × B) C) (epsilon : ℝ) : Prop :=
  ∀ q t : ℕ, 0 < q → 0 < t →
    ∀ psi : EuclideanSpace ℂ (Fin q × Fin a), IsState psi →
    ∀ phi : EuclideanSpace ℂ (Fin t × Fin b), IsState phi →
      1 - epsilon ≤ squaredFidelity (independentPairs (pureDensity psi) (pureDensity phi))
        (K.decoded N (pureDensity psi) (pureDensity phi))

/-- Closed region from actual integer-rank codes with vanishing error and arbitrary
asymptotic rate slack, pp.6–7. Positive n,m,k guard all logs, divisions, and targets.
The code predicate contains its existential code BEFORE its universal input tests. -/
def operationalRegion (good : ℕ → ℕ → ℕ → ℝ → Prop) : Set (ℝ × ℝ) :=
  closure {r | Nonnegative r ∧ ∀ epsilon delta : ℝ, 0 < epsilon → 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      r.1 - delta ≤ Real.logb 2 a / n ∧ r.2 - delta ≤ Real.logb 2 b / n ∧
      good n a b epsilon}

/-- The three operational tasks, pp.5–7,23–24. -/
inductive MACScenario where
  | generation
  | transmission
  | strong

/-- Closed operational CQ region for the chosen task, pp.5–7,23. -/
def cqMacCapacity (N : Superop (A × B) C) (scenario : MACScenario := .generation) : Set (ℝ × ℝ) :=
  operationalRegion fun n m k epsilon => match scenario with
    | .generation => ∃ K : CQGeneration A B C n m k, K.Good N epsilon
    | .transmission => ∃ K : CQTransmission A B C n m k, K.Good N epsilon
    | .strong => ∃ K : CQStrong A B C n m k, K.Good N epsilon

/-- Closed operational Q region for the chosen task, pp.5–7,23–24. -/
def qqMacCapacity (N : Superop (A × B) C) (scenario : MACScenario := .generation) : Set (ℝ × ℝ) :=
  operationalRegion fun n a b epsilon => match scenario with
    | .generation => ∃ K : QQGeneration A B C n a b, K.Good N epsilon
    | .transmission => ∃ K : QQTransmission A B C n a b, K.Good N epsilon
    | .strong => ∃ K : QQTransmission A B C n a b, K.Strong N epsilon

/-- Optimized sum information over exactly product purifications (8), p.30.
For finite positive physical dimensions and CPTP N, this set is nonempty and
bounded; reference compression bounds their dimensions and gives attainment. -/
def optimizedSum (N : Superop (A × B) C) : ℝ :=
  sSup {z | ∃ D : QQData A B, z = D.sumCoherent N}

/-- Corrected controlled-erasure channel of §7.1, PDF p.32.
Printed N0=sum_j |flag><0,j| and Ni=|i><1,i| are NOT TP and dephase Bob.
The prose and N(tau tensor rho)=tau00|flag><flag|+tau11 rho instead specify
K_j=|flag><0,j| and ONE L=sum_j |j><1,j|. This entry formula implements those
Kraus operators, retaining transfer-sector coherences. -/
def controlledErasure (d : ℕ) : Superop (Bool × Fin d) (Option (Fin d)) :=
  fun rho i j => match i, j with
    | none, none => ∑ a, rho (false,a) (false,a)
    | some a, some b => rho (true,a) (true,b)
    | _, _ => 0

/-- Collective phase flip Z tensor Z, §7.2, PDF p.34. -/
def collectivePhaseOperator : Op (Bool × Bool) :=
  Matrix.diagonal fun z => (if z.1 then (-1 : ℂ) else 1) * (if z.2 then (-1 : ℂ) else 1)

/-- The convex mixture (1-p)rho+p(Z tensor Z)rho(Z tensor Z), p.34. -/
def collectivePhase (p : ℝ) : Superop (Bool × Bool) (Bool × Bool) :=
  fun rho => ((1 - p : ℝ) : ℂ) • rho + (p : ℂ) • (collectivePhaseOperator * rho * collectivePhaseOperator)

/-- Channel coherent information using the SAME isometric extension for both
outputs, §7.3, PDF p.35. For density rho this equals the purification definition. -/
def inputCoherent (U : Matrix (B × E) A ℂ) (rho : Op A) : ℝ :=
  vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho)

/-- Sanity checks for the local definitions: scalar Bell normalization, independent
references, classical labels, and erasure coherences. All proofs are complete. -/
example : epr 1 (0,0) (0,0) = 1 := by simp [epr]

example (a b : ℕ) (i j : (Fin a × Fin b) × (Fin a × Fin b)) :
    bellPair a b i j = epr a (i.1.1,i.2.1) (j.1.1,j.2.1) *
      epr b (i.1.2,i.2.2) (j.1.2,j.2.2) := rfl

example (rho : Op (R × A)) (tau : Op (S × B))
    (r rr : R) (s ss : S) (a aa : A) (b bb : B) :
    independentPairs rho tau ((r,s),(a,b)) ((rr,ss),(aa,bb)) =
      rho (r,a) (rr,aa) * tau (s,b) (ss,bb) := rfl

example {m : ℕ} (s : Fin m) (rho : Op (R × I)) (r t : R) (i j : I) :
    cqMessageTarget s rho (r,(s,i)) (t,(s,j)) = rho (r,i) (t,j) := by simp [cqMessageTarget]

example (d : ℕ) (rho : Op (Bool × Fin d)) (a b : Fin d) :
    controlledErasure d rho (some a) (some b) = rho (true,a) (true,b) := rfl

example (d : ℕ) (rho : Op (Bool × Fin d)) :
    controlledErasure d rho none none = ∑ a, rho (false,a) (false,a) := rfl

example (rho : Op (Bool × Bool)) : collectivePhase 0 rho = rho := by
  simp [collectivePhase]

example : collectivePhaseOperator (false,true) (false,true) = -1 := by
  simp [collectivePhaseOperator]

example : collectivePhaseOperator (true,true) (true,true) = 1 := by
  simp [collectivePhaseOperator]

example (D : CQMacData A B) (N : Superop (A × B) C) :
    D.conditionalCoherent N = ∑ x, D.ensemble.weight x *
      (vnEntropy (traceLeft (D.output N x)) - vnEntropy (D.output N x)) := rfl

example (D : QQData A B) (N : Superop (A × B) C) :
    D.sumCoherent N = vnEntropy (traceLeft (D.output N)) - vnEntropy (D.output N) := rfl

example (F : (n : ℕ) → Set (ℝ × ℝ)) (r : ℝ × ℝ)
    (h : r ∈ regularized F) : ∃ n : ℕ, 0 < n ∧
      ((n : ℝ) * r.1, (n : ℝ) * r.2) ∈ F n := h

end QAlgorithms.Papers.Independent.Support50.P02


