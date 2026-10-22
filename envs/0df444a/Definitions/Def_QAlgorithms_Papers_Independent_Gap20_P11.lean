-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11
-- name    : QAlgorithms_Papers_Independent_Gap20_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T23:28:34.709627+00:00
-- url     : https://prove2.me/theorems/8f59210c-a685-4ac0-a196-9b0d6be4edb0
-- title:
--   Definitions for Quantum information can be negative
-- statement:
--   The objects the formalized statements of *Quantum information can be negative* (arXiv:quant-ph/0505062) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `classicalCost`: PDF pp.3–4: I(A:R) for any purification, computed from rho_AB alone.
--   - `marginalAR`: PDF p.4: the actual AR marginal, keeping off-diagonal reference blocks.
--   - `referenceInformation`: PDF p.4: the mutual information of Alice and the inaccessible reference.
--   - `finTransport`: PDF pp.2–3: basis transport of a physical two-party map, with no identification of Alice's and Bob's registers or of their operations.
--   - `IsLOCC`: PDF pp.2–3: an actual finite adaptive LOCC map, in the physical bases. There is no joint quantum gate or free entanglement constructor.
--   - `mergingInput`: PDF p.3: n source copies and k independently supplied Bell pairs. The order is R,(Alice source,Alice Bell),(Bob source,Bob Bell).
--   - `mergingTarget`: PDF p.3: the entire ideal output. Alice holds only her final Bell halves; Bob holds both source shares and his final Bell halves.
--   - `MergingReconstructs`: PDF pp.2–3: full reconstruction, uniformly over purifications of rho_AB. The fixed canonical reference dimension avoids any choice of a hidden realization. Trace-norm error tending to zero is equivalent to the source's fidelity tending to one, for these normalized inputs and the normalized pure target.
--   - `MergingCode`: PDF pp.2–3: a general adaptive LOCC merging code with separate integer input/output entanglement resources. Validity is a property of its physical map.
--   - `MergingAchievable`: PDF p.2: asymptotic signed ebit consumption per source copy. A quantum channel can distribute each consumed Bell pair; teleportation implements the opposite conversion using the permitted classical communication. No finite block count is equated to a generally irrational entropy.
--   - `productApply`: PDF pp.3–4: tensor action defined on every matrix unit, so it retains all coherences and entanglement with arbitrary external registers.
--   - `MergingOneWayCode`: PDF pp.3–4: Alice's actual instrument and Bob's outcome-conditioned channel. The private Kraus index is not communicated; only the finite outcome is sent. Bob receives no quantum message.
--   - `MergingOneWayCode.operation`: PDF pp.3–4: sum over the communicated classical outcome; the private Kraus environment is traced out. This is the map of the stated LOCC protocol.
--   - `MergingConstruction`: PDF pp.2–4: construction with a simultaneous signed ebit rate and cbit rate. For negative conditional entropy it supplies no initial EPR pairs at all. For positive cost it consumes at most n(e+delta) pairs, which can be distributed using that many qubits. The joint error includes the retained final EPR pairs.
--   - `unknownQubit`: PDF pp.3–4, example 1: maximally mixed Alice qubit, trivial Bob register.
--   - `DirectCode`: PDF pp.3–4, example 1: an actual single forward quantum register. Its dimension is 2^q; it is transmitted between the two local maps.
--   - `directQubit`: PDF pp.3–4: the direct one-qubit transmission alternative.
--   - `teleportRow`: PDF p.4: Bell measurement bra indexed by bit flip x and phase flip z. Each branch includes Alice's input and her half of one supplied EPR pair.
--   - `teleportCorrection`: PDF p.4: correction Z^z X^x conditional on the two classical bits.
--   - `teleportOperation`: PDF p.4: teleportation uses only a Bell measurement and a conditional local correction after one Bell pair has been supplied.
--   - `teleportReferenceInput`: PDF pp.3–4: attach the charged Bell resource, retaining every reference block.
--   - `correlatedPurification`: PDF p.4, example 2: canonical coherent purification, in R,A,B order.
--   - `plusMinusRow`: PDF p.4: normalized plus/minus measurement bra, with true denoting minus.
--   - `correlatedDecoder`: PDF p.4: conditional isometry at Bob, |b> ↦ (-1)^(s b)|bb>. The first output is the new local A-prime ancilla; no operation acts on R.
--   - `correlatedOperation`: PDF p.4: Alice measures, sends one cbit, and Bob coherently copies and corrects. There is no quantum message and no supplied entanglement.
--   - `correlatedTarget`: PDF p.4: target includes the reference and the reconstructed coherent source.
--   - `bobPreparesBell`: PDF p.4, example 3: Bob prepares the known pure source Bell pair locally, retaining his original EPR half as the last output register.
--   - `bellMergingOperation`: PDF p.4: keep the old shared resource and prepare the source at Bob. Output ownership is Alice old-half, then (Bob's new source, Bob old-half).
--   - `bellMergingTarget`: PDF p.4: one shared Bell pair and, independently, the reconstructed source Bell pair entirely at Bob; this is not cloning an unknown state.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, https://arxiv.org/abs/quant-ph/0505062v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Horodecki, Oppenheim and Winter, Quantum information can be negative,
arXiv:quant-ph/0505062v1, PDF pp.1–7.

All registers are finite and nonzero at the theorem boundary. Entropies are
in bits. A block code acts on physical registers only, leaving R untouched.
The rate predicates quantify a code BEFORE every purification of the same
source density operator. The fixed reference A × B is large enough to purify
any density on A × B; invariance under reference isometries gives the usual
arbitrary-reference criterion. Errors include the entire final Bell resource.

The accepted FiniteLOCC predicate is reused with explicit basis transport.
It includes arbitrary finite numbers of adaptive rounds, not only one-way
codes. Ancillas and disposal are rectangular local Kraus operations. In the
vanishing-error operational rate, limits of protocols add no rates: approximate
or truncate each block protocol before assigning its error budget.

The independent-paper override permits importing reviewed accepted modules.
No result from the imported paper is used as a hypothesis or as this paper's
merging theorem; only its complete FiniteLOCC definition is used.
Copies, conditionalEntropy and the Bool specialization of the general Bell
vector are imported from the pinned accepted library rather than redeclared.
The sampling predicate Renew46.P05.Reconstructs, the general resource-port
Renew46.P34.OneWayCode and the unreferenced Information100.P21.teleportInput
have different types and tasks. The distinct local merging/reference concepts
use explicit names; ASSESSMENT.json records each comparison and decision.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3–4: I(A:R) for any purification, computed from rho_AB alone. -/
def classicalCost {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight rho) + conditionalEntropy rho

/-- PDF p.4: the actual AR marginal, keeping off-diagonal reference blocks. -/
def marginalAR {A B R : Type} [Fintype B]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ) :
    Matrix (A × R) (A × R) ℂ :=
  fun p q => ∑ b, rho (p.2, (p.1, b)) (q.2, (q.1, b))

/-- PDF p.4: the mutual information of Alice and the inaccessible reference. -/
def referenceInformation {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  vnEntropy (traceRight (traceLeft (pureDensity psi))) +
    vnEntropy (traceRight (pureDensity psi)) - vnEntropy (marginalAR (pureDensity psi))

/-- PDF pp.2–3: basis transport of a physical two-party map, with no
identification of Alice's and Bob's registers or of their operations. -/
def finTransport {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (Phi : Superop (A × B) (C × D)) :
    Superop (Fin (Fintype.card A) × Fin (Fintype.card B))
      (Fin (Fintype.card C) × Fin (Fintype.card D)) :=
  let a := Fintype.equivFin A
  let b := Fintype.equivFin B
  let c := Fintype.equivFin C
  let d := Fintype.equivFin D
  fun X p q => Phi (fun i j => X (a i.1, b i.2) (a j.1, b j.2))
    (c.symm p.1, d.symm p.2) (c.symm q.1, d.symm q.2)

/-- PDF pp.2–3: an actual finite adaptive LOCC map, in the physical bases.
There is no joint quantum gate or free entanglement constructor. -/
def IsLOCC {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (Phi : Superop (A × B) (C × D)) : Prop :=
  QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC (finTransport Phi)

/-- PDF p.3: n source copies and k independently supplied Bell pairs.
The order is R,(Alice source,Alice Bell),(Bob source,Bob Bell). -/
def mergingInput {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B)))
    (n k : ℕ) :
    EuclideanSpace ℂ (Copies R n × ((Copies A n × Qubits k) × (Copies B n × Qubits k))) :=
  WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.1.1 i, p.2.2.1 i))) *
      maxEntangled k (p.2.1.2, p.2.2.2)

/-- PDF p.3: the entire ideal output. Alice holds only her final Bell halves;
Bob holds both source shares and his final Bell halves. -/
def mergingTarget {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B)))
    (n l : ℕ) :
    EuclideanSpace ℂ (Copies R n × (Qubits l × ((Copies A n × Copies B n) × Qubits l))) :=
  WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.2.1.1 i, p.2.2.1.2 i))) *
      maxEntangled l (p.2.1, p.2.2.2)

/-- PDF pp.2–3: full reconstruction, uniformly over purifications of rho_AB.
The fixed canonical reference dimension avoids any choice of a hidden realization.
Trace-norm error tending to zero is equivalent to the source's fidelity tending
to one, for these normalized inputs and the normalized pure target. -/
def MergingReconstructs {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (n k l : ℕ)
    (Phi : Superop ((Copies A n × Qubits k) × (Copies B n × Qubits k))
      (Qubits l × ((Copies A n × Copies B n) × Qubits l))) (eps : ℝ) : Prop :=
  ∀ psi : EuclideanSpace ℂ ((A × B) × (A × B)),
    IsState psi → traceLeft (pureDensity psi) = rho →
      traceNorm (idTensorSuperop Phi (pureDensity (mergingInput psi n k)) -
        pureDensity (mergingTarget psi n l)) ≤ eps

/-- PDF pp.2–3: a general adaptive LOCC merging code with separate integer
input/output entanglement resources. Validity is a property of its physical map. -/
structure MergingCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  k : ℕ
  l : ℕ
  operation : Superop ((Copies A n × Qubits k) × (Copies B n × Qubits k))
    (Qubits l × ((Copies A n × Copies B n) × Qubits l))
  locc : IsLOCC operation

/-- PDF p.2: asymptotic signed ebit consumption per source copy. A quantum
channel can distribute each consumed Bell pair; teleportation implements the
opposite conversion using the permitted classical communication. No finite
block count is equated to a generally irrational entropy. -/
def MergingAchievable {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (rate : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    ∃ P : MergingCode A B n,
      MergingReconstructs rho n P.k P.l P.operation eps ∧
        (P.k : ℝ) - (P.l : ℝ) ≤ (n : ℝ) * (rate + delta)

/-- PDF pp.3–4: tensor action defined on every matrix unit, so it retains all
coherences and entanglement with arbitrary external registers. -/
def productApply {A B C D : Type} [Fintype A] [Fintype B]
    (Phi : Superop A C) (Psi : Superop B D) : Superop (A × B) (C × D) :=
  fun X p q => ∑ a, ∑ a2, ∑ b, ∑ b2,
    X (a, b) (a2, b2) * Phi (Matrix.single a a2 1) p.1 q.1 *
      Psi (Matrix.single b b2 1) p.2 q.2

/-- PDF pp.3–4: Alice's actual instrument and Bob's outcome-conditioned
channel. The private Kraus index is not communicated; only the finite outcome
is sent. Bob receives no quantum message. -/
structure MergingOneWayCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  k : ℕ
  l : ℕ
  outcomes : ℕ
  outcomes_pos : 0 < outcomes
  environment : ℕ
  alice : (Fin outcomes × Fin environment) →
    Matrix (Qubits l) (Copies A n × Qubits k) ℂ
  complete : IsKrausFamily alice
  bob : Fin outcomes → Superop (Copies B n × Qubits k)
    ((Copies A n × Copies B n) × Qubits l)
  bob_channel : ∀ s, IsChannel (bob s)

/-- PDF pp.3–4: sum over the communicated classical outcome; the private
Kraus environment is traced out. This is the map of the stated LOCC protocol. -/
def MergingOneWayCode.operation {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : MergingOneWayCode A B n) :
    Superop ((Copies A n × Qubits P.k) × (Copies B n × Qubits P.k))
      (Qubits P.l × ((Copies A n × Copies B n) × Qubits P.l)) :=
  fun X => ∑ s, productApply (krausApply (fun e => P.alice (s, e))) (P.bob s) X

/-- PDF pp.2–4: construction with a simultaneous signed ebit rate and cbit
rate. For negative conditional entropy it supplies no initial EPR pairs at all.
For positive cost it consumes at most n(e+delta) pairs, which can be distributed
using that many qubits. The joint error includes the retained final EPR pairs. -/
def MergingConstruction {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (c e : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    ∃ P : MergingOneWayCode A B n,
      MergingReconstructs rho n P.k P.l P.operation eps ∧
      Real.logb 2 (P.outcomes : ℝ) ≤ (n : ℝ) * (c + delta) ∧
      (P.k : ℝ) - (P.l : ℝ) ≤ (n : ℝ) * (e + delta) ∧
      (P.k : ℝ) ≤ (n : ℝ) * (max e 0 + delta) ∧
      (n : ℝ) * (max (-e) 0 - delta) ≤ (P.l : ℝ) ∧
      (e < 0 → P.k = 0)

/-- Sanity: signed consumption uses real subtraction, including the negative regime. -/
example : (0 : ℝ) - (1 : ℝ) = -1 := by norm_num

/-- Sanity: zero-copy amplitudes and the zero-ebit resource are one, not an empty state. -/
example {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B)))
    (p : Copies R 0 × ((Copies A 0 × Qubits 0) × (Copies B 0 × Qubits 0))) :
    mergingInput psi 0 0 p = 1 := by
  have h : p.2.1.2 = p.2.2.2 := by
    funext i
    exact Fin.elim0 i
  simp [mergingInput, tensorPow, maxEntangled, h]

/-- Sanity: the imported general Bell vector specializes to the source qubit amplitude. -/
example : QAlgorithms.Papers.Independent.Information100.P22.bell Bool (false, false) =
    ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [QAlgorithms.Papers.Independent.Information100.P22.bell]

/-- PDF pp.3–4, example 1: maximally mixed Alice qubit, trivial Bob register. -/
def unknownQubit : Matrix (Bool × Unit) (Bool × Unit) ℂ :=
  fun p q => if p.1 = q.1 then (1 / 2 : ℂ) else 0

/-- PDF pp.3–4, example 1: an actual single forward quantum register.
Its dimension is 2^q; it is transmitted between the two local maps. -/
structure DirectCode where
  q : ℕ
  encode : Superop Bool (Qubits q)
  decode : Superop (Qubits q) Bool

/-- PDF pp.3–4: the direct one-qubit transmission alternative. -/
def directQubit : DirectCode where
  q := 1
  encode := fun X p q => X (p 0) (q 0)
  decode := fun X p q => X (fun _ => p) (fun _ => q)

/-- PDF p.4: Bell measurement bra indexed by bit flip x and phase flip z.
Each branch includes Alice's input and her half of one supplied EPR pair. -/
def teleportRow (s : Bool × Bool) : Matrix Unit (Bool × Bool) ℂ :=
  fun _ p => if p.2 = (p.1 != s.1) then
    ((Real.sqrt 2)⁻¹ : ℂ) * (if s.2 && p.1 then -1 else 1) else 0

/-- PDF p.4: correction Z^z X^x conditional on the two classical bits. -/
def teleportCorrection (s : Bool × Bool) : Matrix Bool Bool ℂ :=
  fun a b => if b = (a != s.1) then (if s.2 && a then -1 else 1) else 0

/-- PDF p.4: teleportation uses only a Bell measurement and a conditional
local correction after one Bell pair has been supplied. -/
def teleportOperation : Superop ((Bool × Bool) × Bool) (Unit × Bool) :=
  fun X => ∑ s : Bool × Bool,
    productApply (conjSuperop (teleportRow s))
      (conjSuperop (teleportCorrection s)) X

/-- PDF pp.3–4: attach the charged Bell resource, retaining every reference block. -/
def teleportReferenceInput {R : Type} (X : Matrix (R × Bool) (R × Bool) ℂ) :
    Matrix (R × ((Bool × Bool) × Bool)) (R × ((Bool × Bool) × Bool)) ℂ :=
  fun p q => X (p.1, p.2.1.1) (q.1, q.2.1.1) *
    pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) (p.2.1.2, p.2.2) (q.2.1.2, q.2.2)

/-- Sanity: the direct register really has one qubit. -/
example : directQubit.q = 1 := rfl

/-- PDF p.4, example 2: canonical coherent purification, in R,A,B order. -/
def correlatedPurification : EuclideanSpace ℂ (Bool × (Bool × Bool)) :=
  WithLp.toLp 2 fun p => if p.1 = p.2.1 ∧ p.2.1 = p.2.2
    then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.4: normalized plus/minus measurement bra, with true denoting minus. -/
def plusMinusRow (minus : Bool) : Matrix Unit Bool ℂ :=
  fun _ a => ((Real.sqrt 2)⁻¹ : ℂ) * (if minus && a then -1 else 1)

/-- PDF p.4: conditional isometry at Bob, |b> ↦ (-1)^(s b)|bb>.
The first output is the new local A-prime ancilla; no operation acts on R. -/
def correlatedDecoder (minus : Bool) : Matrix (Bool × Bool) Bool ℂ :=
  fun p b => if p = (b, b) then (if minus && b then -1 else 1) else 0

/-- PDF p.4: Alice measures, sends one cbit, and Bob coherently copies and
corrects. There is no quantum message and no supplied entanglement. -/
def correlatedOperation : Superop (Bool × Bool) (Unit × (Bool × Bool)) :=
  fun X => ∑ s : Bool, productApply (conjSuperop (plusMinusRow s))
    (conjSuperop (correlatedDecoder s)) X

/-- PDF p.4: target includes the reference and the reconstructed coherent source. -/
def correlatedTarget : EuclideanSpace ℂ (Bool × (Unit × (Bool × Bool))) :=
  WithLp.toLp 2 fun p => correlatedPurification (p.1, p.2.2)

/-- Sanity: the minus outcome has a negative amplitude on |1>, with unit normalization. -/
example : plusMinusRow true () true = -((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [plusMinusRow]

/-- PDF p.4, example 3: Bob prepares the known pure source Bell pair locally,
retaining his original EPR half as the last output register. -/
def bobPreparesBell : Superop Bool ((Bool × Bool) × Bool) :=
  fun X p q => pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) p.1 q.1 * X p.2 q.2

/-- PDF p.4: keep the old shared resource and prepare the source at Bob.
Output ownership is Alice old-half, then (Bob's new source, Bob old-half). -/
def bellMergingOperation : Superop (Bool × Bool) (Bool × ((Bool × Bool) × Bool)) :=
  productApply (fun X : Matrix Bool Bool ℂ => X) bobPreparesBell

/-- PDF p.4: one shared Bell pair and, independently, the reconstructed
source Bell pair entirely at Bob; this is not cloning an unknown state. -/
def bellMergingTarget : Matrix (Bool × ((Bool × Bool) × Bool))
    (Bool × ((Bool × Bool) × Bool)) ℂ :=
  fun p q => pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) (p.1, p.2.2) (q.1, q.2.2) *
    pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) p.2.1 q.2.1

/-- Sanity: Bob's preparation is independent of the old half's matrix entry. -/
example (X : Matrix Bool Bool ℂ) (s t : Bool × Bool) (b c : Bool) :
    bobPreparesBell X (s, b) (t, c) = pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) s t * X b c := rfl

end QAlgorithms.Papers.Independent.Gap20.P11


