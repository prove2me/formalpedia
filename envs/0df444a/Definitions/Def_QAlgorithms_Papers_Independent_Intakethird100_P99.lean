-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P99
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:46:26.220587+00:00
-- url     : https://prove2.me/theorems/6fbe02d0-4cc8-4ab6-bb08-f9bed44ec9e4
-- title:
--   Definitions for Characterization of non-local gates
-- statement:
--   The objects the formalized statements of *Characterization of non-local gates* (arXiv:quant-ph/0205100) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OneMatrix`: PDF p.2: operators on one qubit.
--   - `TwoMatrix`: PDF p.2: operators on the ordered tensor product A then B.
--   - `OneGate`: PDF pp.1–2: a bundled arbitrary one-qubit unitary control.
--   - `Triple`: PDF p.3: three real interaction coefficients, indexed from zero in Lean.
--   - `OneState`: PDF pp.8–9: one-qubit pure-state vectors; IsState supplies normalization.
--   - `IsGate`: PDF p.2, II.A: a two-qubit gate is unitary.
--   - `localMatrix`: PDF pp.1–2: instantaneous independent local gates on A and B.
--   - `TwoQubitLocalEquivalent`: PDF p.2, II.A: local equivalence; U(2) factors also absorb the global phase.
--   - `canonicalPauliInteraction`: PDF p.3, (3): the canonical interaction Hamiltonian, with no strength bound.
--   - `contentGate`: PDF pp.2–3: U_beta = exp(-i H_beta).
--   - `SOrdered`: PDF p.3, II.B: s-ordered coefficients (not ordinary decreasing order).
--   - `GateChamber`: PDF p.2, (1): the gate chamber, as distinguished from Hamiltonian strength.
--   - `sOrder`: PDF p.3, II.B: sort absolute values and give the least one the product's sign. If the product vanishes the least absolute value is zero, so the sign choice is harmless.
--   - `SMajorized`: PDF p.3, (5): b is s-majorized by a; both sides are s-ordered first.
--   - `contentIntegerShift`: PDF pp.4–6, (7): periodic shift by integer multiples of pi/2.
--   - `secondShift`: PDF p.6, Result 2: the only nonzero shift needed for the minimum.
--   - `HasContent`: PDF pp.2–3: an actual canonical-content witness for the given unitary.
--   - `HasCanonicalHamiltonian`: PDF p.4, III.A: the nonlocal part of H has canonical coefficients a after local conjugation. K and L include arbitrary local terms and the scalar identity term.
--   - `PureInteraction`: PDF p.6, III.C: a pure interaction has no scalar or one-body terms.
--   - `PulseProtocol`: PDF p.4, (6): initial local gates followed by evolution/local-control pairs. Nonnegative times are built into the type; the pulse list counts actual H applications.
--   - `protocolTime`: PDF p.4: only interaction intervals contribute to total duration.
--   - `protocolMatrix`: PDF p.4, (6): the earliest step acts on the right. This is an operator on every input, not a protocol chosen after seeing an input state.
--   - `SamePhysicalGate`: PDF pp.1–2: equality of physical gates disregards one scalar phase.
--   - `IdealSimulates`: PDF p.4: ideal fast-LU simulation, explicitly including the limit of arbitrarily fine pulses needed to eliminate local drift. Every approximant has exactly duration t. An operator-norm approximation is uniform over all input states.
--   - `interactionCost`: PDF pp.4,6: interaction cost as an extended nonnegative infimum, including impossible simulations with value infinity. Attainment is asserted in the result, not assumed here.
--   - `branchCost`: PDF p.6: cost of one unshifted s-majorization branch.
--   - `MoreNonlocal`: PDF pp.7–8, III.E: order by interaction cost for every Hermitian H, including zero interaction. This is a preorder on matrices; no antisymmetry on raw gates is claimed.
--   - `dcnot`: PDF p.7, III.D.2: DCNOT sends |i,j> to |j,i xor j>.
--   - `reverseParties`: PDF p.7: interchange Alice and Bob; first register remains the sender in the predicates.
--   - `CanCbit`: PDF pp.8–10, (11): one perfect classical bit, with fixed orthogonal encoding and a fixed pure receiver input chosen before the bit. The sender's residual states may differ. All states are normalized; no ancillary or prior entangled state occurs in the definition.
--   - `CanTwoCbits`: PDF pp.10–11, (16)–(18): two simultaneous perfect classical bits. Each receiving measurement may depend on that receiver's own sent bit, through the two orthogonality conditions. Inputs are fixed independent orthogonal encodings, not shared entanglement.
--   - `CanQubit`: PDF pp.8,11: unknown-qubit transmission preserves every normalized superposition with one fixed encoding, pure receiver input, recovery, and residual sender state.
--   - `CanHybrid`: PDF pp.11–12: a qubit A→B and a cbit B→A in the same use. Bob's recovery depends on his sent bit j, but the same recovery works for every unknown superposition.
--   - `CanTwoQubits`: PDF p.12, IV.B.4: simultaneous exchange of arbitrary qubits with fixed free local encoding and decoding, uniformly over both unknown states.
--   - `taskCost`: PDF pp.9–12: minimize interaction cost over every gate capable of the task P. The empty set has infimum infinity in ENNReal.
--   - `OptimalTask`: PDF pp.10–12: an explicit attaining gate and time, together with the lower bound against every capable gate. Simulation is ideal fast control as on p.4.
--   - `optimalTransmissionContent`: PDF p.11, Result 5: the minimizing interaction content (not necessarily unique).
--   - `ControlPhase`: PDF p.13, Appendix A: determinant phase of the controlled one-qubit unitary is free on the control. b is an eigenphase half-angle, before folding into the gate chamber.
--   - `controlledContent`: PDF p.13, Appendix A: fold b at pi/4 rather than selecting a principal argument.
--   - `ChamberClass`: PDF p.12, IV.C: four disjoint chamber strata; both signed SWAP endpoints are included.
--   - `TransmissionProfile`: PDF p.12, IV.C: operational profiles, including both orientations. "No capability" means no perfect full bit in this single-use model, not zero Shannon capacity.
--   - `interactionPhases`: PDF p.3, (4): interaction eigenvalues in the exact magic-basis order (2).
--   - `magicBasis`: PDF p.3, (2): columns are -i(|01>+|10>)/sqrt2, (|00>+|11>)/sqrt2, -i(|00>-|11>)/sqrt2, (|01>-|10>)/sqrt2, respectively.
--   - `magicMatrix`: PDF p.13, Appendix A: express a computational-basis matrix in basis (2).
--   - `PhaseCompatibleContent`: PDF p.13: a phase-compatible SU(2) local decomposition of the actual representative. This excludes assuming that an arbitrary projective phase has the same magic spectrum.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, https://arxiv.org/abs/quant-ph/0205100v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

/-!
Statements from Hammerer, Vidal and Cirac, arXiv:quant-ph/0205100v3.
Paper-specific definitions are confined to this paper; the accepted Pauli selector and
matrix evolution are imported from the pinned library. Source indices 1,2,3 are Lean indices 0,1,2.
Registers and Pauli gates use the frozen library: Bool for one qubit, Bool × Bool for A then B.
Local U(2) factors include physically irrelevant scalar phases. Appendix A instead explicitly
requires determinant-one local factors for the chosen representative.

General-H simulation is the ideal fast-control limit of finite protocols of exactly the stated
interaction duration (p.4). The norm used to take that limit is the frozen spectral norm.
Finite exact protocols are distinguished from this limit. Costs lie in ENNReal; an empty feasible
set has cost infinity. No gate-chamber bound is imposed on Hamiltonian strength.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)
open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.2: operators on one qubit. -/
abbrev OneMatrix := Matrix Bool Bool ℂ

/-- PDF p.2: operators on the ordered tensor product A then B. -/
abbrev TwoMatrix := Matrix (Bool × Bool) (Bool × Bool) ℂ

/-- PDF pp.1–2: a bundled arbitrary one-qubit unitary control. -/
abbrev OneGate := Matrix.unitaryGroup Bool ℂ

/-- PDF p.3: three real interaction coefficients, indexed from zero in Lean. -/
abbrev Triple := Fin 3 → ℝ

/-- PDF pp.8–9: one-qubit pure-state vectors; IsState supplies normalization. -/
abbrev OneState := EuclideanSpace ℂ Bool

/-- PDF p.2, II.A: a two-qubit gate is unitary. -/
def IsGate (U : TwoMatrix) : Prop := U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ

/-- PDF pp.1–2: instantaneous independent local gates on A and B. -/
def localMatrix (A B : OneGate) : TwoMatrix :=
  (A : OneMatrix) ⊗ₖ (B : OneMatrix)

/-- PDF p.2, II.A: local equivalence; U(2) factors also absorb the global phase. -/
def TwoQubitLocalEquivalent (U V : TwoMatrix) : Prop :=
  ∃ A B C D : OneGate, U = localMatrix A B * V * localMatrix C D

/-- PDF p.3, (3): the canonical interaction Hamiltonian, with no strength bound. -/
def canonicalPauliInteraction (a : Triple) : TwoMatrix :=
  ∑ i : Fin 3, (a i : ℂ) • (pauli i ⊗ₖ pauli i)

/-- PDF pp.2–3: U_beta = exp(-i H_beta). -/
def contentGate (b : Triple) : TwoMatrix := evolution (canonicalPauliInteraction b) 1

/-- PDF p.3, II.B: s-ordered coefficients (not ordinary decreasing order). -/
def SOrdered (a : Triple) : Prop := a 1 ≤ a 0 ∧ |a 2| ≤ a 1

/-- PDF p.2, (1): the gate chamber, as distinguished from Hamiltonian strength. -/
def GateChamber (b : Triple) : Prop := SOrdered b ∧ b 0 ≤ Real.pi / 4

/-- PDF p.3, II.B: sort absolute values and give the least one the product's sign.
If the product vanishes the least absolute value is zero, so the sign choice is harmless. -/
def sOrder (a : Triple) : Triple :=
  let hi := max |a 0| (max |a 1| |a 2|)
  let lo := min |a 0| (min |a 1| |a 2|)
  ![hi, |a 0| + |a 1| + |a 2| - hi - lo,
    if a 0 * a 1 * a 2 < 0 then -lo else lo]

/-- PDF p.3, (5): b is s-majorized by a; both sides are s-ordered first. -/
def SMajorized (b a : Triple) : Prop :=
  let x := sOrder b
  let y := sOrder a
  x 0 ≤ y 0 ∧ x 0 + x 1 - x 2 ≤ y 0 + y 1 - y 2 ∧
    x 0 + x 1 + x 2 ≤ y 0 + y 1 + y 2

/-- PDF pp.4–6, (7): periodic shift by integer multiples of pi/2. -/
def contentIntegerShift (b : Triple) (n : Fin 3 → ℤ) : Triple :=
  fun i => b i + Real.pi / 2 * (n i : ℝ)

/-- PDF p.6, Result 2: the only nonzero shift needed for the minimum. -/
def secondShift (b : Triple) : Triple := contentIntegerShift b ![-1, 0, 0]

/-- PDF pp.2–3: an actual canonical-content witness for the given unitary. -/
def HasContent (U : TwoMatrix) (b : Triple) : Prop :=
  IsGate U ∧ GateChamber b ∧ TwoQubitLocalEquivalent U (contentGate b)

/-- PDF p.4, III.A: the nonlocal part of H has canonical coefficients a after local
conjugation. K and L include arbitrary local terms and the scalar identity term. -/
def HasCanonicalHamiltonian (H : TwoMatrix) (a : Triple) : Prop :=
  H.IsHermitian ∧ SOrdered a ∧
    ∃ A B : OneGate, ∃ K L : OneMatrix, K.IsHermitian ∧ L.IsHermitian ∧
      localMatrix A B * H * star (localMatrix A B) =
        canonicalPauliInteraction a + K ⊗ₖ (1 : OneMatrix) + (1 : OneMatrix) ⊗ₖ L

/-- PDF p.6, III.C: a pure interaction has no scalar or one-body terms. -/
def PureInteraction (H : TwoMatrix) : Prop :=
  ∃ c : Fin 3 → Fin 3 → ℝ,
    H = ∑ i : Fin 3, ∑ j : Fin 3, (c i j : ℂ) • (pauli i ⊗ₖ pauli j)

/-- PDF p.4, (6): initial local gates followed by evolution/local-control pairs.
Nonnegative times are built into the type; the pulse list counts actual H applications. -/
structure PulseProtocol where
  initialA : OneGate
  initialB : OneGate
  pulses : List (ℝ≥0 × (OneGate × OneGate))

/-- PDF p.4: only interaction intervals contribute to total duration. -/
def protocolTime (p : PulseProtocol) : ℝ≥0 := (p.pulses.map Prod.fst).sum

/-- PDF p.4, (6): the earliest step acts on the right. This is an operator on every input,
not a protocol chosen after seeing an input state. -/
def protocolMatrix (H : TwoMatrix) (p : PulseProtocol) : TwoMatrix :=
  p.pulses.foldl (fun U s => localMatrix s.2.1 s.2.2 * evolution H (s.1 : ℝ) * U)
    (localMatrix p.initialA p.initialB)

/-- PDF pp.1–2: equality of physical gates disregards one scalar phase. -/
def SamePhysicalGate (U V : TwoMatrix) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ U = z • V

/-- PDF p.4: ideal fast-LU simulation, explicitly including the limit of arbitrarily fine
pulses needed to eliminate local drift. Every approximant has exactly duration t.
An operator-norm approximation is uniform over all input states. -/
def IdealSimulates (H U : TwoMatrix) (t : ℝ) : Prop :=
  H.IsHermitian ∧ IsGate U ∧ 0 ≤ t ∧
    ∀ e : ℝ, 0 < e → ∃ p : PulseProtocol, (protocolTime p : ℝ) = t ∧
      ∃ z : ℂ, ‖z‖ = 1 ∧ specNorm (protocolMatrix H p - z • U) < e

/-- PDF pp.4,6: interaction cost as an extended nonnegative infimum, including impossible
simulations with value infinity. Attainment is asserted in the result, not assumed here. -/
def interactionCost (H U : TwoMatrix) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | IdealSimulates H U (t : ℝ)})

/-- PDF p.6: cost of one unshifted s-majorization branch. -/
def branchCost (a b : Triple) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | SMajorized b ((t : ℝ) • a)})

/-- PDF pp.7–8, III.E: order by interaction cost for every Hermitian H, including zero
interaction. This is a preorder on matrices; no antisymmetry on raw gates is claimed. -/
def MoreNonlocal (U V : TwoMatrix) : Prop :=
  ∀ H : TwoMatrix, H.IsHermitian → interactionCost H V ≤ interactionCost H U

/-- PDF p.7, III.D.2: DCNOT sends |i,j> to |j,i xor j>. -/
def dcnot : TwoMatrix :=
  Matrix.of fun p q => if p = (q.2, xor q.1 q.2) then 1 else 0

/-- PDF p.7: interchange Alice and Bob; first register remains the sender in the predicates. -/
def reverseParties (U : TwoMatrix) : TwoMatrix := swapGate * U * swapGate

/-- PDF pp.8–10, (11): one perfect classical bit, with fixed orthogonal encoding and a
fixed pure receiver input chosen before the bit. The sender's residual states may differ.
All states are normalized; no ancillary or prior entangled state occurs in the definition. -/
def CanCbit (U : TwoMatrix) : Prop :=
  IsGate U ∧ ∃ E D : OneGate, ∃ v : OneState, ∃ w : Bool → OneState,
    IsState v ∧ (∀ i, IsState (w i)) ∧
      ∀ i : Bool, act U (tensorVec (act (E : OneMatrix) (ket i)) v) =
        tensorVec (w i) (act (D : OneMatrix) (ket i))

/-- PDF pp.10–11, (16)–(18): two simultaneous perfect classical bits. Each receiving
measurement may depend on that receiver's own sent bit, through the two orthogonality
conditions. Inputs are fixed independent orthogonal encodings, not shared entanglement. -/
def CanTwoCbits (U : TwoMatrix) : Prop :=
  IsGate U ∧ ∃ E F : OneGate, ∃ a b : Bool → Bool → OneState,
    (∀ i j, IsState (a i j) ∧ IsState (b i j)) ∧
    (∀ i, inner ℂ (a i false) (a i true) = 0) ∧
    (∀ j, inner ℂ (b false j) (b true j) = 0) ∧
    ∀ i j : Bool, act U (tensorVec (act (E : OneMatrix) (ket i))
      (act (F : OneMatrix) (ket j))) = tensorVec (a i j) (b i j)

/-- PDF pp.8,11: unknown-qubit transmission preserves every normalized superposition
with one fixed encoding, pure receiver input, recovery, and residual sender state. -/
def CanQubit (U : TwoMatrix) : Prop :=
  IsGate U ∧ ∃ E R : OneGate, ∃ v w : OneState,
    IsState v ∧ IsState w ∧
    ∀ q : OneState, IsState q →
      act (((1 : OneMatrix) ⊗ₖ (R : OneMatrix)) * U)
        (tensorVec (act (E : OneMatrix) q) v) = tensorVec w q

/-- PDF pp.11–12: a qubit A→B and a cbit B→A in the same use. Bob's recovery depends
on his sent bit j, but the same recovery works for every unknown superposition. -/
def CanHybrid (U : TwoMatrix) : Prop :=
  IsGate U ∧ ∃ E F : OneGate, ∃ R : Bool → OneGate, ∃ a : Bool → OneState,
    (∀ j, IsState (a j)) ∧ inner ℂ (a false) (a true) = 0 ∧
    ∀ j : Bool, ∀ q : OneState, IsState q →
      act (((1 : OneMatrix) ⊗ₖ (R j : OneMatrix)) * U)
        (tensorVec (act (E : OneMatrix) q) (act (F : OneMatrix) (ket j))) =
          tensorVec (a j) q

/-- PDF p.12, IV.B.4: simultaneous exchange of arbitrary qubits with fixed free local
encoding and decoding, uniformly over both unknown states. -/
def CanTwoQubits (U : TwoMatrix) : Prop :=
  IsGate U ∧ ∃ E F R S : OneGate,
    ∀ q r : OneState, IsState q → IsState r →
      act (localMatrix R S * U)
        (tensorVec (act (E : OneMatrix) q) (act (F : OneMatrix) r)) = tensorVec r q

/-- PDF pp.9–12: minimize interaction cost over every gate capable of the task P.
The empty set has infimum infinity in ENNReal. -/
def taskCost (H : TwoMatrix) (P : TwoMatrix → Prop) : ℝ≥0∞ :=
  sInf (interactionCost H '' {U | P U})

/-- PDF pp.10–12: an explicit attaining gate and time, together with the lower bound
against every capable gate. Simulation is ideal fast control as on p.4. -/
def OptimalTask (H : TwoMatrix) (P : TwoMatrix → Prop) (U : TwoMatrix) (t : ℝ) : Prop :=
  P U ∧ IdealSimulates H U t ∧ interactionCost H U = ENNReal.ofReal t ∧
    taskCost H P = ENNReal.ofReal t ∧
    ∀ V : TwoMatrix, P V → interactionCost H U ≤ interactionCost H V

/-- PDF p.11, Result 5: the minimizing interaction content (not necessarily unique). -/
def optimalTransmissionContent (a : Triple) : Triple :=
  ![Real.pi / 4, Real.pi / 4, Real.pi / 4 * (2 * a 2 / (a 0 + a 1))]

/-- PDF p.13, Appendix A: determinant phase of the controlled one-qubit unitary is
free on the control. b is an eigenphase half-angle, before folding into the gate chamber. -/
def ControlPhase (W : OneMatrix) (b : ℝ) : Prop :=
  0 ≤ b ∧ b ≤ Real.pi / 2 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
    (z • W).charpoly =
      (Polynomial.X - Polynomial.C (Complex.exp (2 * Complex.I * (b : ℂ)))) *
      (Polynomial.X - Polynomial.C (Complex.exp (-2 * Complex.I * (b : ℂ))))

/-- PDF p.13, Appendix A: fold b at pi/4 rather than selecting a principal argument. -/
def controlledContent (b : ℝ) : Triple := ![min b (Real.pi / 2 - b), 0, 0]

/-- PDF p.12, IV.C: four disjoint chamber strata; both signed SWAP endpoints are included. -/
def ChamberClass (b : Triple) (k : Fin 4) : Prop :=
  if k = 0 then b 0 < Real.pi / 4
  else if k = 1 then b 0 = Real.pi / 4 ∧ b 1 < Real.pi / 4
  else if k = 2 then b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4 ∧ |b 2| < Real.pi / 4
  else b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4 ∧ |b 2| = Real.pi / 4

/-- PDF p.12, IV.C: operational profiles, including both orientations. "No capability"
means no perfect full bit in this single-use model, not zero Shannon capacity. -/
def TransmissionProfile (U : TwoMatrix) (k : Fin 4) : Prop :=
  if k = 0 then
    ¬ CanCbit U ∧ ¬ CanCbit (reverseParties U) ∧ ¬ CanTwoCbits U ∧
      ¬ CanQubit U ∧ ¬ CanQubit (reverseParties U) ∧
      ¬ CanHybrid U ∧ ¬ CanHybrid (reverseParties U) ∧ ¬ CanTwoQubits U
  else if k = 1 then
    CanCbit U ∧ CanCbit (reverseParties U) ∧ ¬ CanTwoCbits U ∧
      ¬ CanQubit U ∧ ¬ CanQubit (reverseParties U) ∧
      ¬ CanHybrid U ∧ ¬ CanHybrid (reverseParties U) ∧ ¬ CanTwoQubits U
  else if k = 2 then
    CanCbit U ∧ CanCbit (reverseParties U) ∧ CanTwoCbits U ∧
      CanQubit U ∧ CanQubit (reverseParties U) ∧
      CanHybrid U ∧ CanHybrid (reverseParties U) ∧ ¬ CanTwoQubits U
  else
    CanCbit U ∧ CanCbit (reverseParties U) ∧ CanTwoCbits U ∧
      CanQubit U ∧ CanQubit (reverseParties U) ∧
      CanHybrid U ∧ CanHybrid (reverseParties U) ∧ CanTwoQubits U

/-- PDF p.3, (4): interaction eigenvalues in the exact magic-basis order (2). -/
def interactionPhases (b : Triple) : Fin 4 → ℝ :=
  ![b 0 + b 1 - b 2, b 0 - b 1 + b 2, -b 0 + b 1 + b 2, -b 0 - b 1 - b 2]

/-- PDF p.3, (2): columns are -i(|01>+|10>)/sqrt2, (|00>+|11>)/sqrt2,
-i(|00>-|11>)/sqrt2, (|01>-|10>)/sqrt2, respectively. -/
def magicBasis : Matrix (Bool × Bool) (Fin 4) ℂ :=
  fun p j =>
    ![if p.1 ≠ p.2 then -Complex.I / (Real.sqrt 2 : ℂ) else 0,
      if p.1 = p.2 then 1 / (Real.sqrt 2 : ℂ) else 0,
      if p.1 = p.2 then (if p.1 then Complex.I else -Complex.I) / (Real.sqrt 2 : ℂ)
        else 0,
      if p.1 ≠ p.2 then (if p.1 then -1 else 1) / (Real.sqrt 2 : ℂ) else 0] j

/-- PDF p.13, Appendix A: express a computational-basis matrix in basis (2). -/
def magicMatrix (U : TwoMatrix) : Matrix (Fin 4) (Fin 4) ℂ :=
  magicBasis.conjTranspose * U * magicBasis

/-- PDF p.13: a phase-compatible SU(2) local decomposition of the actual representative.
This excludes assuming that an arbitrary projective phase has the same magic spectrum. -/
def PhaseCompatibleContent (U : TwoMatrix) (b : Triple) : Prop :=
  GateChamber b ∧ ∃ A B C D : OneGate,
    (A : OneMatrix).det = 1 ∧ (B : OneMatrix).det = 1 ∧
    (C : OneMatrix).det = 1 ∧ (D : OneMatrix).det = 1 ∧
    U = localMatrix A B * contentGate b * localMatrix C D

/-! Definition sanity checks; no paper theorem is proved here. -/

example : canonicalPauliInteraction (0 : Triple) = 0 := by
  simp [canonicalPauliInteraction]

example (H : TwoMatrix) : evolution H 0 = 1 := by
  simp [evolution]

example : GateChamber (0 : Triple) := by
  refine ⟨?_, ?_⟩
  · norm_num [SOrdered]
  · exact div_nonneg Real.pi_pos.le (by norm_num)

example : sOrder (0 : Triple) = 0 := by
  funext i
  fin_cases i <;> norm_num [sOrder]

example : SMajorized (0 : Triple) 0 := by
  norm_num [SMajorized, sOrder]

example (b : Triple) : contentIntegerShift b 0 = b := by
  funext i
  simp [contentIntegerShift]

example (A B : OneGate) : protocolTime ⟨A, B, []⟩ = 0 := rfl

example (A B : OneGate) (H : TwoMatrix) :
    protocolMatrix H ⟨A, B, []⟩ = localMatrix A B := rfl

example : dcnot (true, true) (false, true) = 1 := by
  simp [dcnot]

example (H : TwoMatrix) : taskCost H (fun _ => False) = ⊤ := by
  simp [taskCost]

example (U : TwoMatrix) (h : CanCbit U) : IsGate U := h.1

example (U : TwoMatrix) (h : CanTwoCbits U) : IsGate U := h.1

example (U : TwoMatrix) (h : CanQubit U) : IsGate U := h.1

example (U : TwoMatrix) (h : CanHybrid U) : IsGate U := h.1

example (U : TwoMatrix) (h : CanTwoQubits U) : IsGate U := h.1

example (b : Triple) : interactionPhases b 3 = -b 0 - b 1 - b 2 := rfl

example : magicBasis (false, false) 0 = 0 := by simp [magicBasis]

example : magicBasis (false, true) 3 = 1 / (Real.sqrt 2 : ℂ) := by simp [magicBasis]

end

end QAlgorithms.Papers.Independent.Intakethird100.P99


