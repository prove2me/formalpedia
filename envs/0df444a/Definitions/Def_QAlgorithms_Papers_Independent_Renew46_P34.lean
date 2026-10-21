-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
-- name    : QAlgorithms_Papers_Independent_Renew46_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:05:46.169544+00:00
-- url     : https://prove2.me/theorems/80a63e9a-3ed0-41f8-be40-31ce403d13e5
-- title:
--   Definitions for A family of quantum protocols
-- statement:
--   The objects the formalized statements of *A family of quantum protocols* (arXiv:quant-ph/0308044) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourceAB`: PDF p.1: the AB marginal of one normalized pure ABE source.
--   - `sourceAE`: PDF p.1: the AE marginal, retaining the same A and E and tracing out B.
--   - `entropyA`: PDF p.1: Alice's entropy in bits.
--   - `informationAB`: PDF p.1: I(A;B), computed from the source rather than arbitrary rate parameters.
--   - `informationAE`: PDF p.1: I(A;E), computed from the same pure source.
--   - `stateBlock`: PDF p.1: actual n independent source copies, regrouped as Alice's and Bob's blocks. At n=0 both blocks are singleton spaces and the product is one.
--   - `emptySource`: PDF p.1: the trivial shared state, with no entanglement or communication.
--   - `forwardResource`: PDF pp.1–2: a channel with no Alice output, retaining a singleton Alice port.
--   - `emptyResource`: PDF pp.2–3: no dynamic resource, on singleton input and output ports.
--   - `coherentResource`: PDF p.2, (6): k coherent bits, the isometry |x> -> |x>_A|x>_B. Off-diagonal matrix entries are retained.
--   - `aliceMap`: PDF pp.1–3: free local action on Alice, identity on Bob, including off-diagonal blocks.
--   - `OneWayCode`: PDF pp.1–3: a finite forward protocol with actual resource ports. The source is on A,B. X is the dynamic-resource input; Z,Y are its Alice,Bob outputs. I is the unknown task input, initially at Alice. OA,OB are the designated final outputs. Only q qubits, c dephased bits, e input EPR pairs, and the specified source/channel are used. The encoder and both final local maps are fixed before I is supplied.
--   - `initialCodeState`: PDF pp.1–3: initial task state tensor the supplied source tensor exactly e EPR pairs. Alice owns I,A and the first EPR half; Bob owns B and the other half.
--   - `transmittedCodeState`: PDF pp.1–3: apply the actual dynamic resource, send q qubits, dephase and send c bits. Z and the encoder's memory stay at Alice; every other displayed port goes to Bob. The dephasing condition prevents a classical wire from acting as a coherent bit.
--   - `Simulates`: PDF pp.1–3: uniform trace-distance task simulation for all finite reference systems. The chosen code is outside both universal quantifiers.
--   - `ExactConversion`: PDF pp.2–3: exact finite conversion, with no borrowed resources except the counted e ebits. Equality on all operators also fixes every quantum reference extension.
--   - `TaskInput`: PDF pp.1–3: task port, with unknown quantum data and a classical message.
--   - `TaskBob`: PDF pp.1–3: Bob receives the quantum data, classical message, and his output EPR halves.
--   - `taskTarget`: PDF pp.1–3: the target channel transmits quantum data, transmits dephased classical data, and creates e EPR pairs. Alice holds exactly the first EPR halves.
--   - `coherentTarget`: PDF p.3: coherent bits with a separately returned EPR catalyst.
--   - `rateConstraint`: PDF pp.1–3: signed net rate. A negative rate is an input bound, with zero output; a nonnegative rate is an output bound, with zero input. Zero-rate inputs are exactly absent.
--   - `countsMeet`: PDF pp.1–2: a task code's signed classical, quantum, and entanglement resource counts.
--   - `StaticRI`: PDF pp.1–2: static signed resource inequality, using exactly n independent source copies. No channel is hidden in the singleton dynamic port; local ancillas are free.
--   - `DynamicRI`: PDF pp.1–2: dynamic signed resource inequality. The sole noisy resource is exactly n memoryless uses of N; there is no shared source beyond the explicitly counted EPR input.
--   - `ChannelData`: PDF p.1: Stinespring data for the specified channel; the environment is not unrelated.
--   - `channelPsi`: PDF p.1: (identity_A tensor U_N)|phi>, reordered as (A,B),E.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, https://arxiv.org/abs/quant-ph/0308044v2

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics

/-! Statements from Devetak–Harrow–Winter, quant-ph/0308044v2.
All new definitions are paper-local. Local CPTP maps include arbitrary free ancillas.
Registers in a code are grouped by owner, and classical wires are explicitly dephased.
The main asymptotic statements use uniform trace-distance channel simulation.
Compilation is pending the batch handoff. General retained-environment coherification
and sequential catalytic recycling are deferred in the accompanying HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1: the AB marginal of one normalized pure ABE source. -/
def sourceAB {A B E : Type} [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) := traceRight (pureDensity psi)

/-- PDF p.1: the AE marginal, retaining the same A and E and tracing out B. -/
def sourceAE {A B E : Type} [Fintype B]
    (psi : EuclideanSpace ℂ ((A × B) × E)) : Matrix (A × E) (A × E) ℂ :=
  fun i j => ∑ b, pureDensity psi ((i.1,b),i.2) ((j.1,b),j.2)

/-- PDF p.1: Alice's entropy in bits. -/
def entropyA {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) : ℝ :=
  vnEntropy (traceRight (sourceAB psi))

/-- PDF p.1: I(A;B), computed from the source rather than arbitrary rate parameters. -/
def informationAB {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) : ℝ :=
  entropyA psi + vnEntropy (traceLeft (sourceAB psi)) - vnEntropy (sourceAB psi)

/-- PDF p.1: I(A;E), computed from the same pure source. -/
def informationAE {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) : ℝ :=
  entropyA psi + vnEntropy (traceLeft (pureDensity psi)) - vnEntropy (sourceAE psi)

/-- PDF p.1: actual n independent source copies, regrouped as Alice's and Bob's blocks.
At n=0 both blocks are singleton spaces and the product is one. -/
def stateBlock {A B : Type} (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun i j => ∏ t, rho (i.1 t,i.2 t) (j.1 t,j.2 t)

/-- PDF p.1: the trivial shared state, with no entanglement or communication. -/
def emptySource : Matrix (Unit × Unit) (Unit × Unit) ℂ := fun _ _ => 1

/-- PDF pp.1–2: a channel with no Alice output, retaining a singleton Alice port. -/
def forwardResource {X Y : Type} (N : Superop X Y) : Superop X (Unit × Y) :=
  fun M i j => N M i.2 j.2

/-- PDF pp.2–3: no dynamic resource, on singleton input and output ports. -/
def emptyResource : Superop Unit (Unit × Unit) :=
  forwardResource (fun M : Matrix Unit Unit ℂ => M)

/-- PDF p.2, (6): k coherent bits, the isometry |x> -> |x>_A|x>_B.
Off-diagonal matrix entries are retained. -/
def coherentResource (k : ℕ) : Superop (Qubits k) (Qubits k × Qubits k) :=
  fun M i j => if i.1 = i.2 ∧ j.1 = j.2 then M i.1 j.1 else 0

/-- PDF pp.1–3: free local action on Alice, identity on Bob, including off-diagonal blocks. -/
def aliceMap {X Y T : Type} (F : Superop X Y) : Superop (X × T) (Y × T) :=
  fun M i j => F (fun a b => M (a,i.2) (b,j.2)) i.1 j.1

/-- PDF pp.1–3: a finite forward protocol with actual resource ports.
The source is on A,B. X is the dynamic-resource input; Z,Y are its Alice,Bob outputs.
I is the unknown task input, initially at Alice. OA,OB are the designated final outputs.
Only q qubits, c dephased bits, e input EPR pairs, and the specified source/channel are used.
The encoder and both final local maps are fixed before I is supplied. -/
structure OneWayCode (A B X Z Y I OA OB : Type)
    [Fintype A] [Fintype B] [Fintype X] [Fintype Z] [Fintype Y]
    [Fintype I] [Fintype OA] [Fintype OB] where
  e : ℕ
  q : ℕ
  c : ℕ
  memory : ℕ
  memoryPositive : 0 < memory
  encoder : Superop (I × (A × Qubits e))
    (X × (Fin memory × (Qubits q × Qubits c)))
  aliceDecoder : Superop (Z × Fin memory) OA
  bobDecoder : Superop (Y × (B × (Qubits e × (Qubits q × Qubits c)))) OB
  encoderChannel : IsChannel encoder
  aliceChannel : IsChannel aliceDecoder
  bobChannel : IsChannel bobDecoder

/-- PDF pp.1–3: initial task state tensor the supplied source tensor exactly e EPR pairs.
Alice owns I,A and the first EPR half; Bob owns B and the other half. -/
def initialCodeState {A B X Z Y I OA OB : Type}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Z] [Fintype Y]
    [Fintype I] [Fintype OA] [Fintype OB]
    (P : OneWayCode A B X Z Y I OA OB)
    (rho : Matrix (A × B) (A × B) ℂ) (M : Matrix I I ℂ) :
    Matrix ((I × (A × Qubits P.e)) × (B × Qubits P.e))
      ((I × (A × Qubits P.e)) × (B × Qubits P.e)) ℂ :=
  fun i j => M i.1.1 j.1.1 * rho (i.1.2.1,i.2.1) (j.1.2.1,j.2.1) *
    pureDensity (maxEntangled P.e) (i.1.2.2,i.2.2) (j.1.2.2,j.2.2)

/-- PDF pp.1–3: apply the actual dynamic resource, send q qubits, dephase and send c bits.
Z and the encoder's memory stay at Alice; every other displayed port goes to Bob.
The dephasing condition prevents a classical wire from acting as a coherent bit. -/
def transmittedCodeState {A B X Z Y I OA OB : Type}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Z] [Fintype Y]
    [Fintype I] [Fintype OA] [Fintype OB]
    (P : OneWayCode A B X Z Y I OA OB) (rho : Matrix (A × B) (A × B) ℂ)
    (N : Superop X (Z × Y)) (M : Matrix I I ℂ) :
    Matrix ((Z × Fin P.memory) × (Y × (B × (Qubits P.e × (Qubits P.q × Qubits P.c)))))
      ((Z × Fin P.memory) × (Y × (B × (Qubits P.e × (Qubits P.q × Qubits P.c))))) ℂ :=
  let T := aliceMap P.encoder (initialCodeState P rho M)
  fun i j => if i.2.2.2.2.2 = j.2.2.2.2.2 then
    N (fun x x' =>
      T ((x,(i.1.2,(i.2.2.2.2.1,i.2.2.2.2.2))),(i.2.2.1,i.2.2.2.1))
        ((x',(j.1.2,(j.2.2.2.2.1,j.2.2.2.2.2))),(j.2.2.1,j.2.2.2.1)))
      (i.1.1,i.2.1) (j.1.1,j.2.1)
  else 0

/-- PDF pp.1–3: uniform trace-distance task simulation for all finite reference systems.
The chosen code is outside both universal quantifiers. -/
def Simulates {A B X Z Y I OA OB : Type}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Z] [Fintype Y]
    [Fintype I] [Fintype OA] [Fintype OB]
    (P : OneWayCode A B X Z Y I OA OB) (rho : Matrix (A × B) (A × B) ℂ)
    (N : Superop X (Z × Y)) (target : Superop I (OA × OB)) (eps : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r × I) (Fin r × I) ℂ,
    IsDensityMatrix M →
      traceDistance (idTensorSuperop (fun S => aliceMap P.aliceDecoder
          (idTensorSuperop P.bobDecoder (transmittedCodeState P rho N S))) M)
        (idTensorSuperop target M) ≤ eps

/-- PDF pp.2–3: exact finite conversion, with no borrowed resources except the counted e ebits.
Equality on all operators also fixes every quantum reference extension. -/
def ExactConversion {X Z Y I OA OB : Type}
    [Fintype X] [Fintype Z] [Fintype Y] [Fintype I] [Fintype OA] [Fintype OB]
    (N : Superop X (Z × Y)) (e q c : ℕ) (target : Superop I (OA × OB)) : Prop :=
  ∃ P : OneWayCode Unit Unit X Z Y I OA OB,
    P.e = e ∧ P.q = q ∧ P.c = c ∧
      (fun M => aliceMap P.aliceDecoder
        (idTensorSuperop P.bobDecoder (transmittedCodeState P emptySource N M))) = target

/-- PDF pp.1–3: task port, with unknown quantum data and a classical message. -/
abbrev TaskInput (q c : ℕ) := Qubits q × Qubits c

/-- PDF pp.1–3: Bob receives the quantum data, classical message, and his output EPR halves. -/
abbrev TaskBob (q c e : ℕ) := Qubits q × (Qubits c × Qubits e)

/-- PDF pp.1–3: the target channel transmits quantum data, transmits dephased classical data,
and creates e EPR pairs. Alice holds exactly the first EPR halves. -/
def taskTarget (q c e : ℕ) :
    Superop (TaskInput q c) (Qubits e × TaskBob q c e) :=
  fun M i j => if i.2.2.1 = j.2.2.1 then
    M (i.2.1,i.2.2.1) (j.2.1,j.2.2.1) *
      pureDensity (maxEntangled e) (i.1,i.2.2.2) (j.1,j.2.2.2)
  else 0

/-- PDF p.3: coherent bits with a separately returned EPR catalyst. -/
def coherentTarget (k e : ℕ) :
    Superop (Qubits k) ((Qubits k × Qubits e) × (Qubits k × Qubits e)) :=
  fun M i j => coherentResource k M (i.1.1,i.2.1) (j.1.1,j.2.1) *
    pureDensity (maxEntangled e) (i.1.2,i.2.2) (j.1.2,j.2.2)

/-- PDF pp.1–3: signed net rate. A negative rate is an input bound, with zero output;
a nonnegative rate is an output bound, with zero input. Zero-rate inputs are exactly absent. -/
def rateConstraint (used produced n : ℕ) (rate delta : ℝ) : Prop :=
  if rate < 0 then produced = 0 ∧ (used : ℝ) ≤ n * (-rate + delta)
  else used = 0 ∧ (n : ℝ) * (rate - delta) ≤ produced

/-- PDF pp.1–2: a task code's signed classical, quantum, and entanglement resource counts. -/
def countsMeet {A B X Z Y : Type}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Z] [Fintype Y]
    {qo co eo : ℕ}
    (P : OneWayCode A B X Z Y (TaskInput qo co) (Qubits eo) (TaskBob qo co eo))
    (n : ℕ) (c q e delta : ℝ) : Prop :=
  rateConstraint P.c co n c delta ∧ rateConstraint P.q qo n q delta ∧
    rateConstraint P.e eo n e delta

/-- PDF pp.1–2: static signed resource inequality, using exactly n independent source copies.
No channel is hidden in the singleton dynamic port; local ancillas are free. -/
def StaticRI {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (c q e : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n ≥ n0, ∃ qo co eo : ℕ,
    ∃ P : OneWayCode (Fin n → A) (Fin n → B) Unit Unit Unit
      (TaskInput qo co) (Qubits eo) (TaskBob qo co eo),
      countsMeet P n c q e delta ∧
        Simulates P (stateBlock rho n) emptyResource (taskTarget qo co eo) eps

/-- PDF pp.1–2: dynamic signed resource inequality. The sole noisy resource is exactly n
memoryless uses of N; there is no shared source beyond the explicitly counted EPR input. -/
def DynamicRI {X Y : Type} [Fintype X] [Fintype Y]
    (N : Superop X Y) (c q e : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n ≥ n0, ∃ qo co eo : ℕ,
    ∃ P : OneWayCode Unit Unit (Fin n → X) Unit (Fin n → Y)
      (TaskInput qo co) (Qubits eo) (TaskBob qo co eo),
      countsMeet P n c q e delta ∧
        Simulates P emptySource (forwardResource (piSuperop (fun _ : Fin n => N)))
          (taskTarget qo co eo) eps

/-- PDF p.1: Stinespring data for the specified channel; the environment is not unrelated. -/
structure ChannelData (X B E : Type) [Fintype X] [Fintype B] [Fintype E] where
  channel : Superop X B
  channelCPTP : IsChannel channel
  dilation : Matrix (B × E) X ℂ
  isometry : dilationᴴ * dilation = 1
  realizes : ∀ M, channel M = traceRight (conjSuperop dilation M)

/-- PDF p.1: (identity_A tensor U_N)|phi>, reordered as (A,B),E. -/
def channelPsi {A X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (D : ChannelData X B E) (phi : EuclideanSpace ℂ (A × X)) :
    EuclideanSpace ℂ ((A × B) × E) :=
  WithLp.toLp 2 fun i => ∑ x, D.dilation (i.1.2,i.2) x * phi (i.1.1,x)

/-- Sanity: the empty tensor block has entry one, including at the n=0 boundary (PDF p.1). -/
example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) : stateBlock rho 0 i j = 1 := by
  simp [stateBlock]

/-- Sanity: a negative rate is a genuine input constraint, not truncated subtraction (p.2). -/
example (u v n : ℕ) (r d : ℝ) (hr : r < 0) :
    rateConstraint u v n r d ↔ v = 0 ∧ (u : ℝ) ≤ n * (-r + d) := by
  simp [rateConstraint, hr]

/-- Sanity: off-diagonal coherent bits survive; |00><11| becomes |00,00><11,11| (p.2). -/
example (M : Matrix (Qubits 2) (Qubits 2) ℂ) (x y : Qubits 2) :
    coherentResource 2 M (x,x) (y,y) = M x y := by
  simp [coherentResource]

/-- Sanity: k=0 coherent bits act on the singleton port with entry unchanged (p.3). -/
example (M : Matrix (Qubits 0) (Qubits 0) ℂ) (x y : Qubits 0) :
    coherentResource 0 M (x,x) (y,y) = M x y := by
  simp [coherentResource]

end QAlgorithms.Papers.Independent.Renew46.P34


