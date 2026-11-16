-- Prove2me | Definitions.Def_NuclearTensor_Membership_Supplement_QuantumPrograms
-- name    : NuclearTensor_Membership_Supplement_QuantumPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:41:25.008987+00:00
-- url     : https://prove2.me/theorems/684015e6-a4c3-4610-a7b3-2cf968e3f325
-- title:
--   Finite quantum programs with copy access and charged execution
-- statement:
--   A quantum program is finite classical control together with the elementary gates $H,T,\mathrm{CX}$, zero-qubit initialization, computational-basis measurement, discarding working registers, and a fresh-copy instruction. Gate semantics reuse the published elementary-gate device. Its classical part executes the published arithmetic instructions and charged real SVD, with no local-optimization service. A tail call executes actual finite supplied code; it is used only for the black-box tester in dimensionality reduction.
--
--   A measurement branch retains an unnormalized positive operator, whose trace is its Born probability. Fresh copies tensor the same unknown state onto the current registers. Runtime and copies are sums of the executed instruction charges; they include classical output traffic. Termination, a normalized output law, bounds on every branch, unconditional output validity, and a success event are stated separately.
--
--   For channel approximation, every finite reference register and every joint density operator are retained:
--
--   $$\|((\widehat\Phi-\Phi)\otimes I_B)(X)\|_1\le\delta.$$
--
--   The channel predicate is the existing finite-dimensional Kraus/CPTP predicate. This supplies a reusable operational interface without a state-entry, optimization, filtering, or compression oracle.
--
--   **Formalization Note** Arbitrary positive dimensions are embedded in qubit computational-basis registers; unused basis coordinates initially have zero amplitude. Working registers are traced out on return. Channel comparisons retain the entire physical output register, including any unused coordinates. The input copy count and classical input description are separate.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp. 9, 21–35, 38–51; Section 2, Definitions 6.2–6.3, Section 7.1 and Appendices A–C.

import Definitions.Def_NuclearTensor_Membership_Supplement_Geometry
import Definitions.Def_PoQHierarchy_Main_Device

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

namespace NuclearTensor.Membership.Supplement

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev QMat (n R : ℕ) := Matrix (Bits n × Fin R) (Bits n × Fin R) ℂ

def bitNumber {n : ℕ} (z : Bits n) : ℕ := ∑ i, if z i then 2 ^ i.val else 0

def encoded {a : ℕ} (A : CMat a) : Matrix (Bits (Nat.clog 2 a)) (Bits (Nat.clog 2 a)) ℂ :=
  fun x y => if h : bitNumber x < a ∧ bitNumber y < a then
    A ⟨_, h.1⟩ ⟨_, h.2⟩ else 0

/-- No measurement, preparation, filter or optimizer can be supplied as a primitive.
All quantum gates are the published fixed universal gate set. Classical instructions use
finite arithmetic code; localOptimize and call are unavailable in basicStep with no service. -/
inductive QInstruction where
  | classical (instruction : Instruction)
  | h (address : ℕ)
  | t (address : ℕ)
  | cx (control target : ℕ)
  | zero
  | copy
  | measure (address destination : ℕ)
  | trim (count : ℕ)
  | tailCall (callee ri rn ii inn : ℕ)
  | halt

abbrev QProgram := List QInstruction

structure QConfiguration (R : ℕ) where
  classical : Configuration
  qubits : ℕ
  state : QMat qubits R
  copies : ℕ
  time : ℕ
  calls : ℕ

def liftGate {n R : ℕ} (g : PoQHierarchy.Main.Gate) (X : QMat n R) : QMat n R :=
  let U : Matrix (Bits n) (Bits n) ℂ := fun z w =>
    g.apply (fun v => if v = w then 1 else 0) z
  fun zr ws => ∑ x, ∑ y, U zr.1 x * X (x, zr.2) (y, ws.2) * conj (U ws.1 y)

def appendState {n m R : ℕ} (X : QMat n R) (Y : Matrix (Bits m) (Bits m) ℂ) : QMat (n + m) R :=
  fun zr ws =>
    X ((fun i => zr.1 (Fin.castAdd m i)), zr.2)
      ((fun i => ws.1 (Fin.castAdd m i)), ws.2) *
    Y (fun i => zr.1 (Fin.natAdd n i)) (fun i => ws.1 (Fin.natAdd n i))

def measureState {n R : ℕ} (i : Fin n) (b : Bool) (X : QMat n R) : QMat n R :=
  fun zr ws => if zr.1 i = b ∧ ws.1 i = b then X zr ws else 0

def classicalCode (P : QProgram) : Program := P.map fun i => match i with
  | .classical a => a
  | _ => .halt

/-- Return the first n output qubits, tracing out all other working qubits. References
are retained, including their coherences. No exponential output description is charged. -/
def retained {R : ℕ} (n : ℕ) (s : QConfiguration R) : QMat n R := fun zr ws =>
  if hn : n ≤ s.qubits then
    ∑ z : Bits (s.qubits - n),
      let combine := fun (x : Bits n) (z : Bits (s.qubits - n)) (i : Fin s.qubits) =>
        if h : i.val < n then x ⟨_, h⟩ else
          z ⟨i.val - n, by omega⟩
      s.state (combine zr.1 z, zr.2) (combine ws.1 z, ws.2)
  else 0


/-- Fresh copies are tensor factors independent of all current target/reference registers.
Each gate, classical instruction, allocation, measurement, copy, and output is charged. -/
def qStep {a R : ℕ} (ρ : CMat a) (σ : Spectral) (A r : ℕ) (P : QProgram)
    (s : QConfiguration R) : Option (List (QConfiguration R)) :=
  let next := {s with classical := {s.classical with core :=
    {s.classical.core with pc := s.classical.core.pc + 1}}, time := s.time + 1}
  let addr := fun i => (s.classical.core.ptrs i).toNat
  match P[s.classical.core.pc]? with
  | some (.classical i) =>
      match i with
      | .call .. | .localOptimize .. | .halt => none
      | _ => match basicStep σ none A r (classicalCode P) s.classical with
        | none => none
        | some (c, cost) => some [{s with classical := c, time := s.time + cost}]
  | some (.h i) => if addr i < s.qubits then
      some [{next with state := liftGate (.h (addr i)) s.state}] else none
  | some (.t i) => if addr i < s.qubits then
      some [{next with state := liftGate (.t (addr i)) s.state}] else none
  | some (.cx i j) => if addr i < s.qubits ∧ addr j < s.qubits ∧ addr i ≠ addr j then
      some [{next with state := liftGate (.cx (addr i) (addr j)) s.state}] else none
  | some .zero => some [⟨next.classical, s.qubits + 1,
      appendState s.state (fun z w => if z 0 = false ∧ w 0 = false then 1 else 0),
      s.copies, s.time + 1, s.calls⟩]
  | some .copy => some [⟨next.classical, s.qubits + Nat.clog 2 a,
      appendState s.state (encoded ρ), s.copies + 1, s.time + 1 + Nat.clog 2 a, s.calls⟩]
  | some (.measure i dst) => if h : addr i < s.qubits then
      some ([false, true].map fun b => {next with
        state := measureState ⟨_, h⟩ b s.state,
        classical := {next.classical with core := {next.classical.core with
          ptrs := Function.update next.classical.core.ptrs dst (if b then 1 else 0)}}})
      else none
  | some (.trim count) => if addr count ≤ s.qubits then
      some [⟨next.classical, addr count, retained (addr count) s, s.copies,
        s.time + 1 + s.qubits - addr count, s.calls⟩] else none
  | _ => none

/-- Branches carry unnormalized density operators, so traces are Born probabilities.
The finite fuel bounds only the semantic unfolding; executed charges determine resource bounds.
An invalid instruction or any nonterminating branch gives none, never a successful zero law. -/
def qRun {a R : ℕ} (ρ : CMat a) (σ : Spectral) (A r : ℕ) (P : QProgram)
    (library : List QProgram) : ℕ → QConfiguration R → Option (List (QConfiguration R))
  | 0, s => if P[s.classical.core.pc]? = some .halt then some [s] else none
  | fuel + 1, s => if P[s.classical.core.pc]? = some .halt then some [s] else
      match P[s.classical.core.pc]? with
      | some (.tailCall callee ri rn ii inn) => do
          let child ← library[(s.classical.core.ptrs callee).toNat]?
          let is := readBlock s.classical.integers (s.classical.core.ptrs ii)
            (s.classical.core.ptrs inn).toNat
          let rs := readBlock s.classical.core.mem (s.classical.core.ptrs ri)
            (s.classical.core.ptrs rn).toNat
          qRun ρ σ A r child library fuel
            ⟨initConfig is rs, s.qubits, s.state, s.copies,
              s.time + 1 + is.length + rs.length, s.calls + 1⟩
      | _ => do
          let children ← qStep ρ σ A r P s
          let outputs ← children.mapM (qRun ρ σ A r P library fuel)
          return outputs.flatten

def initialQuantum {n R : ℕ} (is : List ℤ) (rs : List ℝ) (X : QMat n R) : QConfiguration R :=
  ⟨initConfig is rs, n, X, 0, 0, 0⟩

def branchWeight {R : ℕ} (s : QConfiguration R) : ℝ := (Matrix.trace s.state).re

def eventProbability {R : ℕ} (L : List (QConfiguration R)) (E : Configuration → Prop) : ℝ :=
  (L.map fun s => if E s.classical then branchWeight s else 0).sum

def validLaw {R : ℕ} (L : List (QConfiguration R)) : Prop :=
  (∀ s ∈ L, s.state.PosSemidef) ∧ (L.map branchWeight).sum = 1

def charged {R : ℕ} (L : List (QConfiguration R)) (copies time : ℝ) : Prop :=
  ∀ s ∈ L, (s.copies : ℝ) ≤ copies ∧
    ((1 + s.time + (outputIntegers s.classical).length + (outputReals s.classical).length : ℕ) : ℝ) ≤ time

/-- A classical-output quantum computation; the input state has no classical representation
in the RAM. Only the charged copy instruction can obtain it. -/
def quantumAlgorithmWith {a : ℕ} (ρ : CMat a) (σ : Spectral) (A r : ℕ) (P : QProgram)
    (is : List ℤ) (rs : List ℝ) (copies time failure : ℝ) (E : Configuration → Prop) (library : List QProgram)
    (always : Configuration → Prop := fun _ => True) : Prop :=
  ∃ fuel L, qRun ρ σ A r P library fuel
    (initialQuantum is rs (n := 0) (R := 1) (fun _ _ => 1)) = some L ∧
    validLaw L ∧ charged L copies time ∧ (∀ s ∈ L, s.calls ≤ 1 ∧ always s.classical) ∧
    eventProbability L E ≥ 1 - failure

def quantumAlgorithm {a : ℕ} (ρ : CMat a) (σ : Spectral) (A r : ℕ) (P : QProgram)
    (is : List ℤ) (rs : List ℝ) (copies time failure : ℝ) (E : Configuration → Prop)
    (always : Configuration → Prop := fun _ => True) : Prop :=
  quantumAlgorithmWith ρ σ A r P is rs copies time failure E [] always

/-- Finite-dimensional amplification of a linear map, including arbitrary finite references. -/
def amplify {a b : ℕ} (f : CMat a → CMat b) (R : ℕ)
    (X : Matrix (Fin a × Fin R) (Fin a × Fin R) ℂ) :
    Matrix (Fin b × Fin R) (Fin b × Fin R) ℂ := fun ur vs =>
  ∑ i, ∑ j, f (fun x y => if x = i ∧ y = j then 1 else 0) ur.1 vs.1 *
    X (i, ur.2) (j, vs.2)

def encodeJoint {a R : ℕ} (X : Matrix (Fin a × Fin R) (Fin a × Fin R) ℂ) :
    QMat (Nat.clog 2 a) R := fun zr ws =>
  if h : bitNumber zr.1 < a ∧ bitNumber ws.1 < a then
    X (⟨_, h.1⟩, zr.2) (⟨_, h.2⟩, ws.2) else 0

/-- Execution-level channel approximation, with arbitrary entangled references and fresh
auxiliary copies. The ideal channel itself is required CPTP. -/
def implements {a b c : ℕ} (ρ : CMat c) (σ : Spectral) (A r : ℕ) (P : QProgram)
    (is : List ℤ) (rs : List ℝ) (f : CMat a → CMat b) (δ copies time : ℝ) : Prop :=
  IsChannel f ∧ ∀ R : ℕ, ∀ X : Matrix (Fin a × Fin R) (Fin a × Fin R) ℂ,
    ClonableQMASep.Main.IsDensity X →
    ∃ fuel L, qRun ρ σ A r P [] fuel (initialQuantum is rs (encodeJoint X)) = some L ∧
      validLaw L ∧ charged L copies time ∧
      (∀ s ∈ L, Nat.clog 2 b ≤ s.qubits) ∧
      ClonableQMASep.Main.traceNorm
        ((L.map (retained (Nat.clog 2 b))).sum - encodeJoint (amplify f R X)) ≤ δ

/-- A copy-free circuit still runs in the same model: this arbitrary density input is
inaccessible when the executed copy count is zero. -/
def dummyState : CMat 1 := fun _ _ => 1

end NuclearTensor.Membership.Supplement


