-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Circuit
-- name    : PSPACEOracleSynth_Main_Supplement_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:23:55.920196+00:00
-- url     : https://prove2.me/theorems/7e7814e2-bb52-43ca-b219-4058386edba7
-- title:
--   General circuits over G with coherent bit oracles
-- statement:
--   A general quantum circuit has ordered operations, specified input wires and its final live output wires. It extends the published initialization, discard, Hadamard, T, CNOT and dephasing operations by $T^\dagger$ and a classical bit-oracle gate on distinct named query and answer wires. Initialization appends a zero qubit, a measurement retains its outcome on its wire, and discarding removes that wire from the live register.
--
--   Space is the maximum number of live qubits, including the input. Descriptions use canonical current wire labels; discarded wires are renumbered. This is a choice of labels, with no bound on the total number of initialized or discarded qubits. The channel of a malformed interface is zero, and all complexity witnesses explicitly require a valid interface.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Definition 2.1, pp. 9–10

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Quantum
import Definitions.Def_UnitaryQIPPSPACE_Circuit
import Definitions.Def_PSPACEOracleSynth_Main_GateSet
import Definitions.Def_PSPACEOracleSynth_Main_Oracles
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_KTUnitary_Synth_SpaceUniform

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! Definition 2.1, pp. 9–10. Reuse the published general circuit operations, extending
by T† and coherent bit-oracle gates. Wire numbers are current live-wire positions.
Initialization appends a wire; discard renumbers. All remaining wires are outputs. -/

inductive GOp where
  | core (o : UnitaryQIPPSPACE.Op)
  | tdg (i : ℕ)
  | oracle (query : List ℕ) (answer : ℕ)

def GOp.next : GOp → ℕ → ℕ
  | .core o, n => o.next n
  | _, n => n

def GOp.valid : GOp → ℕ → Prop
  | .core o, n => o.Valid n
  | .tdg i, n => i < n
  | .oracle q b, n => q.Nodup ∧ b < n ∧ b ∉ q ∧ ∀ i ∈ q, i < n

def GOp.oracleFree : GOp → Prop
  | .oracle _ _ => False
  | _ => True

def GOp.code : GOp → Str
  | .core o => tup [[false], o.code]
  | .tdg i => tup [[true,false], Nat.bits i]
  | .oracle q b => tup ([true,true] :: Nat.bits b :: q.map Nat.bits)

open Classical in
noncomputable def bitOracleMat (A : Oracle) (q : List ℕ) (b n : ℕ) : Op (Bits n) :=
  fun u v => if ∀ i : Fin n, u i =
    (if i.val = b then xor (v i) (A (q.map fun j => if hj : j < n then v ⟨j, hj⟩ else false))
     else v i) then 1 else 0

noncomputable def GOp.act (A : Oracle) : (o : GOp) → (n : ℕ) →
    Op (Bits n) → Op (Bits (o.next n))
  | .core o, n, ρ => o.act n ρ
  | .tdg i, n, ρ => UnitaryQIPPSPACE.conjBy
      (UnitaryQIPPSPACE.embed1 UnitaryQIPPSPACE.gateT n i)ᴴ ρ
  | .oracle q b, n, ρ => UnitaryQIPPSPACE.conjBy (bitOracleMat A q b n) ρ

abbrev GCircuit := List GOp

def gcNext : GCircuit → ℕ → ℕ
  | [], n => n
  | o :: c, n => gcNext c (o.next n)

def gcValid : GCircuit → ℕ → Prop
  | [], _ => True
  | o :: c, n => o.valid n ∧ gcValid c (o.next n)

noncomputable def gcAct (A : Oracle) : (c : GCircuit) → (n : ℕ) →
    Op (Bits n) → Op (Bits (gcNext c n))
  | [], _, ρ => ρ
  | o :: c, n, ρ => gcAct A c (o.next n) (o.act A n ρ)

def gcSpace : GCircuit → ℕ → ℕ
  | [], n => n
  | o :: c, n => max n (gcSpace c (o.next n))

/-- The input list is canonical 0,…,a−1; the output list is the final live wires. -/
structure GeneralCircuit where
  input : ℕ
  ops : GCircuit

namespace GeneralCircuit

def output (C : GeneralCircuit) := gcNext C.ops C.input

def code (C : GeneralCircuit) : Str := tup (Nat.bits C.input :: C.ops.map GOp.code)
def gateCodes (C : GeneralCircuit) := C.ops.map GOp.code
def valid (C : GeneralCircuit) := gcValid C.ops C.input
def space (C : GeneralCircuit) := gcSpace C.ops C.input
def oracleFree (C : GeneralCircuit) := ∀ o ∈ C.ops, o.oracleFree

/-- The zero value off the well-formed interface is never used by a class witness. -/
noncomputable def channel (C : GeneralCircuit) (A : Oracle) (a b : ℕ) : Map (Bits a) (Bits b) :=
  if h : C.input = a ∧ C.output = b then
    fun ρ => cast (congrArg (fun k => Op (Bits k)) h.2)
      (gcAct A C.ops C.input (cast (congrArg (fun k => Op (Bits k)) h.1.symm) ρ))
  else fun _ => 0

end GeneralCircuit

end PSPACEOracleSynth.Main.Supplement


