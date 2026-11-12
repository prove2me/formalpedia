-- Prove2me | Definitions.Def_FourMsgQMA_NandCircuit
-- name    : FourMsgQMA_NandCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:06.699727+00:00
-- url     : https://prove2.me/theorems/3ee6a2d3-cae9-476d-aeb5-4b5ab5bdbdc2
-- title:
--   Boolean circuits over the fan-in-two NAND basis, with size and depth
-- statement:
--   A **NAND circuit** with $n_C$ inputs is a list of gates in topological order. Gate $g$ is wire $n_C+g$ and computes $\neg(w_a\wedge w_b)$ of two earlier wires; the output is the last wire. It is well formed when every gate reads only earlier wires. Its **size** $|C|$ is the number of gates, its **depth** the depth of the output wire (inputs have depth $0$), and it has an injective bit-string encoding.
--
--   These are the circuits of §3.9 ("The supported circuits are over the fan-in-two NAND basis, with depth at most $L$ and a predetermined polynomial size bound"). They also serve as the decryption circuits of Theorem 3.16 and the relations and index circuits of §3.11.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.9, p.17 (PDF 19)

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.9 (p.17, PDF 19): Boolean circuits
"over the fan-in-two NAND basis", with their size and depth.
-/

open QAlgorithms.Complexity

/-- A Boolean circuit over the fan-in-two NAND basis with `nIn` inputs and one output: wires
`0, …, nIn − 1` are the inputs; gate number `g` is wire `nIn + g` and computes
`NAND(wire a, wire b)` for its pair `(a, b)`; the output is the last wire. -/
structure NandCircuit where
  /-- The number of inputs `n_C`. -/
  nIn : ℕ
  /-- The gates, in topological order: the two input wires of each. -/
  gates : List (ℕ × ℕ)

/-- Topological order: each gate reads only earlier wires. -/
def NandCircuit.WellFormed (C : NandCircuit) : Prop :=
  ∀ g : Fin C.gates.length, C.gates[g].1 < C.nIn + g ∧ C.gates[g].2 < C.nIn + g

/-- The values of all wires on the input `x` (missing input bits read `false`). -/
def NandCircuit.wires (C : NandCircuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [!(vals.getD g.1 false && vals.getD g.2 false)])
    (List.ofFn fun i : Fin C.nIn => x.getD i false)

/-- `C(x)`: the value of the last wire. -/
def NandCircuit.eval (C : NandCircuit) (x : List Bool) : Bool :=
  (C.wires x).getLastD false

/-- The depths of all wires: inputs have depth `0`, a gate one more than its deeper input. -/
def NandCircuit.wireDepths (C : NandCircuit) : List ℕ :=
  C.gates.foldl (fun ds g => ds ++ [max (ds.getD g.1 0) (ds.getD g.2 0) + 1])
    (List.replicate C.nIn 0)

/-- The depth of `C`: the depth of its output wire. -/
def NandCircuit.depth (C : NandCircuit) : ℕ := C.wireDepths.getLastD 0

/-- The size `|C|`: the number of gates. -/
def NandCircuit.size (C : NandCircuit) : ℕ := C.gates.length

/-- The encoding of a circuit as a bit string. -/
def NandCircuit.encode (C : NandCircuit) : Str :=
  encNat C.nIn ++ encStr (C.gates.map fun g => encNat g.1 ++ encNat g.2)

end FourMsgQMA


