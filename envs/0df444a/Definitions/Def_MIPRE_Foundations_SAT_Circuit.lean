-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Circuit
-- name    : MIPRE_Foundations_SAT_Circuit
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:22.357645+00:00
-- url     : https://prove2.me/theorems/308ee67a-afe6-463d-9b28-a14534139ac8
-- title:
--   Definitions of Circuit: Boolean circuits as data The circuits of the succinct Cook–Levin theorem (`planning/succinct-cook-levin.md`, S0;…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Circuit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean circuits as data. The circuits of the succinct Cook–Levin theorem (`planning/succinct-cook-levin.md`, S0; `answer_reduction.tex` `sec:ar-tms`): a circuit is a list of gates in topological order, each gate reading input bits or the values of earlier gates, the last gate being the output. Fan-in is at most two by the shape of the gates; fan-out at most two and a terminal output gate are the well-formedness conditions (`Circuit.WellFormed`) that the arithmetization of the Tseitin formula needs for its individual-degree bound (`prop:tseitin-arith-degree`). The gate count is the paper's…
--
--   **Definitions** (16): `MIPRE.SAT.Circuit` (A Boolean circuit: `inputs` input bits and a list of gates in topological order, the last gate being the output.); `MIPRE.SAT.Circuit.WellFormed` (Well-formedness (`sec:ar-tms`): every gate reads earlier gates and existing inputs, fan-out is at most two, the output gate is read by no…); `MIPRE.SAT.Circuit.eval` (The output of `C` on the input bits `x`: the value of the last gate (`false` for the empty circuit).); `MIPRE.SAT.Circuit.evalBits` (The output of `C` on a bit string (missing bits read `false`).); `MIPRE.SAT.Circuit.fanout` (The number of wires leaving gate `u`.); `MIPRE.SAT.Circuit.instSizedEncoding` (Circuits as data: the pair of the input count and the gate list.); `MIPRE.SAT.Circuit.size` (The number of gates: the paper's size parameter.); `MIPRE.SAT.Circuit.valueAt` (The value of gate `g` of `C` on the input bits `x`: the gate evaluated on the values of the earlier gates (a gate beyond the list reads as…); `MIPRE.SAT.Gate` (A gate: an input bit, a constant, or a binary/unary gate on the values of earlier gates, named by their positions in the gate list.); `MIPRE.SAT.Gate.eval` (The value of a gate given the input bits `x` and the values `vals` of the earlier gates (a missing reference reads `false`).); `MIPRE.SAT.Gate.instSizedEncoding`; `MIPRE.SAT.Gate.ofData?` (Decoding gates.); `MIPRE.SAT.Gate.refs` (The gates a gate reads, with multiplicity.); `MIPRE.SAT.Gate.toData` (Gates as data: a tag and a payload.); and -12 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ofData?_toData`, `length_bitsOfNat`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Circuit` (`MIPRE/Foundations/SAT/Circuit.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Circuit.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Circuit.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B

/-!
# Boolean circuits as data

The circuits of the succinct Cook–Levin theorem (`planning/succinct-cook-levin.md`, S0;
`answer_reduction.tex` `sec:ar-tms`): a circuit is a list of gates in topological order,
each gate reading input bits or the values of earlier gates, the last gate being the output.
Fan-in is at most two by the shape of the gates; fan-out at most two and a terminal output
gate are the well-formedness conditions (`Circuit.WellFormed`) that the arithmetization of
the Tseitin formula needs for its individual-degree bound (`prop:tseitin-arith-degree`).
The gate count is the paper's size parameter `s`. Circuits are first-order data with a
`SizedEncoding`, so that a program of the ambient model can output one
(`MIPRE.SAT.SuccinctCookLevin.describe`).
-/

namespace MIPRE.SAT

open Cost

/-- A gate: an input bit, a constant, or a binary/unary gate on the values of earlier
gates, named by their positions in the gate list. -/
inductive Gate where
  | input (i : ℕ)
  | const (b : Bool)
  | and (u v : ℕ)
  | or (u v : ℕ)
  | not (u : ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace Gate

/-- The gates a gate reads, with multiplicity. -/
def refs : Gate → List ℕ
  | input _ => []
  | const _ => []
  | and u v => [u, v]
  | or u v => [u, v]
  | not u => [u]

/-- The value of a gate given the input bits `x` and the values `vals` of the earlier gates
(a missing reference reads `false`). -/
def eval (x : ℕ → Bool) (vals : List Bool) : Gate → Bool
  | input i => x i
  | const b => b
  | and u v => vals.getD u false && vals.getD v false
  | or u v => vals.getD u false || vals.getD v false
  | not u => !(vals.getD u false)

/-- Gates as data: a tag and a payload. -/
def toData : Gate → Data
  | input i => .cons (.ofNat 0) (encode i)
  | const b => .cons (.ofNat 1) (encode b)
  | and u v => .cons (.ofNat 2) (encode (u, v))
  | or u v => .cons (.ofNat 3) (encode (u, v))
  | not u => .cons (.ofNat 4) (encode u)

/-- Decoding gates. -/
def ofData? : Data → Option Gate
  | .cons t p =>
    if t = .ofNat 0 then (decode p : Option ℕ).map input
    else if t = .ofNat 1 then (decode p : Option Bool).map const
    else if t = .ofNat 2 then (decode p : Option (ℕ × ℕ)).map fun q => and q.1 q.2
    else if t = .ofNat 3 then (decode p : Option (ℕ × ℕ)).map fun q => or q.1 q.2
    else if t = .ofNat 4 then (decode p : Option ℕ).map not
    else none
  | .nil => none

theorem ofData?_toData (g : Gate) : ofData? g.toData = some g := by
  cases g <;> simp [toData, ofData?, Data.ofNat, SizedEncoding.decode_encode]

instance : SizedEncoding Gate where
  encode := toData
  decode := ofData?
  decode_encode := ofData?_toData

end Gate

/-- A list of gates as data. -/
instance instSizedEncodingListGate : SizedEncoding (List Gate) where
  encode := Data.ofList Gate.toData
  decode := Data.toList? Gate.ofData?
  decode_encode := Data.toList?_ofList Gate.ofData?_toData

/-- A Boolean circuit: `inputs` input bits and a list of gates in topological order, the
last gate being the output. -/
structure Circuit where
  /-- The number of input bits. -/
  inputs : ℕ
  /-- The gates, in an order in which every gate reads only earlier ones. -/
  gates : List Gate
  deriving DecidableEq, Repr, Inhabited

namespace Circuit

/-- The value of gate `g` of `C` on the input bits `x`: the gate evaluated on the values of
the earlier gates (a gate beyond the list reads as the constant `false`). -/
def valueAt (C : Circuit) (x : ℕ → Bool) : ℕ → Bool
  | g => (C.gates.getD g (.const false)).eval x (List.ofFn fun k : Fin g => C.valueAt x k)
  decreasing_by exact k.isLt

/-- The output of `C` on the input bits `x`: the value of the last gate (`false` for the
empty circuit). -/
def eval (C : Circuit) (x : ℕ → Bool) : Bool :=
  if C.gates = [] then false else C.valueAt x (C.gates.length - 1)

/-- The output of `C` on a bit string (missing bits read `false`). -/
def evalBits (C : Circuit) (l : List Bool) : Bool := C.eval fun i => l.getD i false

/-- The number of gates: the paper's size parameter. -/
def size (C : Circuit) : ℕ := C.gates.length

/-- The number of wires leaving gate `u`. -/
def fanout (C : Circuit) (u : ℕ) : ℕ := (C.gates.map fun g => g.refs.count u).sum

/-- Well-formedness (`sec:ar-tms`): every gate reads earlier gates and existing inputs,
fan-out is at most two, the output gate is read by no gate, and there is an output gate. -/
structure WellFormed (C : Circuit) : Prop where
  refs_lt : ∀ (k : ℕ) (h : k < C.gates.length), ∀ u ∈ C.gates[k].refs, u < k
  inputs_lt : ∀ i, Gate.input i ∈ C.gates → i < C.inputs
  fanout_le : ∀ u, C.fanout u ≤ 2
  output_terminal : C.fanout (C.gates.length - 1) = 0
  nonempty : C.gates ≠ []

/-- Circuits as data: the pair of the input count and the gate list. -/
instance : SizedEncoding Circuit where
  encode C := encode (C.inputs, C.gates)
  decode d := (decode d : Option (ℕ × List Gate)).map fun p => ⟨p.1, p.2⟩
  decode_encode C := by
    obtain ⟨n, gs⟩ := C
    simp [SizedEncoding.decode_encode]

end Circuit

/-- The `m`-bit binary encoding of `i` (least significant bit first; `rem:plugging-in-integers`). -/
def bitsOfNat (m i : ℕ) : List Bool := List.ofFn fun k : Fin m => i.testBit k

@[simp] theorem length_bitsOfNat (m i : ℕ) : (bitsOfNat m i).length = m := by
  simp [bitsOfNat]

end MIPRE.SAT


