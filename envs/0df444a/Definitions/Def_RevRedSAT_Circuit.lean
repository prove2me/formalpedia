-- Prove2me | Definitions.Def_RevRedSAT_Circuit
-- name    : RevRedSAT_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:48.011646+00:00
-- url     : https://prove2.me/theorems/c26f5a17-7f26-45de-bce4-4234971e1932
-- title:
--   Boolean circuits of bounded fan-in and their codes
-- statement:
--   A **Boolean circuit** with $p$ input bits, $g$ gates and one output bit (Lemma 4.7, p.33) is a list of gates in topological order. Wires $0,\dots,p-1$ carry the input bits and wire $p+i$ the output of gate $i$; gate $i$ reads a list of wires among the inputs and the earlier gates and applies an arbitrary Boolean function to their values; one wire is the output.
--
--   The circuit has **fan-in at most $d$** if every gate reads at most $d$ wires. Its value on an input assignment $x\in\{0,1\}^p$ is computed gate by gate. Its **code** lists $p$, then each gate as its input wires followed by its truth table, then the output wire.
--
--   **Formalization Note** The truth table of a gate with $r$ inputs has $2^r$ entries; entry $j$ is the value when input $t$ equals bit $t$ of $j$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.7 and its proof, pp.33–34

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- A gate: the list of wires it reads (in order) and the Boolean function it applies to their
values. -/
structure Gate where
  /-- the wires read by the gate, in order -/
  inputs : List ℕ
  /-- the Boolean operation of the gate, applied to the list of input values -/
  op : List Bool → Bool

/-- **A Boolean circuit with one output bit.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.7, p.33: "Let C be a
Boolean circuit with p input bits, g gates, and one output bit, where each gate has at most d
inputs"; proof: "Process the gates in an order in which every gate comes after the gates supplying
its inputs."

Wires `0, …, p − 1` are the input bits; wire `p + i` is the output of gate `i`; `out` is the output
wire.

**Formalization Note** Gates are listed in a topological order (well-formedness requires each gate
to read only inputs and earlier gates); a gate may compute any Boolean function of its inputs. -/
structure Circuit where
  /-- the number `p` of input bits -/
  p : ℕ
  /-- the gates, in topological order -/
  gates : List Gate
  /-- the output wire -/
  out : ℕ

namespace Circuit

/-- The circuit has fan-in at most `d`: gate `i` reads at most `d` wires, all among the inputs and
the gates before it, and the output wire exists. -/
def WellFormed (d : ℕ) (C : Circuit) : Prop :=
  (∀ (i : ℕ) (h : i < C.gates.length),
    (C.gates[i].inputs.length ≤ d) ∧ ∀ v ∈ C.gates[i].inputs, v < C.p + i) ∧
  C.out < C.p + C.gates.length

/-- The values of all wires on the input values `x` (the inputs followed by the gate outputs, gate
by gate). -/
def wireValues (C : Circuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun vals G => vals ++ [G.op (G.inputs.map fun v => vals.getD v false)]) x

/-- The output bit of the circuit on the input assignment `x`. -/
def eval (C : Circuit) (x : Fin C.p → Bool) : Bool :=
  (C.wireValues (List.ofFn x)).getD C.out false

end Circuit

/-- The truth table of a gate: entry `j` is its value when input `t` has the value of bit `t` of `j`. -/
def Gate.table (G : Gate) : List Bool :=
  (List.range (2 ^ G.inputs.length)).map fun j => G.op ((List.range G.inputs.length).map j.testBit)

/-- The code of a gate: its input wires, then its truth table. -/
def encGate (G : Gate) : List Bool := encList encNat G.inputs ++ encList (fun b => [b]) G.table

/-- The code of a circuit: `p`, its gates in order, and its output wire. -/
def encCircuit (C : Circuit) : List Bool :=
  encNat C.p ++ encList encGate C.gates ++ encNat C.out

end RevRedSAT


