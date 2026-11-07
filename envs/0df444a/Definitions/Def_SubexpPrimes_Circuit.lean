-- Prove2me | Definitions.Def_SubexpPrimes_Circuit
-- name    : SubexpPrimes_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:39.30387+00:00
-- url     : https://prove2.me/theorems/5825f43d-2e2c-4186-b9cb-61dc8275a615
-- title:
--   Fan-in-two Boolean circuit
-- statement:
--   A **circuit** is a list of gates, each with two input wires and any one of the sixteen Boolean functions of two bits. Its wires are the input bits and then one wire per gate, and its output is the last wire. Its size is the number of gates.
--
--   **Formalization Note** A gate reading a wire that does not exist yet reads $0$, so every list of gates is a circuit and has no cycle.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), §2.1, p.14; Remark 2.4, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT

/-- **A fan-in-two gate** — Gajulapalli, *Deterministic Construction of Primes in Subexponential
Time* (manuscript, sha256 6ad4d3de…), §2.1, p.14: the indices of the two wires it reads, and any
one of the 16 Boolean functions of two bits. -/
structure Gate where
  /-- first input wire -/
  l : ℕ
  /-- second input wire -/
  r : ℕ
  /-- the Boolean function of the gate -/
  op : Bool → Bool → Bool

/-- **A Boolean circuit**: a list of fan-in-two gates; its size is the number of gates. -/
abbrev Circuit := List Gate

/-- The values of all wires: the input bits, then one wire per gate, in order. A gate reading a
wire that does not exist yet reads `false`, so every list of gates is a circuit and has no cycle. -/
def Circuit.wires (c : Circuit) (x : List Bool) : List Bool :=
  c.foldl (fun w g => w ++ [g.op (w.getD g.l false) (w.getD g.r false)]) x

/-- The output of a circuit: its last wire. -/
def Circuit.eval (c : Circuit) (x : List Bool) : Bool :=
  (c.wires x).getLastD false

/-- The encoding of a circuit: per gate, the two wire indices in unary and the four values of its
function. Its length is `O(s²)` on wires of index `O(s)`, and its form does not affect any bound
below, all of which are polynomial in the length. -/
def Circuit.encode (c : Circuit) : List Bool :=
  Encoding.encodeList (fun g : Gate => Encoding.encodeNat g.l ++ Encoding.encodeNat g.r ++
    [g.op false false, g.op false true, g.op true false, g.op true true]) c

end SubexpPrimes


