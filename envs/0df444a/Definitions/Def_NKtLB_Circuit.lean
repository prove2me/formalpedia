-- Prove2me | Definitions.Def_NKtLB_Circuit
-- name    : NKtLB_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:02:40.087679+00:00
-- url     : https://prove2.me/theorems/af105499-3e0e-49c3-95ba-5135291f96b6
-- title:
--   Boolean circuits and their codes
-- statement:
--   A **Boolean circuit** is a straight-line list of gates together with a list of output wires. Each gate is an input bit $x_i$, a constant, or the NOT, AND or OR of earlier wires. On input $x$ the circuit computes the values of its output wires, a bit string. The **code** of a circuit is a uniquely decodable binary string, and "an algorithm outputs a Boolean circuit" means that it outputs this code.
--
--   **Formalization Note** The paper fixes no circuit encoding. A wire index out of range reads $0$; such circuits compute nothing that well-formed circuits do not.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 101, p.68

import Mathlib
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB

/-- **Gates of a Boolean circuit** (for Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 101, p.68): an input bit, a constant, or a
NOT/AND/OR of earlier wires (wire `i` is the value of gate `i`). -/
inductive Gate
  | inp (i : ℕ)
  | const (b : Bool)
  | neg (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)

/-- The value of a gate on input `x`, given the values `vals` of the earlier wires (an index out
of range reads `false`). -/
def Gate.eval (g : Gate) (x vals : List Bool) : Bool :=
  match g with
  | Gate.inp i => x.getD i false
  | Gate.const b => b
  | Gate.neg i => !(vals.getD i false)
  | Gate.and i j => vals.getD i false && vals.getD j false
  | Gate.or i j => vals.getD i false || vals.getD j false

/-- **Multi-output Boolean circuits** (Lemma 101, p.68: "outputs a Boolean circuit that computes a
function `H : {0,1}^n → {0,1}^{O(log l)}`"): a straight-line list of gates and a list of output
wires. -/
structure Circuit where
  gates : List Gate
  outs : List ℕ

/-- The wire values on input `x`. -/
def Circuit.wires (C : Circuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- The function computed: the values of the output wires. -/
def Circuit.eval (C : Circuit) (x : List Bool) : List Bool :=
  C.outs.map (fun o => (C.wires x).getD o false)

/-- Binary representation, most significant bit first. -/
def binRep (i : ℕ) : List Bool := (Nat.bits i).reverse

/-- The code of a gate. -/
def Gate.code (g : Gate) : List Bool :=
  match g with
  | Gate.inp i => tupleEnc [[false, false], binRep i]
  | Gate.const b => tupleEnc [[false, true], [b]]
  | Gate.neg i => tupleEnc [[true, false], binRep i]
  | Gate.and i j => tupleEnc [[true, true, false], binRep i, binRep j]
  | Gate.or i j => tupleEnc [[true, true, true], binRep i, binRep j]

/-- **The code of a circuit**, the string an algorithm outputs when it "outputs a Boolean
circuit".

**Formalization Note.** The paper fixes no circuit encoding; this one is uniquely decodable and
of size linear in the circuit description. -/
def Circuit.encode (C : Circuit) : List Bool :=
  tupleEnc [tupleEnc (C.gates.map Gate.code), tupleEnc (C.outs.map binRep)]

end NKtLB


