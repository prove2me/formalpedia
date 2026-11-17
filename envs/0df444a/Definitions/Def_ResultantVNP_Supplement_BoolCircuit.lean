-- Prove2me | Definitions.Def_ResultantVNP_Supplement_BoolCircuit
-- name    : ResultantVNP_Supplement_BoolCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:56:35.720332+00:00
-- url     : https://prove2.me/theorems/f7e2d7c2-0461-4366-9940-f43c4d8edcc1
-- title:
--   Boolean circuits with $m$ inputs and $s$ gates, and $\#\mathrm{SAT}(C)$
-- statement:
--   A **Boolean circuit** $C$ with $m$ inputs and $s$ gates has fan-in-two AND and OR gates, unary NOT gates and Boolean constants. The gates are listed in topological order, each reading earlier wires (inputs or gates), and the output is the last gate. For $b\in\{0,1\}^m$, $C(b)\in\{0,1\}$ is the output, and
--   $$\#\mathrm{SAT}(C)=\sum_{b\in\{0,1\}^m}C(b)$$
--   is the number of satisfying assignments.
--
--   This is the source problem (Parity Circuit SAT) of Theorem E.1.
--
--   **Formalization Note** The size $s$ counts the gates and not the inputs. The binary code writes $m$ in unary and then lists the gates, so its length is polynomial in $m+s$ and at least $m+s$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Appendix E, p.45

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Inputs

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- A gate of a Boolean circuit: a Boolean constant, a unary NOT, or a fan-in-two AND or OR of two
earlier wires (wires `0, …, m − 1` are the inputs, wire `m + k` is gate `k`). -/
inductive BGate where
  | const (b : Bool)
  | not (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)

/-- A gate reads only wires `< k`. -/
def BGate.ReadsBelow (k : ℕ) : BGate → Prop
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k
  | .or i j => i < k ∧ j < k

/-- The value of a gate, given the values of the earlier wires. -/
def BGate.eval (vals : List Bool) : BGate → Bool
  | .const b => b
  | .not i => !(vals.getD i false)
  | .and i j => vals.getD i false && vals.getD j false
  | .or i j => vals.getD i false || vals.getD j false

/-- Binary code of a gate. -/
def BGate.encode : BGate → Word
  | .const b => encodeNat 0 ++ [b]
  | .not i => encodeNat 1 ++ encodeNat i
  | .and i j => encodeNat 2 ++ encodeNat i ++ encodeNat j
  | .or i j => encodeNat 3 ++ encodeNat i ++ encodeNat j

/-- **Boolean circuits with `m` inputs and `s` gates, and `#SAT`.** The gates are fan-in-two AND
and OR, unary NOT and Boolean constants, in topological order; the output is the last gate.
`#SAT(C) = Σ_{b ∈ {0,1}^m} C(b)` is the number of satisfying assignments.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Appendix E, p.45: "We reduce
from Parity Circuit SAT, which asks whether #SAT(C) = Σ_{b∈{0,1}^m} C(b) is odd for a Boolean
circuit C with m inputs and s gates. We use fan-in-two AND and OR gates, unary NOT gates, and
Boolean constants."

**Formalization Note** `size` is the number `s` of gates (inputs are not gates). The code writes
`m` in unary (`1^m 0`), then the gate list with the published `encodeList`, so its length is at
least `m + s` and at most polynomial in `m + s`: "time polynomial in m + s" is polynomial time in
the code length. -/
structure BoolCircuit where
  m : ℕ
  gates : List BGate
  wf : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]'hk).ReadsBelow (m + k)

/-- The number `s` of gates. -/
def BoolCircuit.size (C : BoolCircuit) : ℕ := C.gates.length

/-- The output `C(b)` on the assignment `b ∈ {0,1}^m` (the value of the last wire). -/
def BoolCircuit.eval (C : BoolCircuit) (b : Fin C.m → Bool) : Bool :=
  (C.gates.foldl (fun vals g => vals ++ [g.eval vals]) (List.ofFn b)).getLastD false

/-- `#SAT(C)`: the number of satisfying assignments. -/
def BoolCircuit.numSat (C : BoolCircuit) : ℕ :=
  (Finset.univ.filter (fun b : Fin C.m → Bool => C.eval b = true)).card

/-- The binary code of the circuit: `1^m 0`, then the gates. -/
def BoolCircuit.encode (C : BoolCircuit) : Word :=
  List.replicate C.m true ++ [false] ++ encodeList BGate.encode C.gates

end Supplement

end ResultantVNP


