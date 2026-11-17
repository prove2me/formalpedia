-- Prove2me | Definitions.Def_ResultantVNP_Supplement_CFCircuit
-- name    : ResultantVNP_Supplement_CFCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:56:11.203143+00:00
-- url     : https://prove2.me/theorems/8fbd138f-a508-4cae-bc8b-5fd9bc6950f3
-- title:
--   Integer constant-free arithmetic circuits in one variable
-- statement:
--   An **integer constant-free arithmetic circuit** has the inputs $x$ and $1$. Its gates add, subtract or multiply the values of two earlier nodes, and earlier values may be reused. It computes a polynomial in $\mathbb Z[x]$ (the value of its last node). Constants such as $0,2,3$ are built from $1$. Its **size** is the number of gates. Circuits are written in binary by listing their nodes.
--
--   These circuits represent the polynomials of the univariate resultant-sign problems of Theorem E.1.
--
--   **Formalization Note** A circuit is a nonempty straight-line program in which every gate reads only earlier positions. The leaves $x$ and $1$ are not counted in the size.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Appendix E, p.45

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Inputs

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- A node of an integer constant-free arithmetic circuit: the input `x`, the input `1`, or a gate
adding, subtracting or multiplying the values of two earlier nodes (referred to by position). -/
inductive CFNode where
  | x
  | one
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)

/-- A gate at position `k` reads only positions `< k`. -/
def CFNode.ReadsBelow (k : ℕ) : CFNode → Prop
  | .add i j => i < k ∧ j < k
  | .sub i j => i < k ∧ j < k
  | .mul i j => i < k ∧ j < k
  | _ => True

/-- Gates (as opposed to the inputs `x` and `1`). -/
def CFNode.isGate : CFNode → Bool
  | .add _ _ => true
  | .sub _ _ => true
  | .mul _ _ => true
  | _ => false

/-- The polynomial at a node, given the values of the earlier nodes. -/
noncomputable def CFNode.eval (vals : List (Polynomial ℤ)) : CFNode → Polynomial ℤ
  | .x => Polynomial.X
  | .one => 1
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .sub i j => vals.getD i 0 - vals.getD j 0
  | .mul i j => vals.getD i 0 * vals.getD j 0

/-- Binary code of a node. -/
def CFNode.encode : CFNode → Word
  | .x => encodeNat 0
  | .one => encodeNat 1
  | .add i j => encodeNat 2 ++ encodeNat i ++ encodeNat j
  | .sub i j => encodeNat 3 ++ encodeNat i ++ encodeNat j
  | .mul i j => encodeNat 4 ++ encodeNat i ++ encodeNat j

/-- **Integer constant-free arithmetic circuits** (straight-line programs) in one variable `x`: the
inputs are `x` and `1`, the gates are addition, subtraction and multiplication of two earlier
values, values may be reused, and the output is the last node. The circuit computes a polynomial in
`ℤ[x]`; its size is the number of gates.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Appendix E, p.45: "An
integer constant-free arithmetic circuit has inputs x and 1 and gates for addition, subtraction, and
multiplication. It computes a polynomial in ℤ[x]; constants such as 0, 2, and 3 are constructed
from 1."

**Formalization Note** A nonempty list of nodes in topological order; leaves (`x`, `1`) are not
counted in the size. The binary code lists the nodes with the published `encodeList`. -/
structure CFCircuit where
  nodes : List CFNode
  nonempty : nodes ≠ []
  wf : ∀ (k : ℕ) (hk : k < nodes.length), (nodes[k]'hk).ReadsBelow k

/-- The polynomial computed by the circuit (at its last node). -/
noncomputable def CFCircuit.value (C : CFCircuit) : Polynomial ℤ :=
  (C.nodes.foldl (fun vals nd => vals ++ [nd.eval vals]) []).getLastD 0

/-- The size: the number of gates. -/
def CFCircuit.size (C : CFCircuit) : ℕ :=
  C.nodes.countP CFNode.isGate

/-- The binary code of the circuit. -/
def CFCircuit.encode (C : CFCircuit) : Word :=
  encodeList CFNode.encode C.nodes

end Supplement

end ResultantVNP


