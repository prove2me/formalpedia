-- Prove2me | Definitions.Def_AffDisp4n_Acyclic
-- name    : AffDisp4n_Acyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:10.616681+00:00
-- url     : https://prove2.me/theorems/6ddeee3f-eb0e-4ecf-a4d6-8b0f480fdd1f
-- title:
--   Straight-line $B_2$-circuit with output literal
-- statement:
--   A **straight-line $B_2$-circuit with inputs $V$** has gates $0, 1, \dots, s-1$, listed in a topological order. Gate $g$ applies an arbitrary operation $\mathrm{op}_g : \mathbb F_2 \times \mathbb F_2 \to \mathbb F_2$ to its two ordered inputs. Any of the sixteen operations of the basis $B_2$ is allowed. Each input is a constant, an input of the circuit, or an earlier gate, and both inputs may be the same. The **output** is a constant, or a literal $t + \varepsilon$ ($\varepsilon \in \mathbb F_2$) of an input or a gate. The **size** is the number $s$ of gates.
--
--   With $V = \{1, \dots, n\}$ this is a fan-in-two Boolean circuit over the full binary basis. With $V$ the parameters and auxiliary variables it is the acyclic part of a fair semi-circuit.
--
--   **Formalization Note** The paper designates "one gate of outdegree zero" as the output, and then allows the output to be a constant or a literal (p.13). Here the output may be any input or gate, and gates that do not reach the output are allowed. Such gates do not change the computed function and only add to the size.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, pp.12–13; §2.3 (ii)–(iii), pp.13–14

import Mathlib
import Definitions.Def_AffDisp4n_Src

namespace AffDisp4n

/-- A **straight-line B₂-circuit with inputs `V`** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, pp.12–13, and the acyclic part of a
fair semi-circuit, §2.3 (ii)–(iii), pp.13–14). The gates `0, …, size − 1` are listed in a topological
order. Gate `g` applies an arbitrary operation `op g : 𝔽₂ → 𝔽₂ → 𝔽₂` (any of the sixteen operations of
B₂) to its two ordered inputs `in₁ g` and `in₂ g`. Each input is a constant, an input or an earlier
gate, and the two may coincide. The output is a constant or a literal `out + outNeg` of an input or a
gate. The size is the number of gates.

**Formalization Note** With `V = Fin n` this is the B₂-circuit of §2.1 (inputs are the variables
`X₁, …, Xₙ` and the constants). "We allow the output to be a constant or a literal" (p.13): the output
is `out` plus the constant `outNeg`, and it may be any gate, not necessarily one of outdegree zero.
Gates that the output does not depend on are allowed; they do not change the computed function and
only increase the size. -/
structure Acyclic (V : Type) where
  /-- the number of gates -/
  size : ℕ
  /-- the operation of each gate (all sixteen maps 𝔽₂ × 𝔽₂ → 𝔽₂ are allowed) -/
  op : Fin size → ZMod 2 → ZMod 2 → ZMod 2
  /-- the first input of gate `g`: a constant, an input, or an earlier gate -/
  in₁ : (g : Fin size) → Src V g.val
  /-- the second input of gate `g`: a constant, an input, or an earlier gate -/
  in₂ : (g : Fin size) → Src V g.val
  /-- the output: a constant, an input, or a gate -/
  out : Src V size
  /-- the output is `out + outNeg`, a literal of `out` -/
  outNeg : ZMod 2

end AffDisp4n


