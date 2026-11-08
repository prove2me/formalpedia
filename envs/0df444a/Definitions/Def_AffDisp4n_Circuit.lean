-- Prove2me | Definitions.Def_AffDisp4n_Circuit
-- name    : AffDisp4n_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:32.259308+00:00
-- url     : https://prove2.me/theorems/afaaf971-a7eb-436c-ae54-4e928d93fddd
-- title:
--   $B_2$-circuit on $n$ inputs
-- statement:
--   A **$B_2$-circuit on $n$ inputs** is a fan-in-two Boolean circuit over the full binary basis whose input vertices are the variables $X_1, \dots, X_n$ and the constants $0, 1$. Each gate has two ordered incoming wires, which may come from the same vertex, and is labelled by one of the sixteen operations $\{0,1\}^2 \to \{0,1\}$. Fan-out is unrestricted. The **size** $|C|$ is the number of gates.
--
--   This is the circuit model of Theorem 1.1 and Theorem 4.1.
--
--   **Formalization Note** The gates are listed in a topological order, which every acyclic circuit has. The output is a constant or a literal of any variable or gate (the paper allows a constant or a literal, p.13), and it need not have outdegree zero. Gates the output does not depend on are allowed. These circuits include the paper's, with the same size, so a lower bound for them implies the paper's.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, pp.12–13

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic

namespace AffDisp4n

/-- A **B₂-circuit on `n` inputs** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, pp.12–13): a straight-line B₂-circuit whose inputs are
the variables `X₁, …, Xₙ` (indexed by `Fin n`). Its size `|C|` is `C.size`, the number of gates.
Constants and variables are free.

**Formalization Note** Every fan-in-two acyclic circuit has a topological order of its gates, so
listing them in that order loses nothing. The paper designates one gate of outdegree zero as the
output, and allows the output to be a constant or a literal (p.13). Here the output may be a constant
or a literal of any variable or gate, and no gate needs to reach it. This admits more circuits, so a
lower bound over this class implies the paper's. -/
abbrev Circuit (n : ℕ) : Type := Acyclic (Fin n)

end AffDisp4n


