-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_evalCircuit
-- name    : DoublyEffIP_Supplement_evalCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:25:40.752204+00:00
-- url     : https://prove2.me/theorems/daffd112-d77b-496e-a35e-fd984d354670
-- title:
--   Evaluation $C(x)$ of an arithmetic circuit over a ring
-- statement:
--   For a commutative ring $R$ with a distinguished element $\alpha$, a circuit $C$ and inputs $x_0,\dots,x_{n-1}\in R$, the value $C(x)$ is computed wire by wire: the inputs, then each gate in order, where ADD and MULT add and multiply the values on their two wires, a constant gate gives $0$ or $1$, and the generator gate gives $\alpha$. The result is the list of values on the output wires.
--
--   Circuits are evaluated over the presented field $\mathbb F=\mathbb F_p[X]/(f)$ with $\alpha$ the class of $X$.
--
--   **Formalization Note** A reference to a wire that does not exist yet reads $0$; such a wire could be replaced by one constant gate.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definitions 3 and 5 (C(x, ⟨Φ⟩))

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **Evaluating an arithmetic circuit** `C(x)` over a ring — Definitions 3 and 5 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…),
Section 3.2, p.9.

The wire values are the inputs `inp`, followed by the value of each gate in order: `add i j` and
`mul i j` add and multiply the values on wires `i`, `j`; `const b` is `1` or `0`; `gen` is `α`.
The result is the list of values on the output wires.

**Formalization Note.** Evaluated over `F = F_p[X]/(f)` with `α` the class of `X`. A reference to a
wire that does not exist yet reads `0` (a total convention; it can be replaced by a `const false`
gate, so it does not change what circuits of a given size compute up to one gate). -/
def evalCircuit {R : Type*} [CommRing R] (α : R) (C : Circuit) (inp : List R) : List R :=
  let vals := C.gates.foldl (fun vs g => vs ++ [match g with
      | .add i j => vs.getD i 0 + vs.getD j 0
      | .mul i j => vs.getD i 0 * vs.getD j 0
      | .const b => if b then 1 else 0
      | .gen => α]) inp
  C.outputs.map fun o => vals.getD o 0

end DoublyEffIP.Supplement


