-- Prove2me | Definitions.Def_PPSLattice_circDepth
-- name    : PPSLattice_circDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:49.942964+00:00
-- url     : https://prove2.me/theorems/66682d08-aa27-44f5-9d79-aa5ad639b7bf
-- title:
--   Depth of a Boolean circuit on $\ell$ inputs
-- statement:
--   For a NAND circuit read on $\ell$ input bits, input wires have depth $0$, a gate has depth one more than the larger depth of its two input wires, and constant wires (wires that do not exist yet) have depth $0$. The depth of the circuit is the largest depth of an output wire. $\mathcal F_{d,\ell}$ consists of the functions on $\ell$ bits computed by circuits of depth $d$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Function Class, p.16; Claim 4.10, p.23

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
set_option autoImplicit false

namespace PPSLattice

/-- The depths of the wires of a circuit on `ℓ` inputs: input wires have depth `0`, and gate `(a, b)`
has depth `1 + max(depth a, depth b)`, where a wire that does not exist yet (a constant) has depth
`0`. -/
def wireDepths (ell : ℕ) (C : RestrictedDec.Circuit) : List ℕ :=
  C.gates.foldl (fun ds g => ds ++ [1 + max (ds.getD g.1 0) (ds.getD g.2 0)])
    (List.replicate ell 0)

/-- The **depth** of a circuit on `ℓ` inputs: the largest depth of an output wire (`0` without
outputs).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Function Class F_{d,ℓ}, p.16 ("functions that take ℓ-bit inputs and can be computed by a
depth-d boolean circuit"); Claim 4.10, p.23 ("depth d_f").

**Formalization Note.** Wires are numbered as in `RestrictedDec.Circuit.eval`: the `ℓ` inputs, then
one wire per gate; the depth therefore depends on the number `ℓ` of inputs. -/
def circDepth (ell : ℕ) (C : RestrictedDec.Circuit) : ℕ :=
  (C.outs.map fun o => (wireDepths ell C).getD o 0).foldr max 0

end PPSLattice


