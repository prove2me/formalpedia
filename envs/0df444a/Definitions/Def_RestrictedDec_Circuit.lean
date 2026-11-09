-- Prove2me | Definitions.Def_RestrictedDec_Circuit
-- name    : RestrictedDec_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:58.283935+00:00
-- url     : https://prove2.me/theorems/89d78298-be62-46d2-b291-6571ab7122b6
-- title:
--   Multi-output Boolean circuits and their descriptions
-- statement:
--   A **circuit** is a straight-line program of NAND gates. On an input $x\in\{0,1\}^\ell$ its wires are $x_1,\dots,x_\ell$ followed by one wire per gate, gate $(a,b)$ computing the NAND of wires $a$ and $b$; the output is the list of the designated output wires. Its **description** is a canonical bit-string code of the gate list and the output list, and a string is an admissible description exactly when it is the code of a circuit.
--
--   These are the post-processing functions $g$ of the observation classes $\mathcal F_q=\{g\circ q\}$.
--
--   **Formalization Note** A reference to a wire that does not yet exist reads $0$, so every gate list is a circuit; constants are available. The size of a circuit is the length of its description.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 (g supplied as an admissible polynomial-size circuit); §2.1, p.13 (the game checks descriptions)

import Mathlib
import Definitions.Def_BeyondDS_tup
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- A **multi-output Boolean circuit** in straight-line form: on an input `x ∈ {0,1}^ℓ` the wires
are `x₁, …, x_ℓ` followed by one wire per gate; gate `(a, b)` is the NAND of wires `a` and `b`
(numbered from `0`), and the output is the list of the wires named in `outs`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 ("g is supplied as
an admissible polynomial-size circuit").

**Formalization Note.** A wire index that does not exist yet reads `0`, so every gate list is a
circuit (constants are available as NANDs of the missing wire). The size of a circuit is the
length of its description; the adversary's outputs are polynomially bounded, hence so are its
circuits. -/
structure Circuit where
  gates : List (ℕ × ℕ)
  outs : List ℕ

/-- The value of a circuit on an input bit string. -/
def Circuit.eval (C : Circuit) (input : Str) : Str :=
  let wires := C.gates.foldl
    (fun ws g => ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]) input
  C.outs.map fun o => wires.getD o false

/-- The description (code) of a circuit: `tup` of its gates (pairs of unary wire indices) and of
its output wires. -/
def Circuit.code (C : Circuit) : Str :=
  BeyondDS.tup [BeyondDS.tup (C.gates.map fun g => BeyondDS.tup [encNat g.1, encNat g.2]),
    BeyondDS.tup (C.outs.map encNat)]

/-- The parser of circuit descriptions: a string is **admissible** exactly when it is the code of
a circuit (the effective syntax of p.12), and then it denotes that circuit. -/
def decCircuit (d : Str) : Option Circuit :=
  let fs := BeyondDS.untup d
  let C : Circuit :=
    { gates := (BeyondDS.untup (fs.getD 0 [])).map fun g =>
        let h := BeyondDS.untup g
        (BeyondDS.decNat (h.getD 0 []), BeyondDS.decNat (h.getD 1 []))
      outs := (BeyondDS.untup (fs.getD 1 [])).map BeyondDS.decNat }
  if C.code = d then some C else none

end RestrictedDec


