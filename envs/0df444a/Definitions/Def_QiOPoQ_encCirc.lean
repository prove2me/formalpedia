-- Prove2me | Definitions.Def_QiOPoQ_encCirc
-- name    : QiOPoQ_encCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:14.040202+00:00
-- url     : https://prove2.me/theorems/eaa1b591-0f7b-43fb-8cf6-fd2cfc113a55
-- title:
--   The classical description of a circuit and its decoding
-- statement:
--   Circuits are "specified by a classical description". The description records in unary, each number closed by a $0$, the values $n_{\mathrm{in}}$, $n_{\mathrm{anc}}$, $n_{\mathrm{out}}$, the output wires, the gate count, and for each gate occurrence its gate index and its wires. Decoding returns the circuit with a given description, and nothing on a string that describes no circuit.
--
--   The description is injective, because each field is self-delimiting and the gate index determines the number of wires. Because the numbers are in unary, its length is polynomially related to the gate count and width (for a fixed gate set), as p.13 requires: a polynomial-time generator can only produce polynomial-size circuits.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13 ("specified by a classical description")

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_Circ

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

variable {G : GateSet}

/-- The code of a gate occurrence: the gate index, then its wires, each in unary (`encNat`). -/
def encGate {W : ℕ} (g : Σ i : Fin G.k, Fin (G.arity i) ↪ Fin W) : Str :=
  encNat g.1.val ++ (List.ofFn fun j => encNat (g.2 j).val).flatten

/-- **The classical description of a circuit** (p.13: "quantum circuits as being specified by a
classical description"): `n_in`, `n_anc`, `n_out`, the output wires, the gate count, then each
gate occurrence. **Formalization Note.** Every field is a self-delimiting `encNat` code and the
number of wires of a gate is determined by its index, so `encCirc` is injective; the length is
polynomial in the gate count and width, as p.13 requires of a description. -/
def encCirc (C : Circ G) : Str :=
  encNat C.nin ++ encNat C.nanc ++ encNat C.out.length ++
    (C.out.map fun w => encNat w.val).flatten ++ encNat C.gates.length ++
    (C.gates.map encGate).flatten

open Classical in
/-- Decoding of circuit descriptions: `some C` when `s = encCirc C`, `none` when `s` describes
no circuit over `G`. -/
noncomputable def decCirc (G : GateSet) (s : Str) : Option (Circ G) :=
  if h : ∃ C : Circ G, encCirc C = s then some h.choose else none

end QiOPoQ


