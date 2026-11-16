-- Prove2me | Definitions.Def_QiOPoQ_Supplement_OCirc
-- name    : QiOPoQ_Supplement_OCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:55:27.322938+00:00
-- url     : https://prove2.me/theorems/d617f567-2d18-49f3-a2c9-0a9cb2a36e53
-- title:
--   Quantum circuits with oracle-query gates
-- statement:
--   An oracle circuit is a circuit over the gate set in which some gate occurrences are query gates of a classical oracle: a query gate on $m+1$ distinct wires reads the first $m$ as a query string $q$ and acts as $|q\rangle|t\rangle\mapsto|q\rangle|t\oplus O(q)\rangle$. The description of the circuit does not depend on the oracle. Input, ancilla and output registers are as for ordinary circuits.
--
--   `oEncCirc` is the classical description, in the layout of the published `encCirc`; `OPolySize` is polynomial size of a family.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §5.2, p.25 (C^O_BQP); Figure 8, p.26

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_Circ
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- A gate occurrence of an oracle circuit on `W` wires: a gate of `G` on an ordered tuple of
distinct wires, or an oracle query gate on `m + 1` distinct wires (query register = the first
`m`, target = the last). -/
inductive OGate (G : GateSet) (W : ℕ) where
  | gate (g : Σ i : Fin G.k, Fin (G.arity i) ↪ Fin W)
  | query (m : ℕ) (w : Fin (m + 1) ↪ Fin W)

/-- **Quantum circuits with oracle-query gates (§5.2).** Gheorghiu, Gupte, Havlíček, Liu,
*Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289
(sha256 fe2f9210…), p.25: "For an oracle O, write C^O_BQP for circuits with O-query gates whose
channels relative to O satisfy the condition defining C_BQP"; Figure 8, p.26: "O is a
deterministic classical oracle, although a quantum algorithm may query it in superposition."

As the published `QiOPoQ.Circ` (input wires, ancilla wires, output register; deferred-measurement
form), with gates that are either gates of `G` or query gates. The description of the circuit does
not depend on the oracle; its semantics (`ochan`) does. -/
structure OCirc (G : GateSet) where
  nin : ℕ
  nanc : ℕ
  gates : List (OGate G (nin + nanc))
  out : List (Fin (nin + nanc))
  out_nodup : out.Nodup

variable {G : GateSet}

/-- The code of an oracle-circuit gate: tag `0` and the published gate code, or tag `1`, the query
length and the wires. -/
def encOGate {W : ℕ} : OGate G W → Str
  | .gate g => encNat 0 ++ encGate g
  | .query m w => encNat 1 ++ encNat m ++ (List.ofFn fun j => encNat (w j).val).flatten

/-- The classical description of an oracle circuit, in the layout of the published `encCirc`. -/
def oEncCirc (C : OCirc G) : Str :=
  encNat C.nin ++ encNat C.nanc ++ encNat C.out.length ++
    (C.out.map fun w => encNat w.val).flatten ++ encNat C.gates.length ++
    (C.gates.map encOGate).flatten

open Classical in
/-- Decoding of oracle-circuit descriptions (`none` on a string that describes none). -/
noncomputable def decOCirc (G : GateSet) (s : Str) : Option (OCirc G) :=
  if h : ∃ C : OCirc G, oEncCirc C = s then some h.choose else none

/-- Polynomial size of a family of oracle circuits (gate count and width), as `QiOPoQ.PolySize`. -/
def OPolySize (Cf : ℕ → OCirc G) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (Cf n).gates.length ≤ p.eval n ∧ (Cf n).nin + (Cf n).nanc ≤ p.eval n

end QiOPoQ.Supplement


