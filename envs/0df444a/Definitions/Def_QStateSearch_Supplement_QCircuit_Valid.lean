-- Prove2me | Definitions.Def_QStateSearch_Supplement_QCircuit_Valid
-- name    : QStateSearch_Supplement_QCircuit_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:07:46.513693+00:00
-- url     : https://prove2.me/theorems/16da92f6-4d19-40ee-9361-c1d58e2abb68
-- title:
--   Well-formed explicit circuits
-- statement:
--   A circuit is **well formed** if
--
--   1. its input count is at most its wire count and its output wire exists;
--   2. every gate acts on distinct wires, all below the wire count;
--   3. each classical-oracle gate has as many ancillas as query wires, and its ancillas are not input wires (so they start in $|0\rangle$);
--   4. the ancillas of a classical-oracle gate are touched by no other gate.
--
--   Conditions 3 and 4 make a classical-oracle gate a computational-basis measurement of the query register followed by a call to $O$, as Definition 3 requires of the distinguisher's access to a completion.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 6.1, p.16

import Mathlib
import Definitions.Def_QStateSearch_Supplement_QCircuit

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- Well-formedness of an explicit circuit `C`:
1. `inputs ≤ wires` and `output < wires`;
2. every gate acts on distinct wires below `wires` (for `oracle lab c ws`: `c :: ws` has no
   repetition; for `cquery qs anc tgt`: `qs ++ anc ++ [tgt]` has none);
3. each classical-query gate `cquery qs anc tgt` has as many ancillas as query wires, and its
   ancillas are non-input wires (so they start in `|0⟩`);
4. the ancillas of a classical-query gate are touched by no other gate of the circuit.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 6.1, p.16 ("classical access to O, meaning that its query register is measured in the
computational basis before each call to O").

**Formalization Note.** Conditions 3 and 4 make `cquery` a measurement of the query register
followed by a call to `O`: the query bits are copied onto fresh ancillas that are never used
again (deferred measurement), so the call cannot be made coherent. -/
def QCircuit.Valid (C : QCircuit) : Prop :=
  let ws : QGate → List ℕ := fun g => match g with
    | .h i => [i]
    | .s i => [i]
    | .t i => [i]
    | .x i => [i]
    | .cnot i j => [i, j]
    | .oracle _ c qs => c :: qs
    | .cquery qs anc tgt => qs ++ anc ++ [tgt]
  let ancOf : QGate → List ℕ := fun g => match g with
    | .cquery _ anc _ => anc
    | _ => []
  C.inputs ≤ C.wires ∧ C.output < C.wires ∧
  (∀ g ∈ C.gates, (ws g).Nodup ∧ ∀ i ∈ ws g, i < C.wires) ∧
  (∀ qs anc tgt, QGate.cquery qs anc tgt ∈ C.gates →
    anc.length = qs.length ∧ ∀ i ∈ anc, C.inputs ≤ i) ∧
  (∀ i j : Fin C.gates.length, i ≠ j → ∀ a ∈ ancOf (C.gates.get i), a ∉ ws (C.gates.get j))

end QStateSearch.Supplement


