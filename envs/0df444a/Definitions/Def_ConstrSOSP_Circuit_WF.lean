-- Prove2me | Definitions.Def_ConstrSOSP_Circuit_WF
-- name    : ConstrSOSP_Circuit_WF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:31.09535+00:00
-- url     : https://prove2.me/theorems/4ed1ee6d-644e-4d3e-be7d-65eb0ffd1cbf
-- title:
--   Well-formed Boolean circuit
-- statement:
--   A circuit with $n$ inputs is **well formed** when
--
--   1. the $k$-th gate reads only wires with index $< n+k$ (the inputs and earlier gates), so the circuit is acyclic;
--   2. it has exactly $n$ output wires;
--   3. every output wire is an existing wire (index $< n+$ number of gates).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit

namespace ConstrSOSP

/-- **Well-formed circuit** (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: a circuit
`C : {0,1}^d → {0,1}^d` built from ∧, ∨ (fan-in 2) and ¬ (fan-in 1)).

`C.WF` holds iff the `k`-th gate reads only wires `< n + k` (inputs and earlier gates, so the
circuit is acyclic), there are exactly `n` output wires, and every output wire exists
(`< n + number of gates`). -/
def Circuit.WF (C : Circuit) : Prop :=
  (∀ k (hk : k < C.gates.length),
    match C.gates[k] with
    | Gate.andG i j => i < C.n + k ∧ j < C.n + k
    | Gate.orG i j => i < C.n + k ∧ j < C.n + k
    | Gate.notG i => i < C.n + k) ∧
  C.outs.length = C.n ∧ ∀ o ∈ C.outs, o < C.n + C.gates.length

end ConstrSOSP


