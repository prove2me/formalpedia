-- Prove2me | Definitions.Def_ConstrSOSP_Circuit_app
-- name    : ConstrSOSP_Circuit_app
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:37.337293+00:00
-- url     : https://prove2.me/theorems/ba60ded9-bb00-4b59-bd07-e6798ec8440b
-- title:
--   A circuit as a map $[2^n]\to[2^n]$
-- statement:
--   A circuit $C$ with $n$ inputs acts on nodes: $C(v)$ writes $v\in[2^n]$ as $n$ bits, evaluates the circuit and reads the output bits back as a node. On a well-formed circuit, $C(v)\in[2^n]$ for every $v\in[2^n]$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.1–4.2, pp.17–18

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_nodeOf
import Definitions.Def_ConstrSOSP_nodeBits

namespace ConstrSOSP

/-- **A circuit as a map `[2ⁿ] → [2ⁿ]`** (arXiv:2604.02285, 2 Nov 2026, Definitions 4.1 and 4.2,
pp.17–18: "Boolean circuits p, g : [2^n] → [2^n]", "Boolean circuit C : [2^n] → [2^n]").

`C.app v` writes the node `v` as `n` bits (`nodeBits`), evaluates the circuit, and reads the
output bits back as a node (`nodeOf`). On a well-formed circuit and `v ∈ {1, …, 2ⁿ}` the value
lies in `{1, …, 2ⁿ}`. -/
def Circuit.app (C : Circuit) (v : ℕ) : ℕ :=
  nodeOf (C.eval (nodeBits C.n v))

end ConstrSOSP


