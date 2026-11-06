-- Prove2me | Definitions.Def_ConstrSOSP_Circuit
-- name    : ConstrSOSP_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:21.195322+00:00
-- url     : https://prove2.me/theorems/041aa113-a5e4-42b5-b8d4-6a900f38dd72
-- title:
--   Boolean circuit with $n$ inputs and $n$ outputs
-- statement:
--   A **Boolean circuit** $C:\{0,1\}^n\to\{0,1\}^n$ is given by its number $n$ of inputs (equal to its number of outputs), a list of gates in topological order, and the list of its output wires.
--
--   Circuits are the inputs of LocalOpt and Iter, the problems that define the class PLS in this paper.
--
--   **Formalization Note** Well-formedness is the separate predicate `Circuit.WF`.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_Gate

namespace ConstrSOSP

/-- **A Boolean circuit with `n` inputs and `n` outputs** (arXiv:2604.02285, 2 Nov 2026, §4.1,
p.17: "a Boolean circuit C : {0, 1}^d → {0, 1}^d with d inputs and d outputs").

`n` is the number of inputs (and of outputs), `gates` the gates in topological order (gate `k`
writes the wire `n + k`), and `outs` the list of output wires.

**Formalization Note** Well-formedness (every gate reads earlier wires, exactly `n` outputs, every
output names an existing wire) is the separate predicate `Circuit.WF`. -/
structure Circuit where
  n : ℕ
  gates : List Gate
  outs : List ℕ

end ConstrSOSP


