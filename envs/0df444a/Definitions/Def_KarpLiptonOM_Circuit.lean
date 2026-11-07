-- Prove2me | Definitions.Def_KarpLiptonOM_Circuit
-- name    : KarpLiptonOM_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:12.440196+00:00
-- url     : https://prove2.me/theorems/8ad58881-bc09-451f-bdf9-48f0598c0124
-- title:
--   Boolean circuit with $n$ inputs
-- statement:
--   A **Boolean circuit** with $n$ inputs is a sequence of gates $g_0, g_1, \dots, g_{s-1}$ in which gate $g$ reads only the inputs and the gates before it. Its **size** is the number $s$ of gates, and its value on an input is the value of the last gate.
--
--   **Formalization Note** Gates are constants, NOT, binary AND and binary OR; a circuit with no gate outputs $0$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (circuits with n inputs and at most s gates)

import Mathlib
import Definitions.Def_KarpLiptonOM_Gate

namespace KarpLiptonOM

/-- A Boolean circuit with `n` inputs (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): a list of gates in which gate `g` reads
only inputs and earlier gates (wires `< n + g`). Its size is the number of gates
`C.gates.length`; its output is the last gate. -/
structure Circuit (n : ℕ) where
  /-- the gates, in topological order -/
  gates : List Gate
  /-- gate `g` reads only wires `< n + g` -/
  wf : ∀ (g : ℕ) (hg : g < gates.length), ∀ i ∈ (gates[g]).refs, i < n + g

end KarpLiptonOM


