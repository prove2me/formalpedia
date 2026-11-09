-- Prove2me | Definitions.Def_TermCycDich_encodeOutcome
-- name    : TermCycDich_encodeOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:52.820865+00:00
-- url     : https://prove2.me/theorems/5c278d44-16fd-4229-b9cb-0452e3e33316
-- title:
--   Binary code of an outcome of Theorem 1.2
-- statement:
--   The **binary code of an outcome** (for an input on $n$ vertices): "$\mathrm{bidim}>b$" is $00$; a kept vertex set $S$ is $01$ followed by the $n$ membership bits of $S$; a tree-decomposition with tree $T$ on $m$ nodes is $1$, then $m$ in unary ($m$ ones and a zero), the $m^2$ adjacency bits of $T$ row by row, and for each node the $n$ membership bits of its bag.
--
--   For fixed $n$ different outcomes have different codes. It is the output format of the algorithm of Theorem 1.2.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6)

import Mathlib
import Definitions.Def_TermCycDich_Outcome

namespace TermCycDich

open Classical in
/-- The **binary encoding of an outcome** of Theorem 1.2 (for an input with `n` vertices).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6): the algorithm outputs one of three outcomes.

**Formalization Note** `bidimGt ↦ 00`; `keep S ↦ 01` followed by the `n` membership bits of `S`;
`treeDec m T bag ↦ 1`, then `m` in unary (`m` ones and a zero), the `m²` adjacency bits of `T` row
by row, and for each node `t` the `n` membership bits of `bag t`. For fixed `n` the code is
injective. Adjacency bits use classical decidability. -/
noncomputable def encodeOutcome {n : ℕ} : Outcome n → List Bool
  | .bidimGt => [false, false]
  | .keep S => [false, true] ++ (List.finRange n).map (fun i => decide (i ∈ S))
  | .treeDec m T bag =>
      [true] ++ List.replicate m true ++ [false] ++
        (List.finRange m).flatMap (fun s => (List.finRange m).map (fun t => decide (T.Adj s t))) ++
        (List.finRange m).flatMap (fun t => (List.finRange n).map (fun i => decide (i ∈ bag t)))

end TermCycDich


