-- Prove2me | Definitions.Def_BaconThesis_Collective_levi
-- name    : BaconThesis_Collective_levi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:17.143668+00:00
-- url     : https://prove2.me/theorems/b56bcba0-c156-4bc2-8e11-5c1143b3cfe3
-- title:
--   Levi-Civita symbol $\varepsilon_{\alpha\beta\gamma}$
-- statement:
--   The **Levi-Civita symbol** on $\{x,y,z\}$: $\varepsilon_{\alpha\beta\gamma}=0$ if two of the indices coincide, $+1$ if $(\alpha,\beta,\gamma)$ is a cyclic permutation of $(x,y,z)$, and $-1$ if it is an anticyclic one. It gives the structure constants of $\mathfrak{su}(2)$ in (8.32).
--
--   **Formalization Note** The indices are the published axis labels `BBPSSW.Distill.Axis`; the six permutations are listed and every other triple gives $0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.32), §8.4, p.114 (PDF p.131)

import Mathlib
import Definitions.Def_BBPSSW_Distill_Axis

open scoped Matrix

namespace BaconThesis.Collective

/-- **The Levi-Civita symbol `ε_{αβγ}` on `{x, y, z}`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.32), §8.4, p.114 (PDF p.131): the structure constants of `su(2)`.

`levi α β γ` is `0` when two indices coincide, `+1` when `(α, β, γ)` is a cyclic permutation of
`(x, y, z)`, and `-1` when it is an anticyclic one.

**Formalization Note.** The labels are the published `BBPSSW.Distill.Axis` (`.x`, `.y`, `.z`);
the six permutations of `(x, y, z)` are listed and every other triple gives `0`. -/
def levi : BBPSSW.Distill.Axis → BBPSSW.Distill.Axis → BBPSSW.Distill.Axis → ℤ
  | .x, .y, .z => 1
  | .y, .z, .x => 1
  | .z, .x, .y => 1
  | .y, .x, .z => -1
  | .x, .z, .y => -1
  | .z, .y, .x => -1
  | _, _, _ => 0

end BaconThesis.Collective


