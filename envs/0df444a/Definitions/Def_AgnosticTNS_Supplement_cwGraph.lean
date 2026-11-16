-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_cwGraph
-- name    : AgnosticTNS_Supplement_cwGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:49.344175+00:00
-- url     : https://prove2.me/theorems/dc9d8b89-52df-4d26-87f4-f67c73a8d134
-- title:
--   Cutwidth $\mathrm{cw}(G)$ of a graph
-- statement:
--   The **cutwidth** of $G$ is $\mathrm{cw}(G)=\min_\pi \mathrm{cw}(\pi)$, the minimum over all linear orderings of the vertices.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.1, p.48

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_cwOrd

namespace AgnosticTNS.Supplement

/-- **The cutwidth of a graph** `cw(G) = min_π cw(π)`, Definition 6.1, p.48 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def cwGraph {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf (Set.range (cwOrd G))

end AgnosticTNS.Supplement


