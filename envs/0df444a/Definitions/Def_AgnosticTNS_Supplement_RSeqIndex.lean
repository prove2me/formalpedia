-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_RSeqIndex
-- name    : AgnosticTNS_Supplement_RSeqIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:58.571283+00:00
-- url     : https://prove2.me/theorems/ca78ad35-5193-4780-a748-be9f24c4e8c0
-- title:
--   Instance of the realisable sequence learner (Algorithm 2)
-- statement:
--   An instance of Algorithm 2 consists of the graph $G$ on $[n]$, a learning sequence for $G$, the local dimension $d$, the bond bound $\chi$, optionally an edge-dimension function $w:E\to\mathbb N$ (when the weighted rank bounds (4.42) are used), and $k_\epsilon=\lceil1/\epsilon\rceil$, $k_\delta=\lceil\log_2(1/\delta)\rceil$. Without $w$ the algorithm uses the uniform rank bounds (4.41).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 2, p.33; Theorem 4.8, pp.36–37

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS.Supplement

/-- **An instance of the realisable sequence learner (Algorithm 2)**, p.33, for Theorems 1.3 and 4.8
(pp.4, 36–37) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the graph `G` on `[n]`, a learning sequence,
`d`, `χ`, optionally an edge-dimension function `w` (Theorem 4.8, weighted rank bounds (4.42)), and
`k_ε = ⌈1/ε⌉`, `k_δ = ⌈log₂(1/δ)⌉`.

**Formalization Note** `w = none` runs the algorithm with the uniform rank bounds (4.41). -/
structure RSeqIndex where
  n : ℕ
  G : SimpleGraph (Fin n)
  Ls : LearningSequence n
  d : ℕ
  χ : ℕ
  w : Option (G.edgeSet → ℕ)
  kε : ℕ
  kδ : ℕ

end AgnosticTNS.Supplement


