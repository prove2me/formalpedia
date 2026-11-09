-- Prove2me | Definitions.Def_AgnosticTNS_SeqIndex
-- name    : AgnosticTNS_SeqIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:15.438719+00:00
-- url     : https://prove2.me/theorems/07af168f-768f-4b6f-ac9c-419109960ba7
-- title:
--   Instance of the sequence learner
-- statement:
--   The inputs of Algorithm 1: a graph $G$ on $[n]$, a learning sequence for $G$, the local dimension $d$, the bond bound $\chi$, the accuracy $\epsilon$ and the overlap bound $\vartheta$ as exact rationals, and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1, p.19; Theorem 3.6, p.23

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **An instance of the sequence learner**, the inputs of Algorithm 1, p.19, for Theorem 3.6,
Proposition 3.10 and Corollary 3.7 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the graph `G` on `[n]`, a learning sequence, `d`, `χ`,
`ε` and `ϑ` as exact rationals, and `k_δ = ⌈log₂(1/δ)⌉`. -/
structure SeqIndex where
  n : ℕ
  G : SimpleGraph (Fin n)
  Ls : LearningSequence n
  d : ℕ
  χ : ℕ
  ε : ℚ
  ϑ : ℚ
  kδ : ℕ

end AgnosticTNS


