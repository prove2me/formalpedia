-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_ToEReal
-- name    : DiscreteConvex_MConvexSets_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:36.081067+00:00
-- url     : https://prove2.me/theorems/296413ef-e403-412f-bae4-94078f57f43f
-- title:
--   Embedding R-cup-infinity into R-cup-plusminus-infinity
-- statement:
--   The canonical embedding $\mathbb R \cup \{+\infty\} \hookrightarrow \mathbb R \cup \{\pm\infty\}$, sending $+\infty \mapsto +\infty$ and real values to themselves. Used to compare submodular- and supermodular-side quantities on a common scale in Theorem 4.17.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111 (supporting Theorem 4.17)

import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, used to compare submodular- and supermodular-side
quantities on a common scale in Theorem 4.17 (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.111), in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- The canonical embedding `WithTop ℝ → EReal` (`EReal = WithBot (WithTop ℝ)`), sending
`⊤ ↦ ⊤` and `(r:ℝ) ↦ (r:EReal)`. -/
def ToEReal (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.MConvexSets


