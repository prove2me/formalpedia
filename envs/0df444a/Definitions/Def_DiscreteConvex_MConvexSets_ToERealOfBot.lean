-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_ToERealOfBot
-- name    : DiscreteConvex_MConvexSets_ToERealOfBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:40.538295+00:00
-- url     : https://prove2.me/theorems/a3c87541-5641-472c-8858-ba7b8fc5317f
-- title:
--   Embedding R-cup-minus-infinity into R-cup-plusminus-infinity
-- statement:
--   The canonical embedding $\mathbb R \cup \{-\infty\} \hookrightarrow \mathbb R \cup \{\pm\infty\}$, sending $-\infty \mapsto -\infty$ and real values to themselves. The supermodular-side counterpart of `ToEReal`.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111 (supporting Theorem 4.17)

import Mathlib

/-!
The embedding `R ∪ {-∞} ↪ R ∪ {±∞}`, used to compare submodular- and supermodular-side
quantities on a common scale in Theorem 4.17 (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.111), in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- The canonical embedding `WithBot ℝ → EReal` (`EReal = WithBot (WithTop ℝ)`), sending
`⊥ ↦ ⊥` and `(r:ℝ) ↦ (r:EReal)`. -/
def ToERealOfBot (v : WithBot ℝ) : EReal :=
  v.map ((↑·) : ℝ → WithTop ℝ)

end DiscreteConvex.MConvexSets


