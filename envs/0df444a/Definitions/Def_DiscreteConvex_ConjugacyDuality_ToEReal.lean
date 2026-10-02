-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
-- name    : DiscreteConvex_ConjugacyDuality_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:25.47352+00:00
-- url     : https://prove2.me/theorems/024d2974-b767-4898-83ff-30bf9ed6c2af
-- title:
--   Embedding R-cup-infinity into R-cup-plusminus-infinity
-- statement:
--   The canonical embedding $\mathbb R \cup \{+\infty\} \hookrightarrow \mathbb R \cup \{\pm\infty\}$, sending $+\infty \mapsto +\infty$ and real values to themselves.
--
--   (Supporting notion throughout Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8 (supporting notion)

import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, used throughout the discrete Legendre-Fenchel transform
(Murota, *Discrete Convex Analysis*, SIAM 2003, Chapter 8), in
`DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The canonical embedding `WithTop ℝ → EReal` (`EReal = WithBot (WithTop ℝ)`), sending
`⊤ ↦ ⊤` and `(r:ℝ) ↦ (r:EReal)`. -/
def ToEReal (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.ConjugacyDuality


