-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_ToEReal2
-- name    : DiscreteConvex_CombinatorialC_ToEReal2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:18.317319+00:00
-- url     : https://prove2.me/theorems/cf9cd24c-3047-4c17-a94f-5e527b179123
-- title:
--   Embedding WithTop R into EReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508

import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The canonical embedding `WithTop ℝ → EReal` (`EReal = WithBot (WithTop ℝ)`). -/
def ToEReal2 (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.CombinatorialC


