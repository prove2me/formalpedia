-- Prove2me | Definitions.Def_AvgPHETH_Game
-- name    : AvgPHETH_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:30.972721+00:00
-- url     : https://prove2.me/theorems/3de790e3-150f-4179-a5ba-5c2bc479c25c
-- title:
--   The quantified formula $Q_1y_1\cdots Q_dy_d\,V$
-- statement:
--   For a list of quantifiers $Q_1,\dots,Q_d\in\{\exists,\forall\}$, not necessarily alternating, a length $m$ and a predicate $V$, this is $Q_1y_1\cdots Q_dy_d\,V(y_1,\dots,y_d)$ with $|y_i|=m$. For the empty list it is the value of $V$ on the empty tuple.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.1, p.24 (PDF 26)

import Mathlib

namespace AvgPHETH

/-- The quantified formula `Q₁y₁ ⋯ Q_d y_d V(y₁, …, y_d)` over strings of common length `m`, with an
arbitrary list of quantifiers (`true` is `∃`, `false` is `∀`) (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.1, p.24 (PDF 26)).
`Game [] m V` is `V []`.

**Formalization Note** The quantifiers need not alternate, unlike the published `KarpLiptonOM.Alt`. -/
def Game : List Bool → ℕ → (List (List Bool) → Prop) → Prop
  | [], _, V => V []
  | true :: Qs, m, V => ∃ y : List Bool, y.length = m ∧ Game Qs m (fun ys => V (y :: ys))
  | false :: Qs, m, V => ∀ y : List Bool, y.length = m → Game Qs m (fun ys => V (y :: ys))

end AvgPHETH


