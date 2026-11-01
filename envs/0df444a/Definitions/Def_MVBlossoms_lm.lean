-- Prove2me | Definitions.Def_MVBlossoms_lm
-- name    : MVBlossoms_lm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:57.639271+00:00
-- url     : https://prove2.me/theorems/e217d457-96b6-44a0-aff8-f18506a0975e
-- title:
--   Length $l_m$ of a minimum-length augmenting path
-- statement:
--   An **augmenting path** is an alternating path that starts and ends at unmatched vertices. $l_m$ denotes the length of a shortest augmenting path in $G$ with respect to $M$, and $l_m=\infty$ if $G$ has no augmenting path.
--
--   **Formalization Note** The minimum ranges over alternating paths of positive length from an unmatched vertex to an unmatched vertex; the value lies in `ℕ∞`.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 3, p.2016

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_MVBlossoms_IsAltPathFromUnmatched

namespace MVBlossoms

/-- **Length of a minimum-length augmenting path, `l_m`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 3, p.2016:
"Throughout, lm will denote the length of a minimum-length augmenting path in G; if G has no
augmenting paths, we will assume that lm = ∞." An augmenting path is "an alternating path that
starts and ends at unmatched vertices" (p.2016).

**Formalization Note.** The infimum in `ℕ∞` of the lengths of alternating paths
(`IsAltPathFromUnmatched`) of positive length whose end vertex is also unmatched; `⊤` when there
is none. Positive length excludes the trivial path at an unmatched vertex. -/
noncomputable def lm {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : ℕ∞ :=
  ⨅ (f : V) (g : V) (p : G.Walk f g) (_ : IsAltPathFromUnmatched M p)
    (_ : BergeMatching.Core.IsNeutral M g) (_ : 0 < p.length), (p.length : ℕ∞)

end MVBlossoms


