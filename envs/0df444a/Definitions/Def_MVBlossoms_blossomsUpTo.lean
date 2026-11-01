-- Prove2me | Definitions.Def_MVBlossoms_blossomsUpTo
-- name    : MVBlossoms_blossomsUpTo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:46:04.202471+00:00
-- url     : https://prove2.me/theorems/a7f93c2e-663b-42c3-b17d-e530be77bd14
-- title:
--   The blossoms of tenacity at most $t$
-- statement:
--   For a number $t$, the family of **blossoms of tenacity at most $t$** consists of the sets $B_{b,s}$ with $s$ an eligible tenacity, $s\le t$, and $b$ a base of a blossom of tenacity $s$ (basal at stage $s$, $\mathrm{tenacity}(b)>s$).
--
--   Statement 4 of Theorem 3 says this family is laminar.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Theorem 3, Statement 4, p.2034; Corollary 5, p.2037

import Mathlib
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_blossom
import Definitions.Def_MVBlossoms_IsBlossomBase

namespace MVBlossoms

/-- **The blossoms of tenacity at most t.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Theorem 3, Statement 4 (p.2034) and
Corollary 5 (p.2037): "the set of blossoms of tenacity at most t".

`blossomsUpTo M t` is the family of the sets `blossom M b s` with `s` an eligible tenacity,
`s ≤ t`, and `b` the base of a blossom of tenacity `s` (`IsBlossomBase M b s`). -/
def blossomsUpTo {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (t : ℕ) : Set (Set V) :=
  {X | ∃ (s : ℕ) (b : V), IsEligible M s ∧ s ≤ t ∧ IsBlossomBase M b s ∧ X = blossom M b s}

end MVBlossoms


