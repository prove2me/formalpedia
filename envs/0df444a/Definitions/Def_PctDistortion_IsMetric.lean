-- Prove2me | Definitions.Def_PctDistortion_IsMetric
-- name    : PctDistortion_IsMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:08.332096+00:00
-- url     : https://prove2.me/theorems/fac4b4ef-fe92-47cb-acc7-c7fc9adacccf
-- title:
--   Voter–candidate metrics and consistency with the rankings
-- statement:
--   A **metric** is a function $d:V\times C\to\mathbb R_{\ge 0}$ satisfying the quadrilateral inequality
--   $$d(v,c)\le d(v,c')+d(v',c')+d(v',c)\qquad\text{for all } v,v'\in V,\ c,c'\in C.$$
--   By Goel et al. this is exactly the condition for $d$ to extend to a pseudometric on $V\cup C$.
--
--   A metric $d$ is **consistent** with the profile $\vec\succ$ of an election, written $d\sim\vec\succ$, if $d(v,c)\le d(v,c')$ for every voter $v$ and candidates $c,c'$ with $c\succ_v c'$.
--
--   Consistent metrics are the hidden cost structures over which distortion takes its worst case.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion

/-- A **metric** in the voter–candidate form: `d : V → C → ℝ` with nonnegative values that
satisfies the quadrilateral inequality `d(v, c) ≤ d(v, c') + d(v', c') + d(v', c)` for all voters
`v, v'` and candidates `c, c'`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8: "We specify voter–candidate distances by a function d : V × C → R≥0 satisfying the
quadrilateral inequality d(v, c) ≤ d(v, c′) + d(v′, c′) + d(v′, c) for all v, v′ ∈ V and
c, c′ ∈ C. … We refer to these distance functions as metrics." -/
def IsMetric {V C : Type} (d : V → C → ℝ) : Prop :=
  (∀ v c, 0 ≤ d v c) ∧ ∀ v v' c c', d v c ≤ d v c' + d v' c' + d v' c

/-- A metric `d` is **consistent** with the ranking profile of `E` (`d ∼ ≻⃗`):
`d(v, c) ≤ d(v, c')` whenever `c ≻_v c'`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8: "we say that a metric d : V × C → R≥0 is consistent with ≻⃗, and write d ∼ ≻⃗, if
d(v, c) ≤ d(v, c′) for all v ∈ V and c, c′ ∈ C such that c ≻v c′." -/
def Consistent {V C : Type} (E : Election V C) (d : V → C → ℝ) : Prop :=
  ∀ v c c', E.prefers v c c' → d v c ≤ d v c'

end PctDistortion


