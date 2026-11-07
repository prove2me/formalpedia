-- Prove2me | Definitions.Def_StableVotingDistortion_IsPseudometric
-- name    : StableVotingDistortion_IsPseudometric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:59.012906+00:00
-- url     : https://prove2.me/theorems/c7d16e17-91a2-46ae-badc-dc695ef981d3
-- title:
--   Pseudometrics on voters and candidates, and consistency with an election
-- statement:
--   A **pseudometric** on the voters and candidates is a function $d$ on $V\cup C$ satisfying, for all points $x,y,z$:
--
--   1. $d(x,y)\ge 0$, with $d(x,x)=0$;
--   2. $d(x,y)=d(y,x)$;
--   3. $d(x,y)+d(y,z)\ge d(x,z)$.
--
--   It is **consistent** with an election $E$ if $a\succ_v b$ implies $d(v,a)\le d(v,b)$ for every voter $v$ and candidates $a,b$.
--
--   Consistent pseudometrics are the hidden cost structures over which distortion takes its worst case.
--
--   **Formalization Note** The points are `V ⊕ C`, so voters and candidates are tagged. Distinct points may be at distance $0$.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- `d` is a **pseudometric** on the voters and candidates `V ∪ C`, here the sum type `V ⊕ C`:
(1) non-negativity, with `d x x = 0`; (2) symmetry; (3) the triangle inequality.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6: "(1) Non-negativity: d(x, y) ≥ 0 (with equality if x = y). (2) Symmetry:
d(x, y) = d(y, x). (3) Triangle inequality: d(x, y) + d(y, z) ≥ d(x, z)."

**Formalization Note.** `d` is on `V ⊕ C`, so the points are tagged voters and candidates. Distinct
points may be at distance `0`, as in a pseudometric. -/
structure IsPseudometric {V C : Type} (d : V ⊕ C → V ⊕ C → ℝ) : Prop where
  /-- Non-negativity. -/
  nonneg : ∀ x y, 0 ≤ d x y
  /-- Distance zero from a point to itself. -/
  self : ∀ x, d x x = 0
  /-- Symmetry. -/
  symm : ∀ x y, d x y = d y x
  /-- Triangle inequality. -/
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- `d` is **consistent** with the election: `a ≻_v b` implies `d(v, a) ≤ d(v, b)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6: "We say that d is consistent with the election if a ≻v b implies that
d(v, a) ≤ d(v, b) for every voter v and candidates a, b." -/
def Consistent {V C : Type} (E : Election V C) (d : V ⊕ C → V ⊕ C → ℝ) : Prop :=
  ∀ v a b, E.prefers v a b → d (Sum.inl v) (Sum.inr a) ≤ d (Sum.inl v) (Sum.inr b)

end StableVotingDistortion


