-- Prove2me | Definitions.Def_RepellingPairs_IsGoodPair
-- name    : RepellingPairs_IsGoodPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:07.416111+00:00
-- url     : https://prove2.me/theorems/9e70ebfa-106e-4737-99ec-2f34c5824c3c
-- title:
--   Good pairs of points, and bars between points
-- statement:
--   Let $C,C'$ be perfect matchings. $S(x)$ is the boundary segment from $C(x)$ to $C'(x)$ that does not contain $x$, endpoints included. The ordered pair $x,y$ is **good** if:
--
--   1. the chords $(x,C(x))$ and $(y,C(y))$ cross;
--   2. $y$ and $C'(x)$ lie on different sides of the chord $(x,C(x))$, which forces $C(x)\neq C'(x)$;
--   3. $C(y)\in S(x)$ or $C'(y)\in S(x)$.
--
--   Also defined: the number of points strictly inside the $x$-$y$ segment that does not contain $C(x)$; and the relation that a bar lies on the boundary segment between two given points that does not contain a third.
--
--   Good pairs carry the proof of Lemma 11.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.4, pp.11–12

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching

set_option autoImplicit false

namespace RepellingPairs

variable {n : ℕ}

/-- `a` lies on the boundary segment `S` from `u` to `v` that does not contain `x`, endpoints included.
(`S(x)` of p.11 is `InSegment x (C x) (C' x)`; the endpoints are needed because `C(y) = C′(x)` occurs.)
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3.4, p.11. -/
def InSegment (x u v a : Fin n) : Prop :=
  a = u ∨ a = v ∨ CyclicallyOrdered x u a v ∨ CyclicallyOrdered x v a u

/-- The points `p` and `q` lie on different sides of the chord `(u, v)`. -/
def OnDifferentSides (u v p q : Fin n) : Prop :=
  CyclicallyOrdered u p v q ∨ CyclicallyOrdered u q v p

/-- The ordered pair `x, y` is good (p.11): the chords `(x, C(x))` and `(y, C(y))` cross; `y` and `C′(x)` lie
on different sides of `(x, C(x))`, which forces `C(x) ≠ C′(x)`; and `C(y) ∈ S(x)` or `C′(y) ∈ S(x)`. -/
def IsGoodPair (C C' : PerfectMatching n) (x y : Fin n) : Prop :=
  Config.ChordsCross x (C.partner x) y (C.partner y) ∧
    OnDifferentSides x (C.partner x) y (C'.partner x) ∧
    (InSegment x (C.partner x) (C'.partner x) (C.partner y) ∨
      InSegment x (C.partner x) (C'.partner x) (C'.partner y))

/-- The number of points strictly inside the `x`-`y` segment that does not contain `C(x)` (p.12). -/
def segmentCount (C : PerfectMatching n) (x y : Fin n) : ℕ :=
  (Finset.univ.filter fun a =>
    CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x).card

/-- The bar `b̄` lies on the clockwise boundary segment from the point `p` to the point `q`: it is one of
`p̄, (p+1)‾, …, (q-1)‾`. -/
def BarOnClockwiseSegment (p q b : Fin n) : Prop :=
  if p ≤ q then p ≤ b ∧ b < q else p ≤ b ∨ b < q

/-- The bar `b̄` lies on the boundary segment between the points `p` and `q` that does not contain the point
`avoid`: "ī between x and y", "j̄ between C(x) and C′(x)" (p.12). -/
def BarBetween (p q avoid b : Fin n) : Prop :=
  (BarOnClockwiseSegment p q b ∧ Config.onSide p q avoid = false) ∨
    (BarOnClockwiseSegment q p b ∧ Config.onSide q p avoid = false)

end RepellingPairs


