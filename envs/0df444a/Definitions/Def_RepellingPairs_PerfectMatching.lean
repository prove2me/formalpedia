-- Prove2me | Definitions.Def_RepellingPairs_PerfectMatching
-- name    : RepellingPairs_PerfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:52.913939+00:00
-- url     : https://prove2.me/theorems/371bacec-17eb-4a09-a930-9b6bfdcbbdd0
-- title:
--   Perfect matchings on the boundary points
-- statement:
--   A **perfect matching** on $n$ points is a fixed-point-free involution $x\mapsto C(x)$. Its configuration has each chord $(x,C(x))$ once. This is the special case of Lemma 11, where the chords do not share endpoints.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.4, p.11

import Mathlib
import Definitions.Def_RepellingPairs_Config

set_option autoImplicit false

namespace RepellingPairs

/-- A perfect matching on the points `Fin n`, the special case of Lemma 11 in which "the chords give a
perfect matching on all points on the boundary" (p.11). `partner x` is the point `C(x)` matched to `x`.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3.4, p.11. -/
structure PerfectMatching (n : ℕ) where
  /-- The point to which `x` is matched. -/
  partner : Fin n → Fin n
  involutive : Function.Involutive partner
  ne_self : ∀ x, partner x ≠ x

/-- The configuration of a perfect matching: each chord `(x, C(x))` once. -/
def PerfectMatching.config {n : ℕ} (C : PerfectMatching n) : Config n :=
  (Finset.univ.image fun x => s(x, C.partner x)).val

end RepellingPairs


