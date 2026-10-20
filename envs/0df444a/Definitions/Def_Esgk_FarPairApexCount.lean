-- Prove2me | Definitions.Def_Esgk_FarPairApexCount
-- name    : Esgk_FarPairApexCount
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:03:00.742798+00:00
-- url     : https://prove2.me/theorems/4fe2bcfe-d255-4b4d-8bb2-44ebd211a6e8
-- title:
--   Ordered pairs at distance greater than a threshold
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane and a real number $s$, `FarOrderedPairs p s` is the set of ordered pairs of distinct indices whose points are farther apart than $s$:
--
--   $$
--   F_p(s)=\{\,(a,b):\ a\ne b,\ |p_a-p_b|>s\,\}.
--   $$
--
--   Apex-counting arguments bound the size of this set from above and from below.
--
--   **Formalization Note** The set is a `Finset (Fin n × Fin n)`; each unordered pair is counted in both orders.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Foundation

namespace Esgk

open EuclideanGeometry
variable {n : ℕ}

noncomputable def FarOrderedPairs (p : Config n) (s : ℝ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ s < dist (p ab.1) (p ab.2))

end Esgk


