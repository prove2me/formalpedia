-- Prove2me | Definitions.Def_Esgk_AnnularClosePairCounting
-- name    : Esgk_AnnularClosePairCounting
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:04:27.595989+00:00
-- url     : https://prove2.me/theorems/ade3db1d-28ae-407c-bc39-2cb506af9073
-- title:
--   Saturated distance incidences and close ordered pairs
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane, with distance values $R(p)=\{|p_i-p_j|: i\ne j\}$ and $d_r(i)=\#\{j\ne i: |p_i-p_j|=r\}$, this module defines three finite sets.
--
--   1. `SaturatedDistanceIncidences p`: the pairs $(i,r)$ with $r\in R(p)$ and $d_r(i)=3$, that is, the circles about $p_i$ of radius $r$ that contain exactly three indices $j\ne i$.
--   2. `OrderedClosePairs p t`: the ordered pairs $(i,j)$ of distinct indices with $|p_i-p_j|^2\le t$.
--   3. `IncreasingClosePairs p t`: the pairs of `OrderedClosePairs p t` with $i<j$.
--
--   When each circle about a configuration point contains at most three other indices, $3$ is the largest possible value of $d_r(i)$, and the saturated incidences are the circles of maximal occupancy. These sets are used to count close pairs among points on such circles.
--
--   **Formalization Note** Indices are elements of `Fin n` with their usual order; the threshold $t$ is a squared distance.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation

namespace Esgk

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

noncomputable def SaturatedDistanceIncidences (p : Config n) : Finset (Fin n × ℝ) :=
  (Finset.univ.product (OrderedDistanceValues p)).filter
    (fun ir ↦ (DistanceOutNeighborsAtValue p ir.1 ir.2).card = 3)

noncomputable def OrderedClosePairs (p : Config n) (t : ℝ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter (fun ij ↦ dist (p ij.1) (p ij.2) ^ 2 ≤ t)

noncomputable def IncreasingClosePairs (p : Config n) (t : ℝ) : Finset (Fin n × Fin n) :=
  (OrderedClosePairs p t).filter (fun ij ↦ ij.1 < ij.2)

end Esgk


