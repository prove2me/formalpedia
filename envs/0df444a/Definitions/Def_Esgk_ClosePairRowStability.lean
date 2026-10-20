-- Prove2me | Definitions.Def_Esgk_ClosePairRowStability
-- name    : Esgk_ClosePairRowStability
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:03:22.264873+00:00
-- url     : https://prove2.me/theorems/141f9344-49a4-44c6-8b10-472176b449c1
-- title:
--   Row of close points at a squared-distance threshold
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane, an index $i$ and a real number $T$, `ClosePairRow p i T` is the set of indices
--
--   $$
--   \{\,j:\ j\ne i,\ |p_i-p_j|^2\le T\,\}.
--   $$
--
--   The threshold $T$ is a squared distance. Let $R(T)$ be the number of distance values $r\in\{|p_a-p_b|: a\ne b\}$ with $r^2\le T$, let $D$ be the number of all distance values, and put $Q=3D-n+1$. If $n\ge1$ and every circle about a configuration point $p_i$ contains at most three indices $j\ne i$, then every row satisfies
--
--   $$
--   3R(T)-Q\le \#\{\,j:\ j\ne i,\ |p_i-p_j|^2\le T\,\}\le 3R(T),
--   $$
--
--   so two rows at the same threshold differ by at most $Q$.
--
--   **Formalization Note** Indices are elements of `Fin n`, and the set is a `Finset (Fin n)`.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Foundation

namespace Esgk

open EuclideanGeometry
variable {n : ℕ}

noncomputable def ClosePairRow (p : Config n) (i : Fin n) (T : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ i ≠ j ∧ dist (p i) (p j) ^ 2 ≤ T)

end Esgk


