-- Prove2me | Definitions.Def_Esgk_AnnulusClusterGeometry
-- name    : Esgk_AnnulusClusterGeometry
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:02:32.744649+00:00
-- url     : https://prove2.me/theorems/0cd6edb8-bbae-4c60-afa5-4bf33a14d236
-- title:
--   Closed ball of indices in an indexed planar configuration
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane, an index $i$ and a real number $t$, `ConfigClosedBall p i t` is the set of indices
--
--   $$
--   B_p(i,t)=\{\,j:\ |p_i-p_j|\le t\,\}.
--   $$
--
--   It contains $i$ when $t\ge 0$ and is empty when $t<0$. When $p$ is injective, its size is the number of configuration points in the closed disk of radius $t$ about $p_i$. Lower bounds for these sizes express that a configuration has heavy small balls.
--
--   **Formalization Note** Indices are elements of `Fin n`, and the set is a `Finset (Fin n)`.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Foundation

namespace Esgk

open scoped RealInnerProductSpace
variable {n : ℕ}

noncomputable def ConfigClosedBall (p : Config n) (i : Fin n) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ dist (p i) (p j) ≤ t)

end Esgk


