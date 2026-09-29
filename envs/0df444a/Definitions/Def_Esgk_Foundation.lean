-- Prove2me | Definitions.Def_Esgk_Foundation
-- name    : Esgk_Foundation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-12T19:22:31.121805+00:00
-- url     : https://prove2.me/theorems/52830133-b5cb-4039-8750-1be311517c02
-- title:
--   Finite indexed planar configurations
-- statement:
--   A raw configuration is a map from the finite index set `Fin n` to the Euclidean plane and may repeat points. Its associated finite set is its image; the theorem hypotheses impose injectivity so their configurations have n different points.
-- source:
--   Self-contained formal statement prepared for this mission.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import Definitions.Def_Esgk_PlanarGeneralPosition

/-!
# Foundation — indexed planar configurations

The numerical targets are stated for injective maps `Fin n → ℝ²`; this module
provides that configuration type and its associated finite set.
-/

namespace Esgk

open EuclideanGeometry

/-- Alias for the ambient plane in this problem. -/
abbrev Point : Type := ℝ²

/-- An indexed configuration of `n` points in the plane. -/
abbrev Config (n : ℕ) : Type := Fin n → Point

/-- Image-finset of an indexed configuration: the set of points that appear in `p`. -/
noncomputable def Config.toFinset {n : ℕ} (p : Config n) : Finset Point := Finset.image p Finset.univ

end Esgk


