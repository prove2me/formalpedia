-- Prove2me | Definitions.Def_HlawkaSchatten_Basic
-- name    : HlawkaSchatten_Basic
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:14:59.076639+00:00
-- url     : https://prove2.me/theorems/5ea3a322-f583-4148-ad20-e1fe7e5a7d3c
-- title:
--   The unit sphere of a normed additive commutative group
-- statement:
--   Defines `HlawkaSchatten.unitSphere`. For a normed additive commutative group $E$ (Lean: `NormedAddCommGroup E`), the unit sphere is the subtype of vectors of norm exactly one,
--
--   $$
--   \mathrm{unitSphere}(E) \;:=\; \{x \in E : \|x\| = 1\}.
--   $$
--
--   It is declared as a Lean `abbrev`, so any fact already known about $E$ is usable directly through the coercion of an element of $\mathrm{unitSphere}(E)$ back to $E$. No inner-product structure is assumed here, only a norm.
--
--   This is the single shared target type used elsewhere to state that some equivalence identifies a Schatten power sphere with an ordinary Hilbert unit sphere (for instance `schattenTwoPowerSphereEquivUnitSphere` in the Hilbert–Schmidt bundle and `rectangularMazurHilbertSphereEquiv` in the variational bundle).
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Basic.lean#L13-L15

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Basic definitions for Hlawka inequalities -/

namespace HlawkaSchatten

/-- The unit sphere of a normed additive group, as a type. -/
abbrev unitSphere (E : Type*) [NormedAddCommGroup E] :=
  {x : E // ‖x‖ = 1}

end HlawkaSchatten


