-- Prove2me | Definitions.Def_OddOrder_Algebra_QuadraticMapCoordinates
-- name    : OddOrder_Algebra_QuadraticMapCoordinates
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:16.185318+00:00
-- url     : https://prove2.me/theorems/a947ea27-fe5c-4da5-80b4-f56cf13fea02
-- title:
--   Coordinates of quadratic maps over $\mathbb{F}_2$
-- statement:
--   Over $\mathbb{Z}/2$, a quadratic map $Q:V\to W$ is determined by its values on a basis of $V$ together with its polar values on pairs of distinct basis vectors, since every vector is a 0/1 combination of basis vectors. Conversely any such data is realized by a sum of elementary quadratic maps $v\mapsto(c_i(v)c_j(v))\,w$ in the basis coordinates. This is packaged as a linear equivalence with the coordinate space $\{p:\iota\times\iota\mid p_1\le p_2\}\to W$.
--
--   The main definition is `coordMulCoord`, the elementary quadratic map attached to two basis coordinates and a vector.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/QuadraticMapCoordinates.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/QuadraticMapCoordinates.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace OddOrder.Algebra.CharTwoQuadratic

open QuadraticMap

variable {ι V W S : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [Semiring S] [Module S W] [SMulCommClass S (ZMod 2) W]

variable (b : Module.Basis ι (ZMod 2) V)

/-- The elementary quadratic map `v ↦ (cᵢ(v)·cⱼ(v)) • w` attached to two
basis coordinates and a target vector. -/
noncomputable def coordMulCoord (i j : ι) (w : W) :
    QuadraticMap (ZMod 2) V W :=
  (LinearMap.toSpanSingleton (ZMod 2) W w).compQuadraticMap
    (QuadraticMap.linMulLin (b.coord i) (b.coord j))

@[simp] theorem coordMulCoord_apply (i j : ι) (w : W) (v : V) :
    coordMulCoord b i j w v = (b.coord i v * b.coord j v) • w :=
  rfl

end OddOrder.Algebra.CharTwoQuadratic


