-- Prove2me | Definitions.Def_MazurCampaign_target_objects
-- name    : MazurCampaign_target_objects
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-05T18:09:33.32533+00:00
-- url     : https://prove2.me/theorems/9fdce5b7-4a66-41d7-81c9-c8fc40c950d1
-- title:
--   Rational elliptic-curve torsion and the fifteen Mazur groups
-- statement:
--   The point group is Mathlib’s standard group of rational points on a Weierstrass curve. Rational torsion is its canonical subgroup of finite-order points. The allowed cyclic orders are exactly 1 through 10 and 12, and the bicyclic parameters are exactly 1 through 4. Classification means existence of an additive group isomorphism from the entire torsion subgroup to one of these groups. The predicate is defined for every rational Weierstrass curve, including singular curves; all classification theorems separately require ellipticity. This bundle asserts no arithmetic theorem.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf; target vocabulary adapted from https://github.com/Vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/GroupTheory/ClassificationCardinality.lean#L27-L44

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Campaign target vocabulary adapted from MazurTorsion/GroupTheory/ClassificationCardinality.lean.
The checked repository remains the integration destination.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Torsion

open scoped WeierstrassCurve.Affine

namespace MazurCampaign

def cyclicOrders : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

def bicyclicParameters : Finset ℕ :=
  {1, 2, 3, 4}

abbrev RationalTorsion (E : WeierstrassCurve ℚ) :=
  AddCommGroup.torsion (E⁄ℚ).Point

def HasMazurClassification (E : WeierstrassCurve ℚ) : Prop :=
  (∃ n ∈ cyclicOrders, Nonempty (RationalTorsion E ≃+ ZMod n)) ∨
    ∃ m ∈ bicyclicParameters, Nonempty (RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m)))

end MazurCampaign


