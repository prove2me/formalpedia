-- Prove2me | Definitions.Def_MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
-- name    : MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:24:01.045514+00:00
-- url     : https://prove2.me/theorems/8dce7b6b-fb95-4f91-86e4-e33a79c97404
-- title:
--   The original line bundle attached to a base-field represented Picard point
-- statement:
--   Let $K$ be a field, let $X$ be a $K$-scheme with the specified section, and let $D$ represent the stated relative degree-zero Picard functor. Each base-field point $a$ determines the original invertible line bundle on $X$: $$\mathcal L_a=\iota_X^*\mathcal P_a,$$ where $\iota_X:X\to X\times_{\operatorname{Spec}K}\operatorname{Spec}K$ is the original product-section map and $\mathcal P_a$ is the represented Poincare line bundle at $a$. This interface supplies base-field curve-pullback naturality and the arithmetic Picard comparison.
-- source:
--   Original complete pointLineBundle and pointLineBundle_isInvertible declarations and bodies from MazurTheorem RepresentedPicardFieldPointLineBundles.lean, Apache-2.0, Vas and contributors. Publishes only the constructor and its invertibility certificate; the retained original header describes the larger source module. Two complete original closed types and one data value are kernel-compared for both the native canonical mirror and this explicit-public-data package. The original product-section constructor is imported directly from the official Anthropic FLT RelPicardAbelJacobiFamily data at pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Design boundary: the original base-field point line bundle. Named downstream consumer: re-rigidified curve pullback and arithmetic Picard naturality.

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: attach an actual line bundle on the original curve to each
base-field point of a represented degree-zero Picard scheme, prove geometric
degree zero and detect equality by sheaf isomorphism. Named downstream consumer:
the finite-field order-13 divisor-class/Jacobian comparison. The constructions
use the official Anthropic FLT relative Picard interface at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, and do not require an
algebraically closed base field or a point/divisor-class dictionary.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace MazurTransfer.LineBundleFieldComparison

noncomputable def pointLineBundle {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) : X.Modules :=
  (Scheme.Modules.pullback (toProdSpec x)).obj (h.poincare.pullbackAlong a).L

theorem pointLineBundle_isInvertible {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    Scheme.Modules.IsInvertible (pointLineBundle x ε D h a) :=
  (h.poincare.pullbackAlong a).isInvertible.pullback (toProdSpec x)


end MazurTransfer.LineBundleFieldComparison
#print axioms MazurTransfer.LineBundleFieldComparison.pointLineBundle
#print axioms MazurTransfer.LineBundleFieldComparison.pointLineBundle_isInvertible


