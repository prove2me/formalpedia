-- Prove2me | Definitions.Def_ProEtale_Morphisms_WeaklyEtale
-- name    : ProEtale_Morphisms_WeaklyEtale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:11:50.240041+00:00
-- url     : https://prove2.me/theorems/d06487b5-3c6a-41eb-98c1-3dd6acd505c9
-- title:
--   Weakly étale morphisms are local on rings
-- statement:
--   The class of weakly étale morphisms of schemes is the one associated with the ring-homomorphism property `RingHom.WeaklyEtale`: a morphism is weakly étale if and only if the induced maps on affine charts are.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 4.1.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Morphisms/WeaklyEtale.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Weakly étale morphisms

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace WeaklyEtale

/-- `WeaklyEtale` is induced by the ring-homomorphism property `RingHom.WeaklyEtale`,
in the sense that a morphism `f : X ⟶ Y` of schemes is weakly étale iff for every affine
open `U ⊆ Y` and every affine open `V ⊆ X` with `f(V) ⊆ U`, the induced ring homomorphism
`Γ(Y, U) → Γ(X, V)` is weakly étale. -/
instance hasRingHomProperty : HasRingHomProperty @WeaklyEtale.{u} RingHom.WeaklyEtale := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget @WeaklyEtale.{u}
  refine HasRingHomProperty.copy (P := @WeaklyEtale.{u}) rfl ?_
  intro R S _ _ f
  algebraize [f]
  have hf : f = algebraMap R S := rfl
  rw [hf, weaklyEtale_iff, diagonal_SpecMap R S,
    MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
    HasRingHomProperty.Spec_iff (P := @Flat), HasRingHomProperty.Spec_iff (P := @Flat)]
  simp only [CommRingCat.hom_ofHom, autoParam, RingHom.flat_algebraMap_iff,
    RingHom.weaklyEtale_algebraMap_iff, Algebra.weaklyEtale_iff]


end WeaklyEtale

end AlgebraicGeometry


