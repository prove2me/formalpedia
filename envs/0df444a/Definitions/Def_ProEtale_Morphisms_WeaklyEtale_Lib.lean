-- Prove2me | Definitions.Def_ProEtale_Morphisms_WeaklyEtale_Lib
-- name    : ProEtale_Morphisms_WeaklyEtale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:48.951027+00:00
-- url     : https://prove2.me/theorems/bb201902-4e9e-4a64-a008-bbcd15900f1c
-- title:
--   Weakly étale morphisms locally of finite presentation are étale; weakly étale morphisms of affine schemes
-- statement:
--   This file continues the published file *Weakly étale morphisms* (same module). Here weakly étale morphisms of schemes are those given affine-locally by weakly étale ring maps (flat ring maps with flat multiplication map). It proves:
--
--   1. If $f : X \to Y$ is weakly étale and locally of finite presentation, then $f$ is étale.
--   2. For a ring homomorphism $\varphi : R \to S$,
--   $$\operatorname{Spec}(\varphi) : \operatorname{Spec} S \to \operatorname{Spec} R \text{ is weakly étale} \iff \varphi \text{ is weakly étale.}$$
--
--   Item 1 is how weakly étale morphisms relate to the étale site; item 2 lets one pass between the scheme-theoretic and algebraic notions.
--
--   **Formalization Note** Main declarations: the instance `AlgebraicGeometry.WeaklyEtale.etale` (priority 900) and the simp lemma `AlgebraicGeometry.WeaklyEtale.Spec_iff`. Schemes live in universe `u`. Item 1 goes through formal unramifiedness on affine opens and Mathlib's criterion étale = flat + formally unramified + locally of finite presentation.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Morphisms/WeaklyEtale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Morphisms_WeaklyEtale of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Maps
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale

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


instance (priority := 900) etale [WeaklyEtale f] [LocallyOfFinitePresentation f] : Etale f := by
  have : FormallyUnramified f := by
    rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
    intro U V e
    exact (HasRingHomProperty.appLE @WeaklyEtale.{u} f ‹_› U V e).formallyUnramified
  exact Etale.of_formallyUnramified_of_flat f

@[simp]
lemma Spec_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    WeaklyEtale (Spec.map f) ↔ f.hom.WeaklyEtale :=
  HasRingHomProperty.Spec_iff (P := @WeaklyEtale.{u})

end WeaklyEtale

end AlgebraicGeometry


