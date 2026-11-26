-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_WeaklyContractible
-- name    : ProEtale_Topology_Comparison_WeaklyContractible
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:25:05.845312+00:00
-- url     : https://prove2.me/theorems/e26f7c3f-b31c-5e52-8f56-b87eeccea4a8
-- title:
--   Weakly contractible pro-étale affines
-- statement:
--   A pro-étale affine $W$ over $S$ is **weakly contractible** (`AffineProEt.IsWeaklyContractible`) if every morphism $V \to W$ of pro-étale affines that is surjective on underlying spaces has a section. The paper's Definition 3.2.1 is the topos-level notion (every surjection of sheaves onto the object splits).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 3.2.1, in affine form. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/WeaklyContractible.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Weakly contractible objects of the pro-étale site

An object `W` of the affine pro-étale site of a scheme `S` is *weakly contractible* if
every surjection onto `W` in the affine pro-étale site splits. We show:

- `AlgebraicGeometry.Scheme.AffineProEt.isWeaklyContractible_of_isWContractibleRing`:
  if the ring of global sections of `W` is w-contractible, then `W` is weakly
  contractible (every faithfully flat ind-étale algebra over a w-contractible ring has a
  retraction, `IsWContractibleRing.exists_retraction`).
- `AlgebraicGeometry.Scheme.AffineProEt.exists_isWeaklyContractible_cover`:
  every object of the affine pro-étale site admits a surjection from a weakly
  contractible object (BS, Proposition 4.2.8; blueprint `prop:proet-wc`). This follows
  from `exists_isWContractibleRing`.
- `AlgebraicGeometry.Scheme.AffineProEt.surjective_app_of_epi`: an epimorphism of abelian
  sheaves on the pro-étale site is surjective on sections over weakly contractible
  objects.
- `AlgebraicGeometry.Scheme.AffineProEt.epi_of_forall_surjective_app`: conversely, a
  morphism of abelian sheaves which is surjective on sections over all weakly
  contractible objects is an epimorphism.

In particular the topos of pro-étale sheaves on `S` has enough weakly contractible
objects, hence is replete.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- An object `W` of the affine pro-étale site is weakly contractible if every surjection
onto `W` in the affine pro-étale site splits. -/
def IsWeaklyContractible (W : S.AffineProEt) : Prop :=
  ∀ ⦃V : S.AffineProEt⦄ (q : V ⟶ W), Surjective q.left → ∃ s : W ⟶ V, s ≫ q = 𝟙 W


variable (F : Sheaf (ProEt.topology S) Ab.{u + 1})


variable {F} {G : Sheaf (ProEt.topology S) Ab.{u + 1}}


end AlgebraicGeometry.Scheme.AffineProEt


