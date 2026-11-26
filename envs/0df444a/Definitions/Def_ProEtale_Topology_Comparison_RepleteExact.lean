-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_RepleteExact
-- name    : ProEtale_Topology_Comparison_RepleteExact
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:25:42.565728+00:00
-- url     : https://prove2.me/theorems/74daf6ea-098a-5244-a0e1-21abd181af0b
-- title:
--   Limits of abelian pro-étale sheaves
-- statement:
--   Instances providing sequential inverse limits and small products in the category of abelian sheaves on the pro-étale site, in the universe conventions of this development.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Section 3.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/RepleteExact.lean (declarations kept unchanged, unused ones removed).

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
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
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
import Definitions.Def_ProEtale_Topology_Comparison_WeaklyContractible
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Exactness of sequential limits of pro-étale abelian sheaves

The topos of pro-étale sheaves on a scheme is replete: it has enough weakly contractible
objects (`Proetale.Topology.Comparison.WeaklyContractible`). We deduce the two exactness
statements needed for the comparison of continuous étale cohomology with pro-étale
cohomology (BS, Propositions 3.1.9 and 3.1.10; blueprint `prop:replete-products-exact`
and `prop:lim-exact-replete`):

- `AlgebraicGeometry.Scheme.ProEt.epi_piMap`: products of epimorphisms of abelian
  pro-étale sheaves are epimorphisms.
- `AlgebraicGeometry.Scheme.ProEt.shortExact_limMap`: the limit of a levelwise short
  exact sequence of inverse systems of abelian pro-étale sheaves is short exact, provided
  the first system has epimorphic transition maps (Mittag-Leffler).
- `AlgebraicGeometry.Scheme.ProEt.shortExact_telescope`: for an inverse system `G` with
  epimorphic transition maps, the Milnor sequence
  `0 → lim G → ∏ Gₙ → ∏ Gₙ → 0` (with second map `1 - shift`) is short exact.

All proofs proceed by evaluating on weakly contractible objects of the affine pro-étale
site, where the corresponding statements for abelian groups are elementary.
-/

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- Limits of shape `ℕᵒᵖ` of abelian pro-étale sheaves. Registered explicitly: typeclass
search for limit shapes in sheaf categories is prohibitively slow. -/
instance : HasLimitsOfShape ℕᵒᵖ (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Sheaf.instHasLimitsOfShape

/-- Products indexed by a small type of abelian pro-étale sheaves, registered
explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

/-- Products indexed by a small type of abelian groups, registered explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) Ab.{u + 1} :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm


end AlgebraicGeometry.Scheme.ProEt


