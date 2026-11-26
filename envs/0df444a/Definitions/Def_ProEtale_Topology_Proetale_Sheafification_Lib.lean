-- Prove2me | Definitions.Def_ProEtale_Topology_Proetale_Sheafification_Lib
-- name    : ProEtale_Topology_Proetale_Sheafification_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:42:30.576305+00:00
-- url     : https://prove2.me/theorems/bafd8517-883f-4a51-ad41-197302a0046c
-- title:
--   Existence of sheafification for sheaves of sets in the next universe on the pro-étale site
-- statement:
--   This file continues the published file of the same name. For a scheme $S$ in universe $u$, the pro-étale site $S_{\mathrm{pro\acute et}}$ (objects: schemes weakly étale over $S$) admits sheafification for presheaves of sets valued in the universe $u+1$: the inclusion of sheaves into presheaves $S_{\mathrm{pro\acute et}}^{\mathrm{op}} \to \mathrm{Set}_{u+1}$ has a finite-limit-preserving left adjoint.
--
--   The universe shift is needed because $S_{\mathrm{pro\acute et}}$ is a large category whose objects form a type in universe $u+1$.
--
--   **Formalization Note** The single declaration is an instance `HasSheafify (ProEt.topology S) (Type (u + 1))` for `S : Scheme.{u}`, obtained by instance search from results of the published file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Proetale/Sheafification.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Topology_Proetale_Sheafification of the same module.

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Sets.CompactOpenCovered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Topology_Flat_QuasiCompactCover
import Definitions.Def_ProEtale_Topology_Proetale_Basic
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# The pro-étale site has sheafification

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry
namespace Scheme
namespace ProEt

/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Type (u + 1)`-valued sheafs. -/
instance inst_TopologyProetaleSheafification_L19 (S : Scheme.{u}) : HasSheafify (ProEt.topology S) (Type (u + 1)) :=
  inferInstance


end ProEt
end Scheme
end AlgebraicGeometry


