-- Prove2me | Definitions.Def_ProEtale_Topology_Flat_QuasiCompactCover
-- name    : ProEtale_Topology_Flat_QuasiCompactCover
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:24.006973+00:00
-- url     : https://prove2.me/theorems/5610261d-3340-41c4-862d-59dfa2ce8cbe
-- title:
--   A finite affine cover of an affine scheme is a quasi-compact cover
-- statement:
--   A cover $(U_i \to S)_i$ of a scheme $S$ is *quasi-compact* if every affine open of $S$ is covered by the images of finitely many quasi-compact opens of the $U_i$; this is the condition used in defining the fpqc topology.
--
--   The file proves: if $S$ is an affine scheme and $(\operatorname{Spec} A_i \to S)_{i \in I}$ is a cover of $S$ by affine schemes, with morphisms satisfying a property $P$, and the index set $I$ is finite, then this cover is quasi-compact. (Each affine open of $S$ is quasi-compact, and the preimages under the spectral maps $\operatorname{Spec} A_i \to S$ provide the required finitely many quasi-compact opens.)
--
--   **Formalization Note** `S : Scheme.{u}` with `[IsAffine S]`, `𝒰 : S.AffineCover P` with `[Finite 𝒰.I₀]`; the result is an anonymous instance `QuasiCompactCover 𝒰.cover.toPreZeroHypercover`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Flat/QuasiCompactCover.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Sets.CompactOpenCovered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

universe w u v

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

variable (𝒰 : Scheme.Cover.{v} (precoverage P) S)

namespace Scheme
namespace Cover
namespace QuasiCompact

variable {𝒰 : Cover.{v} (Scheme.precoverage P) S}

open TopologicalSpace.Opens

open TopologicalSpace Opens


instance inst_TopologyFlatQuasiCompactCover_L91 {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    have : Finite 𝒰.cover.I₀ := inferInstanceAs (Finite 𝒰.I₀)
    have (i : 𝒰.I₀) : IsAffine (𝒰.cover.X i) := isAffine_Spec _
    have (i : 𝒰.I₀) : QuasiCompact (𝒰.cover.f i) := inferInstance
    exact .of_finite_of_isSpectralMap (fun i ↦ (𝒰.cover.f i).isSpectralMap)
      (fun x _ ↦ ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

end QuasiCompact
end Cover
end Scheme
end AlgebraicGeometry


