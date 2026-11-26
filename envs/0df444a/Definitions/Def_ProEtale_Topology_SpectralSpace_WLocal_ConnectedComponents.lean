-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
-- name    : ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:42:28.005022+00:00
-- url     : https://prove2.me/theorems/9293590b-4dcf-4bba-a7e8-77780d081702
-- title:
--   In a w-local space the closed points map homeomorphically onto the connected components
-- statement:
--   A topological space $X$ is *w-local* if it is spectral, its set $X^c$ of closed points is closed, and every point specializes to at most one closed point (in a spectral space every point specializes to some closed point).
--
--   Principal results:
--
--   1. If $X$ is w-local, the composite
--   $$X^c \hookrightarrow X \longrightarrow \pi_0(X)$$
--   of the inclusion of the closed points with the quotient map onto the space of connected components is a homeomorphism.
--   2. Consequently, two closed points of a w-local space that lie in the same connected component are equal.
--
--   This identifies $\pi_0$ of a w-local space with its subspace of closed points, a basic fact in the theory of w-local spaces.
--
--   **Formalization Note** Main declarations: `WLocalSpace.isHomeomorph_connectedComponents_closedPoints` (stated as `IsHomeomorph (ConnectedComponents.mk ∘ Subtype.val)` on `closedPoints X`) and `WLocalSpace.closedPoints_eq_of_mk_eq`. The module docstring also mentions a homeomorphism `WLocalSpace.closedPointsHomeomorph`, but that declaration is not in this file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/WLocal/ConnectedComponents.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Yiming Fu
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Connected components of w-local spaces

This file establishes the relationship between closed points and connected components
in w-local spaces.

## Main results

* `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`: The composition
  `closedPoints X → X → ConnectedComponents X` is a homeomorphism for w-local spaces.
* `WLocalSpace.closedPointsHomeomorph`: The closed points of a w-local space are
  homeomorphic to the connected components.

-/

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) := by
  have : CompactSpace (closedPoints X) :=
    (IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints).compactSpace
  have : T2Space (ConnectedComponents X) := t2Space_connectedComponent
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
    simp only [Function.comp_apply] at heq
    by_contra hxy
    obtain ⟨U₀, hU₀_clopen, hxU₀, hyU₀⟩ := exists_isClopen_of_totally_separated hxy
    have hce : Topology.IsClosedEmbedding ((↑) : closedPoints X → X) :=
      IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints
    let U := generalizationHull (Subtype.val '' U₀)
    let V := generalizationHull (Subtype.val '' U₀ᶜ)
    have hU_closed : IsClosed U :=
      isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap U₀ hU₀_clopen.1)
    have hV_closed : IsClosed V :=
      isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap U₀ᶜ hU₀_clopen.compl.1)
    have hX_eq : (Set.univ : Set X) = U ∪ V := by
      ext z
      simp only [Set.mem_univ, true_iff]
      obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
      have hc_cp : c ∈ closedPoints X := mem_closedPoints_iff.mpr hc_closed
      exact (em (⟨c, hc_cp⟩ ∈ U₀)).imp
        (fun h ↦ mem_generalizationHull_iff.mpr ⟨c, ⟨⟨c, hc_cp⟩, h, rfl⟩, hzc⟩)
        (fun h ↦ mem_generalizationHull_iff.mpr ⟨c, ⟨⟨c, hc_cp⟩, h, rfl⟩, hzc⟩)
    have hUV_disjoint : Disjoint U V := by
      rw [Set.disjoint_iff]
      rintro z ⟨hzU, hzV⟩
      rw [mem_generalizationHull_iff] at hzU hzV
      obtain ⟨c, ⟨⟨c', hc'⟩, hc'U₀, rfl⟩, hzc⟩ := hzU
      obtain ⟨d, ⟨⟨d', hd'⟩, hd'V₀, rfl⟩, hzd⟩ := hzV
      exact hd'V₀ (WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hc')
        (mem_closedPoints_iff.mp hd') hzc hzd ▸ hc'U₀)
    have hUV_compl : IsCompl U V :=
      ⟨hUV_disjoint, Set.codisjoint_iff.mpr hX_eq.symm⟩
    have hU_clopen : IsClopen U :=
      ⟨hU_closed, hUV_compl.eq_compl.symm ▸ hV_closed.isOpen_compl⟩
    have hxU : x ∈ U :=
      mem_generalizationHull_iff.mpr ⟨x, ⟨⟨x, hx⟩, hxU₀, rfl⟩, specializes_refl x⟩
    have hyV : y ∈ V :=
      mem_generalizationHull_iff.mpr ⟨y, ⟨⟨y, hy⟩, hyU₀, rfl⟩, specializes_refl y⟩
    exact hUV_disjoint.ne_of_mem (hU_clopen.connectedComponent_subset hxU
      (ConnectedComponents.coe_eq_coe'.mp heq.symm)) hyV rfl
  · intro c
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨p, hp, hxp⟩ := exists_isClosed_specializes x
    exact ⟨⟨p, mem_closedPoints_iff.mpr hp⟩, ConnectedComponents.coe_eq_coe.mpr
      (connectedComponent_eq_iff_mem.mpr (isConnected_singleton.closure.subset_connectedComponent
        (subset_closure rfl) (specializes_iff_mem_closure.mp hxp)))⟩


/-- Two closed points in a w-local space lying in the same connected component are equal. -/
lemma WLocalSpace.closedPoints_eq_of_mk_eq {X : Type*} [TopologicalSpace X] [WLocalSpace X]
    {c₁ c₂ : X} (hc₁ : c₁ ∈ closedPoints X) (hc₂ : c₂ ∈ closedPoints X)
    (hmk : ConnectedComponents.mk c₁ = ConnectedComponents.mk c₂) : c₁ = c₂ :=
  congrArg Subtype.val <|
    (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).bijective.1
      (a₁ := ⟨c₁, hc₁⟩) (a₂ := ⟨c₂, hc₂⟩) hmk


