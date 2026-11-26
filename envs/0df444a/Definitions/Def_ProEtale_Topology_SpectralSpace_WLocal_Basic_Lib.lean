-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
-- name    : ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:19.035743+00:00
-- url     : https://prove2.me/theorems/05ddc9e0-b683-5e45-b978-399525eff476
-- title:
--   w-local maps; subspaces of w-local spaces stable under specialization; generalization hulls of closed sets in w-local spaces
-- statement:
--   This file continues the published file *Topology/SpectralSpace/WLocal/Basic*. A **w-local space** is a spectral space in which every point specializes to a unique closed point and the set of closed points is closed.
--
--   **Definition.** A map $f : X \to Y$ of topological spaces is **w-local** if it is spectral and sends closed points to closed points: $\mathrm{cl}(X) \subseteq f^{-1}(\mathrm{cl}(Y))$, where $\mathrm{cl}(-)$ denotes the set of closed points.
--
--   **Results.** Let $f : X \to Y$ be a topological embedding whose image is stable under specialization.
--
--   1. A point $z \in X$ is closed iff $f(z)$ is closed in $Y$. The "if" direction holds for every embedding. Hence $\mathrm{cl}(X) = f^{-1}(\mathrm{cl}(Y))$.
--   2. If $X$ is spectral and $Y$ is w-local, then $X$ is w-local. In particular a closed embedding into a w-local space has w-local domain.
--   3. In a w-local space $X$, the generalization hull $\{x : \exists y \in s,\ x \rightsquigarrow y\}$ of a set $s$ stable under specialization is again stable under specialization. The generalization hull of a closed set is closed.
--
--   The file also makes closedness of the set of closed points of a w-local space an instance.
--
--   **Formalization Note** Main declarations: `IsWLocalMap` (a structure extending `IsSpectralMap`, with field `closedPoints_subset_preimage_closedPoints`), `Topology.IsEmbedding.isClosed_singleton`, `Topology.IsEmbedding.isClosed_singleton_of_isClosed_image_singleton`, `Topology.IsEmbedding.closedPoints_eq_preimage`, `Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range`, `Topology.IsClosedEmbedding.wLocalSpace`, `StableUnderSpecialization.generalizationHull_of_wLocalSpace` and `isClosed_generalizationHull_of_wLocalSpace`. Here $x \rightsquigarrow y$ (`x ⤳ y`) means $y \in \overline{\{x\}}$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/WLocal/Basic.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Topology_SpectralSpace_WLocal_Basic of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Data.Set.Card
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-local spaces

In this file we define w-local spaces. These are spectral spaces in which every point
specializes to a unique closed point and where the set of closed points is closed.
-/


attribute [instance] WLocalSpace.isClosed_closedPoints

/-- A w-local map is a spectral map that maps closed points to closed points. -/
@[mk_iff]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop
    extends IsSpectralMap f where
  closedPoints_subset_preimage_closedPoints : closedPoints X ⊆ f ⁻¹' (closedPoints Y)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Topology


/-- An embedding with specialization-stable range maps closed singletons to closed singletons. -/
lemma Topology.IsEmbedding.isClosed_singleton
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f))
    {z : X} (hz : IsClosed {z}) :
    IsClosed {f z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
  obtain ⟨z', rfl⟩ := hrange hspec (Set.mem_range_self z)
  have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
  have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
  rw [Set.mem_singleton_iff.mp this]
  exact Set.mem_singleton _

/-- If `f` is an embedding and `{f z}` is closed, then `{z}` is closed. -/
lemma Topology.IsEmbedding.isClosed_singleton_of_isClosed_image_singleton
    {f : X → Y} (hf : IsEmbedding f) {z : X} (hz : IsClosed {f z}) :
    IsClosed {z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  have hfspec : f z ⤳ f x := (specializes_iff_mem_closure.mpr hx).map hf.continuous
  exact Set.mem_singleton_iff.mpr
    (hf.injective (Set.mem_singleton_iff.mp (hz.closure_eq ▸ hfspec.mem_closure)))

/-- An embedding with specialization-stable range identifies
closed points of `X` with the preimage of closed points of `Y`. -/
lemma Topology.IsEmbedding.closedPoints_eq_preimage
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f)) :
    closedPoints X = f ⁻¹' closedPoints Y := by
  ext x
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  exact ⟨hf.isClosed_singleton hrange, hf.isClosed_singleton_of_isClosed_image_singleton⟩

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' :=
    hf.injective (WLocalSpace.eq_of_specializes (hf.isClosed_singleton h hc)
      (hf.isClosed_singleton h hc') (hxc.map hf.continuous) (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    rw [hf.closedPoints_eq_preimage h]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  rw [generalizationHull_eq]
  intro a b hab ha
  obtain ⟨y, hys, hay⟩ := ha
  obtain ⟨c, hc_closed, hyc⟩ := exists_isClosed_specializes y
  obtain ⟨c', hc'_closed, hbc'⟩ := exists_isClosed_specializes b
  obtain rfl := WLocalSpace.eq_of_specializes hc_closed hc'_closed
    (hay.trans hyc) (hab.trans hbc')
  exact ⟨c, hs hyc hys, hbc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X :=
  have : SpectralSpace X := hf.spectralSpace
  hf.isEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    hf.isClosedMap.isClosed_range.stableUnderSpecialization

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) := by
  have ⟨u, hu1, hu2⟩ := generalizationHull.eq_sInter_of_isCompact
    (isCompact_univ.of_isClosed_subset hs (Set.subset_univ s))
  have hsg : IsClosed[constructibleTopology X] (generalizationHull s) := by
    refine hu2 ▸ @isClosed_sInter X (constructibleTopology X) _ fun t ht ↦ ?_
    obtain ⟨ht1, ht2⟩ := hu1 ht
    exact ht2.isClosed_constructibleTopology_of_isOpen ht1
  exact hsg.of_isClosed_constructibleTopology
    hs.stableUnderSpecialization.generalizationHull_of_wLocalSpace


