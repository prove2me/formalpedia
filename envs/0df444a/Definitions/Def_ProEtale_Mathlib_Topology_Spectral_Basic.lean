-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
-- name    : ProEtale_Mathlib_Topology_Spectral_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:15.99936+00:00
-- url     : https://prove2.me/theorems/f1d467c7-ee9f-5187-960d-1bc2ba5bf188
-- title:
--   Spectral spaces: transport along homeomorphisms and closed embeddings, products, and generalization hulls of compact sets
-- statement:
--   A topological space is *spectral* if it is $T_0$, quasi-compact, quasi-sober and quasi-separated, and its compact open subsets form a basis. For a point $x$ and a point $y$, write $x \rightsquigarrow y$ if $x$ specializes to $y$ (that is, $y \in \overline{\{x\}}$). The *generalization hull* of a set $s$ is the set of points $x$ with $x \rightsquigarrow y$ for some $y \in s$.
--
--   Principal results:
--
--   1. A space homeomorphic to a spectral space is spectral.
--   2. If $f : X \to Y$ is a closed embedding and $Y$ is spectral, then $X$ is spectral; in particular every closed subspace of a spectral space is spectral.
--   3. (Stacks 0907) The product of two spectral spaces is spectral.
--   4. If $X$ is spectral, $s \subseteq X$ is compact, and $x$ specializes to no point of $s$, then there is a compact open $V$ with $s \subseteq V$ and $x \notin V$.
--   5. If $X$ is spectral and $s \subseteq X$ is compact, then the generalization hull of $s$ is the intersection of a family of compact open subsets of $X$.
--
--   These are general facts about spectral spaces (such as underlying spaces of affine schemes), used in the theory of w-local spaces.
--
--   **Formalization Note** Main declarations: `Homeomorph.spectralSpace`, `Topology.IsClosedEmbedding.spectralSpace`, the instances `SpectralSpace.of_isClosed` and `SpectralSpace.prod`, `IsCompact.exists_isOpen_isCompact_subset_of_forall_not_specializes`, `generalizationHull.eq_sInter_of_isCompact`. In item 5 the family is a set `S` of subsets that are open and compact, with `generalizationHull s = ⋂₀ S`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 0907. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Spectral/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open Topology

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

-- after `SpectralSpace`
variable {X Y} in
theorem Homeomorph.spectralSpace [SpectralSpace X] (f : X ≃ₜ Y) : SpectralSpace Y :=
  {f.t0Space, f.compactSpace, f.quasiSober, f.quasiSeparatedSpace, f.prespectralSpace with}

variable {X Y} in
theorem Topology.IsClosedEmbedding.spectralSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [SpectralSpace Y] : SpectralSpace X where
  toT0Space := hf.isEmbedding.t0Space
  toQuasiSober := hf.quasiSober
  toQuasiSeparatedSpace := by
    constructor
    intro V1 V2 open1 cpt1 open2 cpt2
    obtain ⟨U1, open1, cpt1, h1⟩ := hf.isOpen_and_isCompact_and_preimage_eq open1 cpt1
    obtain ⟨U2, open2, cpt2, h2⟩ := hf.isOpen_and_isCompact_and_preimage_eq open2 cpt2
    simp only [← h1, ← h2, ← Set.preimage_inter]
    apply IsCompact.preimage_of_isOpen hf.isProperMap.isSpectralMap
    · exact QuasiSeparatedSpace.inter_isCompact U1 U2 open1 cpt1 open2 cpt2
    · exact open1.inter open2
  toCompactSpace := hf.compactSpace
  toPrespectralSpace := PrespectralSpace.of_isClosedEmbedding f hf

instance SpectralSpace.of_isClosed [SpectralSpace X] {C : Set X} [IsClosed C] : SpectralSpace C :=
  (IsClosed.isClosedEmbedding_subtypeVal ‹_›).spectralSpace

@[stacks 0907]
instance SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) where
  toCompactSpace := inferInstance
  toT0Space := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance

variable {X} in
/-- In a spectral space, if `s` is compact and `x` does not specialize to any point of `s`, then
there exists a compact open containing `s` but not `x`. -/
theorem IsCompact.exists_isOpen_isCompact_subset_of_forall_not_specializes [SpectralSpace X]
    {s : Set X} (hs : IsCompact s) {x : X} (hxs : ∀ y ∈ s, ¬ x ⤳ y) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ s ⊆ V ∧ x ∉ V := by
  have hbasis := PrespectralSpace.isTopologicalBasis (X := X)
  have hcov : ∀ y ∈ s, ∃ U, (IsOpen U ∧ IsCompact U) ∧ y ∈ U ∧ x ∉ U := by
    intro y hy
    have hxy : ¬ x ⤳ y := hxs y hy
    rw [specializes_iff_mem_closure] at hxy
    obtain ⟨U, hU, hyU, hUsub⟩ :=
      hbasis.exists_subset_of_mem_open hxy (isOpen_compl_iff.mpr isClosed_closure)
    exact ⟨U, hU, hyU, fun hxU ↦ hUsub hxU (subset_closure rfl)⟩
  choose U hU hyU hxnU using hcov
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun y : s ↦ U y y.2)
    (fun y ↦ (hU y y.2).1) (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyU y hy⟩)
  refine ⟨⋃ y ∈ t, U y.1 y.2, isOpen_biUnion fun y _ ↦ (hU y.1 y.2).1,
    t.finite_toSet.isCompact_biUnion fun y _ ↦ (hU y.1 y.2).2, fun z hz ↦ ht hz, fun hxV ↦ ?_⟩
  obtain ⟨y, hyt, hxUy⟩ : ∃ y ∈ t, x ∈ U y.1 y.2 := by simpa using hxV
  exact hxnU y.1 y.2 hxUy


variable {X} in
theorem generalizationHull.eq_sInter_of_isCompact [SpectralSpace X] {s : Set X} (hs : IsCompact s) :
    ∃ S ⊆ {U : Set X | IsOpen U ∧ IsCompact U}, (generalizationHull s) = ⋂₀ S := by
  refine ⟨{U : Set X | IsOpen U ∧ IsCompact U ∧ s ⊆ U}, fun _ h ↦ ⟨h.1, h.2.1⟩,
    subset_antisymm (fun x hx U hU ↦ ?_) (fun x hx ↦ ?_)⟩
  · obtain ⟨y, hys, hxy⟩ := mem_generalizationHull_iff.mp hx
    exact hU.1.stableUnderGeneralization hxy (hU.2.2 hys)
  · by_contra hxs
    obtain ⟨V, hVopen, hVcompact, hsV, hxV⟩ :=
      hs.exists_isOpen_isCompact_subset_of_forall_not_specializes
        (fun y hy hxy ↦ hxs (mem_generalizationHull_iff.mpr ⟨y, hy, hxy⟩))
    exact hxV (hx V ⟨hVopen, hVcompact, hsV⟩)


