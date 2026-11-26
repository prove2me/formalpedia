-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
-- name    : ProEtale_Mathlib_Topology_Spectral_Prespectral
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:18.309956+00:00
-- url     : https://prove2.me/theorems/bbfc535e-84a1-4f6f-b18f-3092bd88dc86
-- title:
--   Prespectral spaces: transport along homeomorphisms, binary products, and compact opens of closed subspaces
-- statement:
--   A topological space is *prespectral* if its compact open subsets form a basis of the topology.
--
--   Principal results:
--
--   1. A space homeomorphic to a prespectral space is prespectral.
--   2. The product $X \times Y$ of two prespectral spaces is prespectral.
--   3. Let $X$ be compact and prespectral and let $f : Z \to X$ be a closed embedding. Then for every compact open $V \subseteq Z$ there is a compact open $U \subseteq X$ with $f^{-1}(U) = V$.
--
--   These results support transferring spectral-space structure along homeomorphisms, products and closed subspaces.
--
--   **Formalization Note** Main declarations: `Homeomorph.prespectralSpace`, the instance `PrespectralSpace.prod`, and `Topology.IsClosedEmbedding.isOpen_and_isCompact_and_preimage_eq`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Spectral/Prespectral.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Spectral.Prespectral

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-- A prespectral space structure transfers along homeomorphisms. -/
-- after `PrespectralSpace.of_isTopologicalBasis'`
theorem Homeomorph.prespectralSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] (f : X ≃ₜ Y) : PrespectralSpace Y := by
  have hbasis : TopologicalSpace.IsTopologicalBasis
      (Set.preimage f.symm '' { U : Set X | IsOpen U ∧ IsCompact U }) :=
    PrespectralSpace.isTopologicalBasis.isInducing f.symm.isInducing
  apply PrespectralSpace.of_isTopologicalBasis hbasis
  intro U hU
  simp only [Set.mem_image, Set.mem_setOf_eq] at hU
  obtain ⟨V, ⟨_, hVc⟩, rfl⟩ := hU
  rw [f.preimage_symm]
  exact hVc.image f.continuous

/-- The product of two prespectral spaces is prespectral. -/
-- after `PrespectralSpace.sigma`
instance PrespectralSpace.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y] : PrespectralSpace (X × Y) :=
  .of_isTopologicalBasis
    (PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis)
    (fun _U hU => by
      obtain ⟨U₁, hU₁, U₂, hU₂, rfl⟩ := Set.mem_image2.mp hU
      exact hU₁.2.prod hU₂.2)

-- end of file
theorem Topology.IsClosedEmbedding.isOpen_and_isCompact_and_preimage_eq {X Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Z] [PrespectralSpace X] [CompactSpace X]
    {f : Z → X} (hf : Topology.IsClosedEmbedding f) {V : Set Z} (h₁ : IsOpen V) (h₂ : IsCompact V) :
    ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ f ⁻¹' U = V := by
  obtain ⟨U', open', hV⟩ := hf.isInducing.isOpen_iff.mp h₁
  obtain ⟨S, Ui, hU', hUi⟩ := PrespectralSpace.isTopologicalBasis.open_eq_iUnion open'
  obtain ⟨T, hT⟩ := IsCompact.elim_finite_subcover h₂ (fun i ↦ f ⁻¹' Ui i)
    (fun i ↦ (hUi i).1.preimage hf.continuous)
    (by simpa [← hV, ← Set.preimage_iUnion] using Set.preimage_mono hU'.subset)
  have := fun i ↦ (hUi i).2.preimage_of_isOpen hf.isProperMap.isSpectralMap (hUi i).1
  have : V = ⋃ i ∈ T, f ⁻¹' Ui i := by
    refine subset_antisymm hT (Set.iUnion₂_subset ?_)
    rw [← hV, hU']
    exact fun _ _ ↦ Set.preimage_mono (Set.subset_iUnion _ _)
  use ⋃ i ∈ T, Ui i, isOpen_biUnion (fun i _ ↦ (hUi i).1),
    T.finite_toSet.isCompact_biUnion (fun i hi ↦ (hUi i).2)
  simp [this]


