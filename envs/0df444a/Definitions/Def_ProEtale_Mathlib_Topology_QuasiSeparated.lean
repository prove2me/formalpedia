-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
-- name    : ProEtale_Mathlib_Topology_QuasiSeparated
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:08.0348+00:00
-- url     : https://prove2.me/theorems/59f3ee3e-50cd-53c1-b2e3-0dbab403c81a
-- title:
--   Quasi-separatedness is preserved by homeomorphisms and by products of prespectral spaces
-- statement:
--   A topological space is **quasi-separated** if the intersection of any two compact open subsets is compact. A space is **prespectral** if its compact open subsets form a basis of the topology.
--
--   Principal results:
--   1. If $\alpha$ is quasi-separated and $\alpha \cong \beta$ is a homeomorphism, then $\beta$ is quasi-separated.
--   2. If $\alpha$ and $\beta$ are quasi-separated and prespectral, then $\alpha \times \beta$ is quasi-separated (using the basis of products of compact opens).
--
--   These are used to show that products such as $T \times X$ with $T$ profinite and $X$ spectral are spectral.
--
--   **Formalization Note** Declarations: `Homeomorph.quasiSeparatedSpace` and the instance `QuasiSeparatedSpace.prod`, with Mathlib's `QuasiSeparatedSpace` and `PrespectralSpace`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/QuasiSeparated.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- Quasi-separatedness transfers along homeomorphisms. -/
-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) :
    QuasiSeparatedSpace β where
  inter_isCompact U V hUo hUc hVo hVc := by
    have hc := QuasiSeparatedSpace.inter_isCompact _ _
      (hUo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hUc)
      (hVo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hVc)
    rw [← f.image_preimage (U ∩ V), Set.preimage_inter]
    exact hc.image f.continuous


-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [PrespectralSpace α]
    [QuasiSeparatedSpace β] [PrespectralSpace β] : QuasiSeparatedSpace (α × β) := by
  let b : ({ U : Set α // IsOpen U ∧ IsCompact U } × { V : Set β // IsOpen V ∧ IsCompact V }) →
      Set (α × β) := fun i ↦ (i.1.1 : Set α) ×ˢ (i.2.1 : Set β)
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := b) ?_ ?_
  · have hbα : IsTopologicalBasis ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α)) :=
      PrespectralSpace.isTopologicalBasis (X := α)
    have hbβ : IsTopologicalBasis ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) :=
      PrespectralSpace.isTopologicalBasis (X := β)
    have hrange : Set.range b =
        Set.image2 (· ×ˢ ·) ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α))
          ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) := by
      ext s
      refine ⟨?_, ?_⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.1.1, i.1.2, i.2.1, i.2.2, rfl⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    simpa [hrange] using hbα.prod hbβ
  · intro i j
    have hA : IsCompact ((i.1.1 : Set α) ∩ (j.1.1 : Set α)) :=
      i.1.2.2.inter_of_isOpen j.1.2.2 i.1.2.1 j.1.2.1
    have hB : IsCompact ((i.2.1 : Set β) ∩ (j.2.1 : Set β)) :=
      i.2.2.2.inter_of_isOpen j.2.2.2 i.2.2.1 j.2.2.1
    simpa [b, Set.prod_inter_prod] using hA.prod hB


