-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
-- name    : ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:22.076871+00:00
-- url     : https://prove2.me/theorems/6efd5eed-cb5f-4063-bbfb-6aaf8d1ef0ee
-- title:
--   Discrete Topology Lat Of
-- statement:
--   Definitions and structural lemmas for Discrete Topology Lat Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
namespace ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
theorem embZ_injective : Function.Injective (embZ (E := E)) := by
  intro a b h
  exact RingOfIntegers.coe_injective (mixedEmbedding_injective E h)
theorem mem_latOf {I : Ideal (𝓞 E)} {x : mixedSpace E} : x ∈ latOf I ↔ ∃ α ∈ I, embZ α = x := by
  simp only [latOf, Submodule.mem_map, Submodule.restrictScalars_mem]
scoped instance discreteTopology_latOf (I : Ideal (𝓞 E)) : DiscreteTopology (latOf I) := by
  have hsub : ((latOf I : Set (mixedSpace E))) ⊆ (mixedEmbedding.integerLattice E : Set _) := by
    intro x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact ⟨α, rfl⟩
  exact DiscreteTopology.of_subset (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice E)) hsub
noncomputable def latEquiv (I : Ideal (𝓞 E)) : I ≃ latOf I :=
  Equiv.ofBijective (fun α => ⟨embZ (α : 𝓞 E), mem_latOf.mpr ⟨α, α.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (embZ_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨α, hα, h⟩ := mem_latOf.mp x.2
      exact ⟨⟨α, hα⟩, Subtype.ext h⟩⟩
section Sign
open NumberField.InfinitePlace
end Sign
end ReciprocityTheory.Cheb


