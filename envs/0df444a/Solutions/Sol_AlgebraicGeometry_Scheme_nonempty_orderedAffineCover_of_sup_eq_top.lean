-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2a01df40-f6fb-51e3-8ca1-fe7104e2259f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace K2SOL

theorem main
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover) :
    Nonempty ((U : Scheme.{u}).OrderedAffineCover) := by
  classical

  have hX : IsCompact (Set.univ : Set X) := by
    rw [← TopologicalSpace.Opens.coe_top, ← 𝔛.iSup_eq_top, TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => (𝔛.isAffineOpen i).isCompact

  have hK₁ : IsCompact ((V : Set X)ᶜ) :=
    hX.of_isClosed_subset V.isOpen.isClosed_compl (Set.subset_univ _)

  have hK₂ : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    have e : (U ⊓ V : X.Opens) = ⨆ i, (U ⊓ V).ι ''ᵁ 𝔚.U i := by
      rw [← Scheme.Hom.image_iSup, 𝔚.iSup_eq_top, Scheme.Opens.ι_image_top]
    rw [e, TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => ((𝔚.isAffineOpen i).image_of_isOpenImmersion _).isCompact

  have hUV' : (U : Set X) ∪ (V : Set X) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, hUV, TopologicalSpace.Opens.coe_top]
  have hUeq : (U : Set X) = (V : Set X)ᶜ ∪ ((U ⊓ V : X.Opens) : Set X) := by
    ext x
    rw [TopologicalSpace.Opens.coe_inf, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    constructor
    · intro hx
      by_cases hv : x ∈ (V : Set X)
      · exact Or.inr ⟨hx, hv⟩
      · exact Or.inl hv
    · rintro (hv | ⟨hu, -⟩)
      · have hx : x ∈ (U : Set X) ∪ (V : Set X) := by rw [hUV']; exact Set.mem_univ x
        exact hx.resolve_right hv
      · exact hu
  have hUc : IsCompact (U : Set X) := by rw [hUeq]; exact hK₁.union hK₂

  let ι₀ : Type u := {W : X.Opens // IsAffineOpen W ∧ W ≤ U}
  have hcov : (U : Set X) ⊆ ⋃ i : ι₀, (i.1 : Set X) := by
    intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ U from hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW, hWU⟩, hxW⟩
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun i : ι₀ => (i.1 : Set X)) (fun i => i.1.isOpen) hcov

  let ι : Type u := {i : ι₀ // i ∈ t}
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  refine ⟨{ ι := ι
            U := fun j => U.ι ⁻¹ᵁ j.1.1
            isAffineOpen := fun j => j.1.2.1.preimage_of_isOpenImmersion U.ι
              (by rw [Scheme.Opens.opensRange_ι]; exact j.1.2.2)
            iSup_eq_top := ?_ }⟩
  rw [eq_top_iff]
  rintro y -
  have hy : U.ι.base y ∈ (U : Set X) := by
    rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩

end K2SOL

theorem solution
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover) :
    Nonempty ((U : Scheme.{u}).OrderedAffineCover) :=
  K2SOL.main U V hUV 𝔛 𝔚

end S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top (solution)
