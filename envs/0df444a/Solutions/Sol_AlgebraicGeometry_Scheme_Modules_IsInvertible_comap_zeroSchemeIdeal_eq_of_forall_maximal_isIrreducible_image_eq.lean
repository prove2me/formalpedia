-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1a096467-3d55-58f5-a9b3-ab6aa18a2ca9

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace B2Sol

theorem exists_maximal_isIrreducible_subset {α : Type*} [TopologicalSpace α] {D T : Set α}
    (hT : IsIrreducible T) (hTD : T ⊆ D) :
    ∃ C : Set α, T ⊆ C ∧ Maximal (fun C' : Set α => IsIrreducible C' ∧ C' ⊆ D) C := by
  obtain ⟨m, hTm, hm⟩ :=
    zorn_subset_nonempty { t : Set α | IsPreirreducible t ∧ t ⊆ D }
      (fun c hc hcc _ =>
        ⟨⋃₀ c,
          ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
            let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
            let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
            Or.casesOn (hcc.total hpc hqc)
              (fun hpq : p ⊆ q =>
                let ⟨z, hzp, hzuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
                ⟨z, Set.mem_sUnion_of_mem hzp hqc, hzuv⟩)
              fun hqp : q ⊆ p =>
              let ⟨z, hzp, hzuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
              ⟨z, Set.mem_sUnion_of_mem hzp hpc, hzuv⟩,
            Set.sUnion_subset fun t ht => (hc ht).2⟩,
          fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
      T ⟨hT.isPreirreducible, hTD⟩
  refine ⟨m, hTm, ⟨⟨hT.nonempty.mono hTm, hm.prop.1⟩, hm.prop.2⟩, ?_⟩
  intro u hu hmu
  exact (hm.eq_of_subset ⟨hu.1.isPreirreducible, hu.2⟩ hmu).symm.le

theorem map_germ_ideal_eq_top_of_notMem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (hx : x ∉ I.support) (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U) = ⊤ := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨f, hfI, hxf⟩ := hx
  rw [Ideal.eq_top_iff_one]
  have hu : IsUnit ((X.presheaf.germ U x hxU).hom f) := by
    rwa [X.mem_basicOpen] at hxf
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have hmem : (X.presheaf.germ U x hxU).hom f ∈ Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U) :=
    Ideal.mem_map_of_mem _ hfI
  have := Ideal.mul_mem_left _ v hmem
  rwa [hv] at this

theorem eq_of_closure_singleton_eq {X : Scheme.{u}} {x y : X} (h : closure ({x} : Set X) = closure {y}) : x = y := by
  have h1 : x ⤳ y := specializes_iff_closure_subset.mpr h.ge
  have h2 : y ⤳ x := specializes_iff_closure_subset.mpr h.le
  exact (h1.antisymm h2).eq

end B2Sol

open B2Sol in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0)
    (σ : X ≅ X)
    (hσ : ∀ C : Set X,
      Maximal (fun C' : Set X => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal s).support) C →
        σ.hom.base '' C = C) :
    (Scheme.Modules.zeroSchemeIdeal s).comap σ.hom = Scheme.Modules.zeroSchemeIdeal s := by
  set I := Scheme.Modules.zeroSchemeIdeal s with hI

  have hσD : ∀ y : X, y ∈ (I.support : Set X) → σ.hom.base y ∈ (I.support : Set X) := by
    intro y hy
    obtain ⟨C, hyC, hC⟩ := exists_maximal_isIrreducible_subset (isIrreducible_singleton (x := y)).closure
      (closure_minimal (Set.singleton_subset_iff.mpr hy) I.support.isClosed)
    have h1 := hσ C (hI ▸ hC)
    have : σ.hom.base y ∈ σ.hom.base '' C := ⟨y, hyC (subset_closure (Set.mem_singleton y)), rfl⟩
    rw [h1] at this
    exact hC.1.2 this
  have hσD' : ∀ y : X, y ∈ (I.support : Set X) → σ.inv.base y ∈ (I.support : Set X) := by
    intro y hy
    obtain ⟨C, hyC, hC⟩ := exists_maximal_isIrreducible_subset (isIrreducible_singleton (x := y)).closure
      (closure_minimal (Set.singleton_subset_iff.mpr hy) I.support.isClosed)
    have h1 := hσ C (hI ▸ hC)
    have hyC' : y ∈ C := hyC (subset_closure (Set.mem_singleton y))
    rw [← h1] at hyC'
    obtain ⟨z, hzC, hzy⟩ := hyC'
    have : σ.inv.base y = z := by
      rw [← hzy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [this]
    exact hC.1.2 hzC

  have hM' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ.hom).obj M) := hM.pullback σ.hom
  have hZ' : Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection σ.hom s) = I.comap σ.hom := by
    rw [hI]; exact (hM.comap_zeroSchemeIdeal_monoidalV2 σ.hom s).symm
  symm
  rw [← hZ']
  refine AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
    hX hM hM' s (Scheme.Modules.pullbackSection σ.hom s) hs ?_
  intro x hdim U hxU
  rw [hZ']
  by_cases hxD : x ∈ I.support
  ·
    have hmax := AlgebraicGeometry.Scheme.Modules.IsInvertible.maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
      hM s hs x (hI ▸ hxD) hdim
    have hfix : σ.hom.base x = x := by
      have h1 := hσ (closure {x}) (hI ▸ hmax)
      have h2 : σ.hom.base '' closure {x} = closure {σ.hom.base x} := by
        have e : ((Scheme.homeoOfIso σ) : X → X) = σ.hom.base := funext fun _ => rfl
        have := (Scheme.homeoOfIso σ).image_closure {x}
        rw [e, Set.image_singleton] at this
        exact this
      rw [h2] at h1
      exact eq_of_closure_singleton_eq h1
    haveI : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    haveI : IsDomain (X.presheaf.stalk x) := (hX x).1
    haveI : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
    exact (AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one
      I σ x hfix hdim U hxU).symm
  · have hxD' : x ∉ (I.comap σ.hom).support := by
      intro hx'
      rw [Scheme.IdealSheafData.support_comap] at hx'
      have hx'' : σ.hom.base x ∈ (I.support : Set X) := hx'
      have := hσD' _ hx''
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id] at this
      exact hxD this
    rw [map_germ_ideal_eq_top_of_notMem_support I x hxD U hxU,
      map_germ_ideal_eq_top_of_notMem_support (I.comap σ.hom) x hxD' U hxU]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq (solution)
