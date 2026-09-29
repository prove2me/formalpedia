-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_iso_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5abf31f9-5c14-59eb-9183-32b7fa0ebf53

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry NeronModelInfra CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.support_comap Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.support_ker Spec Scheme Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules Scheme.Opens Scheme.IdealSheafData isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Modules.pullbackTensorObjIso Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range"
namespace TwoGluedCurves
namespace K5Far
p2m_open "AlgebraicGeometry"

theorem comap_ker_eq_top_of_range_subset_compl {X C T : Scheme.{u}} (i : C ⟶ X)
    (p : T ⟶ X) [IsClosedImmersion p] (hp : Set.range p.base ⊆ (Set.range i.base)ᶜ) :
    p.ker.comap i = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [Scheme.IdealSheafData.support_comap] at hc
  have hc' : i.base c ∈ (p.ker.support : Set X) := hc
  rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hc'
  exact (hp hc' ⟨c, rfl⟩).elim

theorem isPullback_of_mono {X C T : Scheme.{u}} (i : C ⟶ X) [Mono i] (p₂ : T ⟶ C) :
    IsPullback p₂ (𝟙 T) i (p₂ ≫ i) := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_)
    (fun s => by simp) (fun s m _ h₂ => by simpa using h₂))
  exact ((cancel_mono i).mp (by rw [Category.assoc]; exact s.condition.symm))

theorem comap_ker_eq_ker_of_comp_eq {X C T : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (p : T ⟶ X) [IsClosedImmersion p] (p₂ : T ⟶ C) (hp₂ : p₂ ≫ i = p) :
    p.ker.comap i = p₂.ker := by
  subst hp₂
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hpb := isPullback_of_mono i p₂
  rw [← hpb.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso]

theorem isInvertible_ker_of_comp_eq {X C T : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (W : X.Opens) (hoi : IsOpenImmersion ((i ⁻¹ᵁ W).ι ≫ i))
    (p : T ⟶ X) [IsClosedImmersion p] (hpW : Set.range p.base ⊆ W) (p₂ : T ⟶ C) (hp₂ : p₂ ≫ i = p)
    (hpi : p.ker.IsInvertible) : p₂.ker.IsInvertible := by
  rw [← comap_ker_eq_ker_of_comp_eq i p p₂ hp₂]
  haveI := hoi
  refine Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range (i ⁻¹ᵁ W).ι _ ?_ ?_
  · intro c hc
    rw [Scheme.IdealSheafData.support_comap] at hc
    have hc' : i.base c ∈ (p.ker.support : Set X) := hc
    rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hc'
    rw [Scheme.Opens.range_ι]
    exact hpW hc'
  · rw [← Scheme.IdealSheafData.comap_comp]
    exact hpi.comap_of_isOpenImmersion _

section KPoints

variable {k : Type u} [Field k] {X C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (i₂ : C₂ ⟶ X)

scoped instance isClosedImmersion_kpoint (p : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) :
    IsClosedImmersion p.1 :=
  isClosedImmersion_of_comp_eq_id x p.1 p.2

theorem comap_ker_eq_top_of_range_subset_compl' (p : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _})
    (hp : Set.range p.1.base ⊆ (Set.range i₂.base)ᶜ) : p.1.ker.comap i₂ = ⊤ :=
  haveI := isClosedImmersion_kpoint x p
  comap_ker_eq_top_of_range_subset_compl i₂ p.1 hp

theorem comap_ker_eq_ker_of_comp_eq' [IsClosedImmersion i₂] (p : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _})
    (p₂ : Spec (CommRingCat.of k) ⟶ C₂) (hp₂ : p₂ ≫ i₂ = p.1) : p.1.ker.comap i₂ = p₂.ker :=
  haveI := isClosedImmersion_kpoint x p
  comap_ker_eq_ker_of_comp_eq i₂ p.1 p₂ hp₂

theorem isInvertible_ker_of_comp_eq' [IsClosedImmersion i₂] (W₂ : X.Opens)
    (hoi : IsOpenImmersion ((i₂ ⁻¹ᵁ W₂).ι ≫ i₂))
    (p : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hpW : Set.range p.1.base ⊆ W₂)
    (p₂ : Spec (CommRingCat.of k) ⟶ C₂) (hp₂ : p₂ ≫ i₂ = p.1) (hpi : p.1.ker.IsInvertible) :
    p₂.ker.IsInvertible :=
  haveI := isClosedImmersion_kpoint x p
  isInvertible_ker_of_comp_eq i₂ W₂ hoi p.1 hpW p₂ hp₂ hpi

end KPoints

end AlgebraicGeometry.TwoGluedCurves.K5Far
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry.TwoGluedCurves P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry.TwoGluedCurves.K5Far"
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry.TwoGluedCurves"
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.AlgebraicGeometry"

open AlgebraicGeometry.TwoGluedCurves.K5Far in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (W₂ : X.Opens) (hW₂ : (W₂ : Set X) = (Set.range i₁.1.base)ᶜ) (hoi : IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))
    (L₀ : X.Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)

    (r : ℕ) (ε₀ : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hε₀ : Set.range ε₀.1.base ⊆ (Set.range i₂.1.base)ᶜ) (hε₀i : ε₀.1.ker.IsInvertible)
    {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv : ∀ j, Set.range (v j).1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hvi : ∀ j, (v j).1.ker.IsInvertible)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hq : ∀ m, Set.range (q m).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hqi : ∀ m, (q m).1.ker.IsInvertible) (q₂ : Fin d → {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) (hq₂ : ∀ m, (q₂ m).1 ≫ i₂.1 = (q m).1)
    {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv' : ∀ j, Set.range (v' j).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hv'i : ∀ j, (v' j).1.ker.IsInvertible) (v₂ : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) (hv₂ : ∀ j, (v₂ j).1 ≫ i₂.1 = (v' j).1) :
    Nonempty (
      (Scheme.Modules.pullback i₂.1).obj
          (L₀ ⊗ (((ε₀.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ≅
      (Scheme.Modules.pullback i₂.1).obj L₀ ⊗
        ((∏ ml : Fin d × Fin r', (q₂ ml.1).1.ker).invModule ⊗ (∏ j, (v₂ j).1.ker).module)) := by
  classical
  set A : X.IdealSheafData := (ε₀.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r' with hA
  set Bm : X.IdealSheafData := (∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker) with hBm

  have hprod : ∀ {Y : Scheme.{u}} {κ : Type} (s : Finset κ) (I : κ → Y.IdealSheafData),
      (∀ i ∈ s, (I i).IsInvertible) → (∏ i ∈ s, I i).IsInvertible := by
    intro Y κ s I h
    induction s using Finset.induction_on with
    | empty => simpa using Scheme.IdealSheafData.isInvertible_top
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hAi : A.IsInvertible :=
    (hε₀i.pow r).mul ((hprod Finset.univ _ fun m _ => hqi m).pow r')
  have hBi : Bm.IsInvertible :=
    (hprod Finset.univ _ fun j _ => hvi j).mul (hprod Finset.univ _ fun j _ => hv'i j)

  have e2 : (Scheme.Modules.pullback i₂.1).obj (L₀ ⊗ (A.invModule ⊗ Bm.module)) ≅
      (Scheme.Modules.pullback i₂.1).obj L₀ ⊗
        ((Scheme.Modules.pullback i₂.1).obj A.invModule ⊗ (Scheme.Modules.pullback i₂.1).obj Bm.module) :=
    Scheme.Modules.pullbackTensorObjIso i₂.1 L₀ (A.invModule ⊗ Bm.module) ≪≫
      ((Iso.refl _) ⊗ᵢ Scheme.Modules.pullbackTensorObjIso i₂.1 A.invModule Bm.module)

  have comap_prod : ∀ {κ : Type} (s : Finset κ) (I : κ → X.IdealSheafData),
      (∏ i ∈ s, I i).comap i₂.1 = ∏ i ∈ s, (I i).comap i₂.1 := by
    intro κ s I
    induction s using Finset.induction_on with
    | empty => simp [Scheme.IdealSheafData.comap_top]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.comap_mul, ih]
  have comap_pow : ∀ (I : X.IdealSheafData) (n : ℕ), (I ^ n).comap i₂.1 = (I.comap i₂.1) ^ n := by
    intro I n
    induction n with
    | zero => simp [Scheme.IdealSheafData.comap_top]
    | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

  have hε₀c : ε₀.1.ker.comap i₂.1 = ⊤ := comap_ker_eq_top_of_range_subset_compl' x i₂.1 ε₀ hε₀
  have hvc : ∀ j, (v j).1.ker.comap i₂.1 = ⊤ := fun j => comap_ker_eq_top_of_range_subset_compl' x i₂.1 (v j) (hv j)
  have hqc : ∀ m, (q m).1.ker.comap i₂.1 = (q₂ m).1.ker := fun m => comap_ker_eq_ker_of_comp_eq' x i₂.1 (q m) (q₂ m).1 (hq₂ m)
  have hv'c : ∀ j, (v' j).1.ker.comap i₂.1 = (v₂ j).1.ker := fun j => comap_ker_eq_ker_of_comp_eq' x i₂.1 (v' j) (v₂ j).1 (hv₂ j)
  have h4a : A.comap i₂.1 = ∏ ml : Fin d × Fin r', (q₂ ml.1).1.ker := by
    rw [hA, Scheme.IdealSheafData.comap_mul, comap_pow, comap_pow, hε₀c, comap_prod,
      ← Scheme.IdealSheafData.one_eq_top, one_pow, one_mul]
    simp only [hqc]
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
  have h4b : Bm.comap i₂.1 = ∏ j, (v₂ j).1.ker := by
    rw [hBm, Scheme.IdealSheafData.comap_mul, comap_prod, comap_prod]
    simp only [hvc, hv'c, ← Scheme.IdealSheafData.one_eq_top, Finset.prod_const_one, one_mul]

  have hW₂' : ∀ (p : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}), Set.range p.1.base ⊆ (Set.range i₁.1.base)ᶜ →
      Set.range p.1.base ⊆ W₂ := fun p hp z hz => by
    have : z ∈ (W₂ : Set X) := by rw [hW₂]; exact hp hz
    exact this
  have hq₂i : ∀ m, (q₂ m).1.ker.IsInvertible := fun m =>
    isInvertible_ker_of_comp_eq' x i₂.1 W₂ hoi (q m) (hW₂' (q m) (hq m)) (q₂ m).1 (hq₂ m) (hqi m)
  have hv₂i : ∀ j, (v₂ j).1.ker.IsInvertible := fun j =>
    isInvertible_ker_of_comp_eq' x i₂.1 W₂ hoi (v' j) (hW₂' (v' j) (hv' j)) (v₂ j).1 (hv₂ j) (hv'i j)
  have hAi' : (A.comap i₂.1).IsInvertible := by
    rw [h4a]; exact hprod Finset.univ _ fun ml _ => hq₂i ml.1
  have hBi' : (Bm.comap i₂.1).IsInvertible := by
    rw [h4b]; exact hprod Finset.univ _ fun j _ => hv₂i j

  obtain ⟨e3a⟩ := hAi.nonempty_pullback_invModule_iso i₂.1 hAi'
  haveI := hBi.isIso_pullbackModuleComparison i₂.1 hBi'
  let e3b : (Scheme.Modules.pullback i₂.1).obj Bm.module ≅ (Bm.comap i₂.1).module :=
    asIso (Bm.pullbackModuleComparison i₂.1)

  refine ⟨e2 ≪≫ ?_⟩
  rw [← h4a, ← h4b]
  exact (Iso.refl _) ⊗ᵢ (e3a ⊗ᵢ e3b)

end S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd (solution)
