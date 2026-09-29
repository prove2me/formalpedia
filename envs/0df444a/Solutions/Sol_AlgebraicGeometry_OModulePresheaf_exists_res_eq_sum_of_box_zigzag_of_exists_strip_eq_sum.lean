-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b6f473d0-3496-5916-baa6-0afe9e55459c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace G2aBody

section Res
variable {P : Scheme.{u}}

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end Res

section Cover

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
  (U : X.Opens) (hU : IsAffineOpen U)

noncomputable def boxCover {n : ℕ} (t : 𝒲.Idx n) : P.OrderedAffineCoverOf (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) where
  ι := 𝒱.ι
  U i := (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) ⊓ p₂ ⁻¹ᵁ 𝒱.U i
  isAffineOpen i := by
    haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
    haveI : IsSeparated (p₁ ≫ fX) := inferInstance
    have h1 : IsAffineOpen (𝒲.inter t) := Scheme.OrderedAffineCover.isAffineOpen_inter (p₁ ≫ fX) 𝒲 t
    have h2 : IsAffineOpen (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) :=
      Scheme.OrderedAffineCover.fiberAffineOpen p₁ fX h1 hU
    exact Scheme.OrderedAffineCover.fiberAffineOpen p₂ fY h2 (𝒱.isAffineOpen i)
  le _ := inf_le_left
  iSup_eq := by
    rw [← inf_iSup_eq, ← Scheme.Hom.preimage_iSup, 𝒱.iSup_eq_top]
    exact le_antisymm inf_le_left (le_inf le_rfl le_top)

variable {fX fY p₁ p₂ 𝒲 𝒱 U}

theorem boxCover_face {n m : ℕ} (t : 𝒲.Idx n) (σ : 𝒱.Idx (m + 1)) (j : Fin (m + 2)) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).face σ j = 𝒱.face σ j := rfl

theorem inter_le_box {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s := by
  refine le_inf (((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s 0).trans inf_le_left) ?_
  calc (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ ⨅ j, p₂ ⁻¹ᵁ 𝒱.U (s.1 j) :=
        le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans inf_le_right
    _ = p₂ ⁻¹ᵁ 𝒱.inter s := (Scheme.OrderedAffineCover.preimage_iInf_fin p₂ _).symm

theorem box_le_inter {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s :=
  le_iInf fun j => le_inf inf_le_left (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le s j)))

theorem inter_le_inter {n n' m : ℕ} (t : 𝒲.Idx n) (t' : 𝒲.Idx n') (h : 𝒲.inter t ≤ 𝒲.inter t')
    (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t').inter s :=
  le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans
    (inf_le_inf_right _ (inf_le_inf_right _ h))

end Cover

end G2aBody

open G2aBody in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (he : ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j))) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by
  classical
  obtain ⟨g, hg⟩ := he
  haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
  haveI : IsSeparated (p₁ ≫ fX) := inferInstance
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)

  let f : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).cochain 0 := fun t s =>
    (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom
      (γ s t - (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)).op).hom (g s))

  have hf : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).d (p₁ ≫ fX) 0 (f t) = 0 := by
    intro t
    funext σ
    rw [Scheme.OrderedAffineCoverOf.d_apply]
    have h1 := congrArg (fun x => (P.presheaf.map (homOfLE
      (inter_le_box hP hU t σ)).op).hom x) (hH σ t)
    have h2 := congrArg (fun x => (P.presheaf.map (homOfLE
      ((inter_le_box hP hU t σ).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right))).op).hom x) (hg σ)
    simp only [map_sum, map_zsmul, map_sub, res_res, f] at h1 h2 ⊢
    rw [Fin.sum_univ_two] at h1 h2 ⊢
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h1 h2 ⊢
    dsimp only [boxCover_face] at h1 h2 ⊢
    show _ = (0 : Γ(P, _))
    linear_combination h2 - h1

  have hglue : ∀ t : 𝒲.Idx 0, ∃ w : Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX) w = f t := by
    intro t
    have hmem : f t ∈ LinearMap.range ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX)) := by
      rw [← Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact LinearMap.mem_ker.mpr (hf t)
    exact LinearMap.mem_range.mp hmem
  choose β hβ using hglue
  have hβ' : ∀ (t : 𝒲.Idx 0) (s : 𝒱.Idx 0) {O : P.Opens}
      (h : O ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s)
      (h₁ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) (h₂ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)
      (h₃ : O ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s),
      (P.presheaf.map (homOfLE h₁).op).hom (β t)
        = (P.presheaf.map (homOfLE h₂).op).hom (γ s t) - (P.presheaf.map (homOfLE h₃).op).hom (g s) := by
    intro t s O h h₁ h₂ h₃
    have := congrArg (fun x => (P.presheaf.map (homOfLE h).op).hom x) (congrFun (hβ t) s)
    simp only [Scheme.OrderedAffineCoverOf.aug_apply, map_sub, res_res, f] at this
    exact this
  refine ⟨β, fun t => ?_⟩
  apply Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t)
  funext s
  simp only [Scheme.OrderedAffineCoverOf.aug_apply, map_sum, map_zsmul, res_res]
  have h3 := congrArg (fun x => (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom x) (hV s t)
  simp only [map_sum, map_zsmul, res_res] at h3
  rw [Fin.sum_univ_two] at h3 ⊢
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h3 ⊢
  have l0 := inter_le_inter hP hU t (𝒲.face t 0) (𝒲.inter_le_inter_face t 0) s
  have l1 := inter_le_inter hP hU t (𝒲.face t 1) (𝒲.inter_le_inter_face t 1) s
  rw [hβ' (𝒲.face t 0) s l0 _ (l0.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right)),
    hβ' (𝒲.face t 1) s l1 _ (l1.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right))]
  linear_combination h3

end S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum (solution)
