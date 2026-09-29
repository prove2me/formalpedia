-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/87e99cff-749f-5cae-ba66-d1cffbd5fa41

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace G3Body

variable {Y P : Scheme.{u}}

theorem res_res {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x)
      = (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_appLE (f : Y ⟶ P) {U : P.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(P, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom y) = (f.appLE U W (h.trans e)).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res (f : Y ⟶ P) {U U' : P.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(P, U')) :
    (f.appLE U V e).hom ((P.presheaf.map (homOfLE h).op).hom y)
      = (f.appLE U' V (e.trans (f.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem app_eq_appLE' (f : Y ⟶ P) (U : P.Opens) (y : Γ(P, U)) :
    (f.app U).hom y = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom y := by
  rw [Scheme.Hom.app_eq_appLE]

theorem res_app_eq_appLE (f : Y ⟶ P) (U : P.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (y : Γ(P, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app U).hom y) = (f.appLE U W h).hom y := by
  rw [app_eq_appLE', res_appLE]

end G3Body

open G3Body in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x₀ : Spec (CommRingCat.of k) ⟶ X)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU₀ : x₀ ⁻¹ᵁ U = ⊤)
    (γ : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (e : ∀ σ : (𝒲.comap iY).Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (hV : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : (𝒲.comap iY).Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j)))).op).hom (γ ((𝒲.comap iY).face σ j) t)) :
    ∃ g : ∀ i : (𝒲.comap iY).Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter i)),
      ∀ σ : (𝒲.comap iY).Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j))))).op).hom (g ((𝒲.comap iY).face σ j)) := by
  classical
  obtain ⟨b, hb⟩ := hcY
  have hpre2 : ∀ W : Y.Opens, iY ⁻¹ᵁ (p₂ ⁻¹ᵁ W) = W := fun W => by
    rw [← Scheme.Hom.comp_preimage, hiY₂]; rfl
  have hpre1 : iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hiY₁, Scheme.Hom.comp_preimage, hU₀]; rfl

  have L1 : ∀ {n : ℕ} (s : 𝒲.Idx n),
      iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s) ≤ (𝒲.comap iY).inter s := fun s =>
    (iY.preimage_mono inf_le_right).trans (hpre2 _).le
  have LV : ∀ {n : ℕ} (s : 𝒲.Idx n), (𝒲.comap iY).inter s ≤ iY ⁻¹ᵁ 𝒲.inter s := fun s =>
    𝒲.comap_inter_le iY s

  have L2 : ∀ {n n' m : ℕ} (s : 𝒲.Idx n) (s' : 𝒲.Idx n') (t : 𝒲.Idx m),
      (𝒲.comap iY).inter s ≤ (𝒲.comap iY).inter s' →
      (𝒲.comap iY).inter s ≤ (𝒲.comap iY).inter t →
      iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s)
        ≤ iY ⁻¹ᵁ (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter s') :=
    fun s s' t h1 h2 => by
      change iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) ⊓ iY ⁻¹ᵁ (p₂ ⁻¹ᵁ (𝒲.comap iY).inter s)
          ≤ iY ⁻¹ᵁ 𝒲.inter t ⊓ iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U) ⊓ iY ⁻¹ᵁ (p₂ ⁻¹ᵁ (𝒲.comap iY).inter s')
      exact le_inf (le_inf ((L1 s).trans (h2.trans (LV t))) inf_le_left)
        (inf_le_right.trans (iY.preimage_mono (p₂.preimage_mono h1)))
  refine ⟨fun i => (iY.appLE _ _ (L2 i i i le_rfl le_rfl)).hom (γ i i)
      - (Y.presheaf.map (homOfLE (L1 i)).op).hom (b i), fun σ => ?_⟩
  have hσ₀ : (𝒲.comap iY).inter σ ≤ (𝒲.comap iY).inter (𝒲.face σ 0) :=
    (𝒲.comap iY).inter_le_inter_face σ 0
  have hσ₁ : (𝒲.comap iY).inter σ ≤ (𝒲.comap iY).inter (𝒲.face σ 1) :=
    (𝒲.comap iY).inter_le_inter_face σ 1

  have hE := congrArg
    (fun x => (iY.appLE _ (iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
      (L2 σ σ (𝒲.face σ 1) le_rfl hσ₁)).hom x) (hH σ (𝒲.face σ 1))
  simp only [map_sum, map_zsmul, appLE_res] at hE
  rw [Fin.sum_univ_two] at hE
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hE

  have hC := congrArg
    (fun x => (iY.appLE _ (iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
      (L2 σ (𝒲.face σ 0) σ hσ₀ le_rfl)).hom x) (hV (𝒲.face σ 0) σ)
  simp only [map_sum, map_zsmul, appLE_res] at hC
  rw [Fin.sum_univ_two] at hC
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hC

  have hD0 : ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (Y.presheaf.map (homOfLE ((𝒲.comap iY).inter_le_inter_face σ j)).op).hom
        (b ((𝒲.comap iY).face σ j))
      = (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY σ)).op).hom ((iY.app (𝒲.inter σ)).hom (c σ)) := by
    have := congrFun hb σ
    rw [OModulePresheaf.d_apply] at this
    exact this
  have hD := congrArg (fun x => (Y.presheaf.map (homOfLE (L1 σ)).op).hom x) hD0
  simp only [map_sum, map_zsmul, res_res, res_app_eq_appLE, res_appLE] at hD
  rw [Fin.sum_univ_two] at hD
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hD

  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_sub,
    res_appLE, res_res, app_eq_appLE']
  dsimp only [Scheme.OrderedAffineCover.comap_face] at hE hC hD ⊢
  linear_combination hE + hC + hD

end S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq (solution)
