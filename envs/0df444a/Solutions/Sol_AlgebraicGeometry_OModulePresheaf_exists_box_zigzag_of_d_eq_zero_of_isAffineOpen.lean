-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bfa95f3d-89ae-55ff-a47a-28e9f988c54e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace G1SlabZigzagAux

variable {P : Scheme.{u}}

noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (U : X.Opens)

theorem isSeparated_fst (hP : IsPullback p₁ p₂ fX fY) : IsSeparated p₁ :=
  MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)

theorem isAffineOpen_strip (hP : IsPullback p₁ p₂ fX fY) (hU : IsAffineOpen U) {a : ℕ} (σ : 𝒱.Idx a) :
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) := by
  have hV : IsAffineOpen (𝒱.inter σ) := Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of k))
  have hsq := Scheme.Hom.isPullback_resLE hP (US := ⊤) (UT := 𝒱.inter σ) (UX := U)
    (by simp) (by simp) (UY := p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) rfl
  exact .of_isIso hsq.isoPullback.hom

theorem restrict_inter {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R)) [IsSeparated π]
    {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  show (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end Main

end G1SlabZigzagAux

open G1SlabZigzagAux in
theorem solution
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
      (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)),
      (∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
        (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
                (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j))) ∧
      (∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
        (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
                ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t)) ∧
      (∀ ρ : 𝒱.Idx (1 + 1),
        ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e (𝒱.face ρ j)) = 0) := by
  classical

  haveI : IsSeparated p₁ := isSeparated_fst fX fY p₁ p₂ hP
  haveI hπ : IsSeparated (p₁ ≫ fX) := inferInstance
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)

  have hF : ∀ {a : ℕ} (σ : 𝒱.Idx a), IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => isAffineOpen_strip fX fY p₁ p₂ 𝒱 U hP hU σ
  let K : ∀ {a : ℕ} (σ : 𝒱.Idx a), P.OrderedAffineCoverOf (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => 𝒲.restrict (p₁ ≫ fX) (hF σ)
  have hKi : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t = 𝒲.inter t ⊓ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => restrict_inter 𝒲 (p₁ ≫ fX) (hF σ) t
  have hBK : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ (K σ).inter t :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKB : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKW : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b), (K σ).inter t ≤ 𝒲.inter t :=
    fun σ t => (hKB σ t).trans (inf_le_left.trans inf_le_left)

  have step1 : ∀ σ : 𝒱.Idx 0, ∃ g : (K σ).cochain 0,
      (K σ).d (p₁ ≫ fX) 0 g = fun t => rr (hKW σ t) (c t) := by
    intro σ
    have hmem : (fun t => rr (hKW σ t) (c t) : (K σ).cochain 1) ∈
        LinearMap.ker ((K σ).d (p₁ ≫ fX) 1) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have h0' : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (OModulePresheaf.unit (p₁ ≫ fX)).res (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 := by
        have := congrFun hc s
        rwa [OModulePresheaf.d_apply] at this
      have h0 : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 := h0'
      have h1 := congrArg (rr (hKW σ s)) h0
      rw [map_sum, map_zero] at h1
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
      rw [map_zsmul]
      congr 1
      change rr _ (rr _ (c _)) = rr _ (rr _ (c _))
      simp only [rr_rr]
      try rfl
    obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen
      (p₁ ≫ fX) (K σ) (hF σ) 0 hmem
    exact ⟨g, hg⟩
  choose g hg using step1

  let γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => rr (hBK σ t) (g σ t)

  have hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      rr (inf_le_left.trans inf_le_left) (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))
              (γ σ (𝒲.face t j)) := by
    intro σ t
    have h1 := congrFun (hg σ) t
    rw [Scheme.OrderedAffineCoverOf.d_apply] at h1
    have h2 := congrArg (rr (hBK σ t)) h1
    rw [map_sum, rr_rr] at h2
    refine Eq.trans h2.symm (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (g σ _)) = rr _ (rr _ (g σ _))
    simp only [rr_rr]
    try rfl

  have step2 : ∀ σ : 𝒱.Idx 1, ∃ eσ : Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ),
      (K σ).aug (p₁ ≫ fX) eσ = fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) := by
    intro σ
    set η : (K σ).cochain 0 := fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) with hη
    have hmem : η ∈ LinearMap.ker ((K σ).d (p₁ ≫ fX) 0) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have key : ∀ j : Fin (0 + 2),
          ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) •
            rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
              (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))))
              (γ (𝒱.face σ j) (𝒲.face s l))
          = rr (hKW σ s) (c s) := by
        intro j
        have hle : (K σ).inter s ≤ 𝒲.inter s ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter (𝒱.face σ j) :=
          (hKB σ s).trans (inf_le_inf_left _ ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))
        have h3 := congrArg (rr hle) (hV (𝒱.face σ j) s)
        rw [rr_rr, map_sum] at h3
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h3.symm
        rw [map_zsmul]
        congr 1
        change rr _ (rr _ (g _ _)) = rr _ (rr _ (rr _ (g _ _)))
        simp only [rr_rr]
        try rfl
      calc ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) • rr ((K σ).inter_le_inter_face s l) (η ((K σ).face s l))
          = ∑ l : Fin (0 + 2), ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (l : ℕ)) •
              rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
                (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                  ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))))
                (γ (𝒱.face σ j) (𝒲.face s l))) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hη, map_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_zsmul, smul_comm]
            congr 2
            change rr _ (rr _ (rr _ (g _ _))) = rr _ (rr _ (g _ _))
            simp only [rr_rr]
            try rfl
        _ = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • rr (hKW σ s) (c s) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.smul_sum, key j]
        _ = 0 := by
            rw [Fin.sum_univ_two]
            simp
    have hrange : η ∈ LinearMap.range ((K σ).aug (p₁ ≫ fX)) := by
      rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact hmem
    obtain ⟨eσ, heσ⟩ := hrange
    exact ⟨eσ, heσ.trans hη⟩
  choose e he using step2

  have hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))) (γ (𝒱.face σ j) t) := by
    intro σ t
    have h1 := congrFun (he σ) t
    rw [Scheme.OrderedAffineCoverOf.aug_apply] at h1
    have h2 := congrArg (rr (hBK σ t)) h1
    change rr _ (rr _ (e σ)) = _ at h2
    rw [rr_rr, map_sum] at h2
    refine Eq.trans h2 (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (rr _ (g _ _))) = rr _ (rr _ (g _ _))
    simp only [rr_rr]
    try rfl
  refine ⟨γ, e, hV, hH, ?_⟩

  intro ρ
  have hbox : ∀ t : 𝒲.Idx 0,
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)
        (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (inf_le_inf_left (p₁ ⁻¹ᵁ U)
            ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j))) (e (𝒱.face ρ j)))
        = 0 := by
    intro t
    let G := OModulePresheaf.Leray.pullOpen p₂ fY (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
    have hdd := congrFun (LinearMap.congr_fun (OModulePresheaf.Leray.d_d G 𝒱 0)
      (fun σ => γ σ t : G.cochain 𝒱 0)) ρ
    rw [LinearMap.comp_apply, LinearMap.zero_apply, OModulePresheaf.d_apply] at hdd
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hdd
    rw [map_zsmul, OModulePresheaf.d_apply, rr_rr]
    congr 1
    have hle : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter (𝒱.face ρ j) :=
      inf_le_inf_left _ ((Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j))
    have h5 := congrArg (rr hle) (hH (𝒱.face ρ j) t)
    rw [rr_rr, map_sum] at h5
    rw [map_sum]
    refine h5.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_zsmul, map_zsmul]
    congr 1
  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (K ρ)
  rw [map_zero]
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Pi.zero_apply]
  change rr ((K ρ).inter_le_base t) _ = 0
  have hfac : rr ((K ρ).inter_le_base t)
      = (rr (hKB ρ t)).comp (rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)) := by
    ext x
    exact (rr_rr _ _ x).symm
  rw [hfac, RingHom.comp_apply, hbox t, map_zero]

end S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen (solution)
