-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_smooth_isPullback_of_local_lifts_of_overlap_isos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/981e4f3b-5da3-5aae-9cff-2e82f74c99a3

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace OB4bAux

section Restr

variable {Y Y' : Scheme.{u}} {A C : Y.Opens} {A' C' : Y'.Opens}

noncomputable def restr (hC : C ≤ A) (hC' : C' ≤ A') (ψ : (↑A : Scheme.{u}) ⟶ ↑A')
    (hψ : ∀ x : ↑A, x.1 ∈ C → (ψ.base x).1 ∈ C') : (↑C : Scheme.{u}) ⟶ ↑C' :=
  IsOpenImmersion.lift (Y'.homOfLE hC') (Y.homOfLE hC ≫ ψ) (by
    rintro _ ⟨x, rfl⟩
    have hm : ((Y.homOfLE hC ≫ ψ).base x).1 ∈ C' := by
      rw [Scheme.Hom.comp_apply]
      exact hψ _ (by rw [Scheme.homOfLE_apply]; exact x.2)
    exact ⟨⟨_, hm⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩)

variable (hC : C ≤ A) (hC' : C' ≤ A') (ψ : (↑A : Scheme.{u}) ⟶ ↑A')
  (hψ : ∀ x : ↑A, x.1 ∈ C → (ψ.base x).1 ∈ C')

@[reassoc]
theorem restr_fac : restr hC hC' ψ hψ ≫ Y'.homOfLE hC' = Y.homOfLE hC ≫ ψ :=
  IsOpenImmersion.lift_fac _ _ _

theorem restr_val (x : ↑C) : ((restr hC hC' ψ hψ).base x).1 = (ψ.base ((Y.homOfLE hC).base x)).1 := by
  have h := restr_fac hC hC' ψ hψ
  have h' : ((restr hC hC' ψ hψ ≫ Y'.homOfLE hC').base x).1 = ((Y.homOfLE hC ≫ ψ).base x).1 := by rw [h]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.homOfLE_apply] at h'

theorem restr_unique {χ : (↑C : Scheme.{u}) ⟶ ↑C'} (hχ : χ ≫ Y'.homOfLE hC' = Y.homOfLE hC ≫ ψ) :
    χ = restr hC hC' ψ hψ := by
  rw [← cancel_mono (Y'.homOfLE hC'), hχ, restr_fac]

end Restr

theorem restr_eq_id {Y : Scheme.{u}} {A C : Y.Opens} (hC : C ≤ A) (ψ : (↑A : Scheme.{u}) ⟶ ↑A)
    (hψ : ∀ x : ↑A, x.1 ∈ C → (ψ.base x).1 ∈ C) (h1 : ψ = 𝟙 _) :
    restr hC hC ψ hψ = 𝟙 _ := by
  rw [← cancel_mono (Y.homOfLE hC), restr_fac, h1]; simp

theorem restr_comp {Y Y' Y'' : Scheme.{u}} {A C : Y.Opens} {A' C' : Y'.Opens} {A'' C'' : Y''.Opens}
    (hC : C ≤ A) (hC' : C' ≤ A') (hC'' : C'' ≤ A'')
    (ψ : (↑A : Scheme.{u}) ⟶ ↑A') (hψ : ∀ x : ↑A, x.1 ∈ C → (ψ.base x).1 ∈ C')
    (ψ' : (↑A' : Scheme.{u}) ⟶ ↑A'') (hψ' : ∀ x : ↑A', x.1 ∈ C' → (ψ'.base x).1 ∈ C'')
    (hψψ' : ∀ x : ↑A, x.1 ∈ C → ((ψ ≫ ψ').base x).1 ∈ C'') :
    restr hC hC' ψ hψ ≫ restr hC' hC'' ψ' hψ' = restr hC hC'' (ψ ≫ ψ') hψψ' := by
  rw [← cancel_mono (Y''.homOfLE hC'')]
  simp only [Category.assoc, restr_fac, restr_fac_assoc]

theorem homOfLE_restr {Y Y' : Scheme.{u}} {A C D : Y.Opens} {A' C' D' : Y'.Opens}
    (hC : C ≤ A) (hC' : C' ≤ A') (hD : D ≤ C) (hD' : D' ≤ C')
    (ψ : (↑A : Scheme.{u}) ⟶ ↑A') (hψ : ∀ x : ↑A, x.1 ∈ C → (ψ.base x).1 ∈ C')
    (hψD : ∀ x : ↑A, x.1 ∈ D → (ψ.base x).1 ∈ D') :
    Y.homOfLE hD ≫ restr hC hC' ψ hψ = restr (hD.trans hC) (hD'.trans hC') ψ hψD ≫ Y'.homOfLE hD' := by
  rw [← cancel_mono (Y'.homOfLE hC')]
  simp only [Category.assoc, restr_fac, Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE_assoc]

section T

variable {X₀ : Scheme.{u}} (𝒰 : X₀.OrderedAffineCover) (Y : 𝒰.ι → Scheme.{u})
  (V : ∀ i, X₀.Opens → (Y i).Opens) (hVm : ∀ i, Monotone (V i))
  (φ : ∀ (i j : 𝒰.ι), i < j → ((↑(V i (𝒰.U i ⊓ 𝒰.U j)) : Scheme.{u}) ≅ ↑(V j (𝒰.U i ⊓ 𝒰.U j))))

include hVm in
theorem V_swap (k i j : 𝒰.ι) : V k (𝒰.U i ⊓ 𝒰.U j) ≤ V k (𝒰.U j ⊓ 𝒰.U i) :=
  hVm k (le_inf inf_le_right inf_le_left)

noncomputable def t (i j : 𝒰.ι) : (↑(V i (𝒰.U i ⊓ 𝒰.U j)) : Scheme.{u}) ⟶ ↑(V j (𝒰.U j ⊓ 𝒰.U i)) :=
  if h : i < j then (φ i j h).hom ≫ (Y j).homOfLE (V_swap 𝒰 Y V hVm j i j)
  else if h' : j < i then (Y i).homOfLE (V_swap 𝒰 Y V hVm i i j) ≫ (φ j i h').inv
  else eqToHom (by cases le_antisymm (not_lt.1 h') (not_lt.1 h); rfl)

theorem t_of_lt {i j : 𝒰.ι} (h : i < j) :
    t 𝒰 Y V hVm φ i j = (φ i j h).hom ≫ (Y j).homOfLE (V_swap 𝒰 Y V hVm j i j) := dif_pos h

theorem t_of_gt {i j : 𝒰.ι} (h : j < i) :
    t 𝒰 Y V hVm φ i j = (Y i).homOfLE (V_swap 𝒰 Y V hVm i i j) ≫ (φ j i h).inv := by
  rw [t, dif_neg (not_lt.2 h.le), dif_pos h]

theorem t_self (i : 𝒰.ι) : t 𝒰 Y V hVm φ i i = 𝟙 _ := by
  rw [t, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]; rfl

theorem t_inv (i j : 𝒰.ι) : t 𝒰 Y V hVm φ i j ≫ t 𝒰 Y V hVm φ j i = 𝟙 _ := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [t_of_lt 𝒰 Y V hVm φ h, t_of_gt 𝒰 Y V hVm φ h]
    simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
    rw [Scheme.homOfLE_rfl, Category.id_comp, Iso.hom_inv_id]
  · rw [t_self]; simp
  · rw [t_of_gt 𝒰 Y V hVm φ h, t_of_lt 𝒰 Y V hVm φ h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl]

variable (hφV : ∀ (i j : 𝒰.ι) (h : i < j) (W' : X₀.Opens),
    (φ i j h).hom ⁻¹ᵁ ((V j (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V j W') = (V i (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V i W')

include hφV in
theorem φ_mem {i j : 𝒰.ι} (h : i < j) (W' : X₀.Opens) (x : ↑(V i (𝒰.U i ⊓ 𝒰.U j))) :
    x.1 ∈ V i W' ↔ ((φ i j h).hom.base x).1 ∈ V j W' := by
  have e := hφV i j h W'
  constructor
  · intro hx
    have hx' : x ∈ (φ i j h).hom ⁻¹ᵁ ((V j (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V j W') := by rw [e]; exact hx
    exact hx'
  · intro hx
    have hx' : x ∈ (φ i j h).hom ⁻¹ᵁ ((V j (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V j W') := hx
    rw [e] at hx'
    exact hx'

include hφV in
theorem φinv_mem {i j : 𝒰.ι} (h : i < j) (W' : X₀.Opens) (y : ↑(V j (𝒰.U i ⊓ 𝒰.U j))) :
    y.1 ∈ V j W' ↔ ((φ i j h).inv.base y).1 ∈ V i W' := by
  rw [φ_mem 𝒰 Y V φ hφV h W' ((φ i j h).inv.base y), ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

include hφV in

theorem t_mem (i j : 𝒰.ι) (W' : X₀.Opens) (x : ↑(V i (𝒰.U i ⊓ 𝒰.U j))) :
    x.1 ∈ V i W' ↔ ((t 𝒰 Y V hVm φ i j).base x).1 ∈ V j W' := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [t_of_lt 𝒰 Y V hVm φ h, Scheme.Hom.comp_apply, Scheme.homOfLE_apply]
    exact φ_mem 𝒰 Y V φ hφV h W' x
  · rw [t_self]; rfl
  · rw [t_of_gt 𝒰 Y V hVm φ h, Scheme.Hom.comp_apply, ← φinv_mem 𝒰 Y V φ hφV h W',
      Scheme.homOfLE_apply]

end T

section R

variable {X₀ : Scheme.{u}} (𝒰 : X₀.OrderedAffineCover) (Y : 𝒰.ι → Scheme.{u})
  (V : ∀ i, X₀.Opens → (Y i).Opens) (hVm : ∀ i, Monotone (V i))
  (φ : ∀ (i j : 𝒰.ι), i < j → ((↑(V i (𝒰.U i ⊓ 𝒰.U j)) : Scheme.{u}) ≅ ↑(V j (𝒰.U i ⊓ 𝒰.U j))))
  (hφV : ∀ (i j : 𝒰.ι) (h : i < j) (W' : X₀.Opens),
    (φ i j h).hom ⁻¹ᵁ ((V j (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V j W') = (V i (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V i W')

theorem swap_le (i j : 𝒰.ι) : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j ⊓ 𝒰.U i := le_inf inf_le_right inf_le_left

noncomputable def R (i j : 𝒰.ι) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U j) :
    (↑(V i W') : Scheme.{u}) ⟶ ↑(V j W') :=
  restr (hVm i hW) (hVm j (hW.trans (swap_le 𝒰 i j))) (t 𝒰 Y V hVm φ i j)
    (fun x hx => (t_mem 𝒰 Y V hVm φ hφV i j W' x).1 hx)

@[reassoc]
theorem R_fac (i j : 𝒰.ι) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U j) :
    R 𝒰 Y V hVm φ hφV i j hW ≫ (Y j).homOfLE (hVm j (hW.trans (swap_le 𝒰 i j))) =
      (Y i).homOfLE (hVm i hW) ≫ t 𝒰 Y V hVm φ i j :=
  restr_fac _ _ _ _

@[reassoc]
theorem R_ι (i j : 𝒰.ι) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U j) :
    R 𝒰 Y V hVm φ hφV i j hW ≫ (V j W').ι =
      (Y i).homOfLE (hVm i hW) ≫ t 𝒰 Y V hVm φ i j ≫ (V j (𝒰.U j ⊓ 𝒰.U i)).ι := by
  rw [← Scheme.homOfLE_ι (Y j) (hVm j (hW.trans (swap_le 𝒰 i j))), R_fac_assoc]

@[reassoc]
theorem homOfLE_R (i j : 𝒰.ι) {W' W'' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U j) (h : W'' ≤ W') :
    (Y i).homOfLE (hVm i h) ≫ R 𝒰 Y V hVm φ hφV i j hW =
      R 𝒰 Y V hVm φ hφV i j (h.trans hW) ≫ (Y j).homOfLE (hVm j h) :=
  homOfLE_restr _ _ _ _ _ _ _

theorem R_self (i : 𝒰.ι) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U i) : R 𝒰 Y V hVm φ hφV i i hW = 𝟙 _ :=
  restr_eq_id _ _ _ (t_self 𝒰 Y V hVm φ i)

theorem R_R_symm (i j : 𝒰.ι) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U i ⊓ 𝒰.U j) (hW' : W' ≤ 𝒰.U j ⊓ 𝒰.U i) :
    R 𝒰 Y V hVm φ hφV i j hW ≫ R 𝒰 Y V hVm φ hφV j i hW' = 𝟙 _ := by
  rw [R, R, restr_comp]
  · exact restr_eq_id _ _ _ (t_inv 𝒰 Y V hVm φ i j)
  · intro x hx
    rw [t_inv]; exact hx

variable (hcocR : ∀ (a b c : 𝒰.ι), a < b → b < c →
      ∃ (W : X₀.Opens) (_ : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ W) (h1 : W ≤ 𝒰.U a ⊓ 𝒰.U b)
        (h2 : W ≤ 𝒰.U b ⊓ 𝒰.U c) (h3 : W ≤ 𝒰.U a ⊓ 𝒰.U c),
        R 𝒰 Y V hVm φ hφV a c h3 = R 𝒰 Y V hVm φ hφV a b h1 ≫ R 𝒰 Y V hVm φ hφV b c h2)

theorem R_eq_of_fac {a b : 𝒰.ι} (hab : a < b) {W' : X₀.Opens} (hW : W' ≤ 𝒰.U a ⊓ 𝒰.U b)
    (ρ : (↑(V a W') : Scheme.{u}) ⟶ ↑(V b W'))
    (hρ : ρ ≫ (Y b).homOfLE (hVm b hW) = (Y a).homOfLE (hVm a hW) ≫ (φ a b hab).hom) :
    ρ = R 𝒰 Y V hVm φ hφV a b hW := by
  refine restr_unique _ _ _ _ ?_
  rw [t_of_lt 𝒰 Y V hVm φ hab, ← Category.assoc, ← hρ, Category.assoc, Scheme.homOfLE_homOfLE]

include hcocR in

theorem R_sorted {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) {W' : X₀.Opens}
    (h1 : W' ≤ 𝒰.U a ⊓ 𝒰.U b) (h2 : W' ≤ 𝒰.U b ⊓ 𝒰.U c) (h3 : W' ≤ 𝒰.U a ⊓ 𝒰.U c) :
    R 𝒰 Y V hVm φ hφV a c h3 = R 𝒰 Y V hVm φ hφV a b h1 ≫ R 𝒰 Y V hVm φ hφV b c h2 := by
  obtain ⟨W, hW0, g1, g2, g3, hρ⟩ := hcocR a b c hab hbc
  have hW : W' ≤ W := (le_inf h1 (h2.trans inf_le_right)).trans hW0
  rw [← cancel_mono ((Y c).homOfLE (hVm c hW)), Category.assoc,
    ← homOfLE_R 𝒰 Y V hVm φ hφV b c g2 hW, ← homOfLE_R 𝒰 Y V hVm φ hφV a c g3 hW, hρ,
    ← homOfLE_R_assoc 𝒰 Y V hVm φ hφV a b g1 hW]

include hcocR in

theorem R_cocycle {i j k : 𝒰.ι} {W' : X₀.Opens}
    (hij : W' ≤ 𝒰.U i ⊓ 𝒰.U j) (hjk : W' ≤ 𝒰.U j ⊓ 𝒰.U k) (hki : W' ≤ 𝒰.U k ⊓ 𝒰.U i) :
    R 𝒰 Y V hVm φ hφV i j hij ≫ R 𝒰 Y V hVm φ hφV j k hjk ≫ R 𝒰 Y V hVm φ hφV k i hki = 𝟙 _ := by
  have hji : W' ≤ 𝒰.U j ⊓ 𝒰.U i := hij.trans (swap_le 𝒰 i j)
  have hkj : W' ≤ 𝒰.U k ⊓ 𝒰.U j := hjk.trans (swap_le 𝒰 j k)
  have hik : W' ≤ 𝒰.U i ⊓ 𝒰.U k := hki.trans (swap_le 𝒰 k i)
  have RS := fun (a b : 𝒰.ι) (h : W' ≤ 𝒰.U a ⊓ 𝒰.U b) (h' : W' ≤ 𝒰.U b ⊓ 𝒰.U a) =>
    R_R_symm 𝒰 Y V hVm φ hφV a b h h'
  rcases lt_trichotomy i j with hij' | rfl | hji'
  · rcases lt_trichotomy j k with hjk' | rfl | hkj'
    ·
      rw [← Category.assoc, ← R_sorted 𝒰 Y V hVm φ hφV hcocR hij' hjk' hij hjk hik, RS]
    ·
      rw [R_self, Category.id_comp, RS]
    · rcases lt_trichotomy i k with hik' | rfl | hki'
      ·
        rw [R_sorted 𝒰 Y V hVm φ hφV hcocR hik' hkj' hik hkj hij, Category.assoc, reassoc_of% (RS k j hkj hjk), RS]
      ·
        rw [R_self, Category.comp_id, RS]
      ·
        have h1 := R_sorted 𝒰 Y V hVm φ hφV hcocR hki' hij' hki hij hkj
        have h2 : R 𝒰 Y V hVm φ hφV k i hki ≫ R 𝒰 Y V hVm φ hφV i j hij ≫ R 𝒰 Y V hVm φ hφV j k hjk = 𝟙 _ := by
          rw [← Category.assoc, ← h1, RS]
        calc R 𝒰 Y V hVm φ hφV i j hij ≫ R 𝒰 Y V hVm φ hφV j k hjk ≫ R 𝒰 Y V hVm φ hφV k i hki
            = (R 𝒰 Y V hVm φ hφV i k hik ≫ R 𝒰 Y V hVm φ hφV k i hki) ≫
                R 𝒰 Y V hVm φ hφV i j hij ≫ R 𝒰 Y V hVm φ hφV j k hjk ≫ R 𝒰 Y V hVm φ hφV k i hki := by
              rw [RS, Category.id_comp]
          _ = R 𝒰 Y V hVm φ hφV i k hik ≫ (R 𝒰 Y V hVm φ hφV k i hki ≫ R 𝒰 Y V hVm φ hφV i j hij ≫
                R 𝒰 Y V hVm φ hφV j k hjk) ≫ R 𝒰 Y V hVm φ hφV k i hki := by
              simp only [Category.assoc]
          _ = 𝟙 _ := by rw [h2, Category.id_comp, RS]
  ·
    rw [R_self, Category.id_comp, RS]
  · rcases lt_trichotomy j k with hjk' | rfl | hkj'
    · rcases lt_trichotomy i k with hik' | rfl | hki'
      ·
        rw [R_sorted 𝒰 Y V hVm φ hφV hcocR hji' hik' hji hik hjk, Category.assoc, reassoc_of% (RS i j hij hji), RS]
      ·
        rw [R_self, Category.comp_id, RS]
      ·
        rw [← R_sorted 𝒰 Y V hVm φ hφV hcocR hjk' hki' hjk hki hji, RS]
    ·
      rw [R_self, Category.id_comp, RS]
    ·
      rw [R_sorted 𝒰 Y V hVm φ hφV hcocR hkj' hji' hkj hji hki, reassoc_of% (RS j k hjk hkj), RS]

end R

section Glue

variable {X₀ : Scheme.{u}} (𝒰 : X₀.OrderedAffineCover) (Y : 𝒰.ι → Scheme.{u})
  (V : ∀ i, X₀.Opens → (Y i).Opens) (hVm : ∀ i, Monotone (V i))
  (hVtop : ∀ i, V i (𝒰.U i) = ⊤)
  (hVinf : ∀ (i : 𝒰.ι) (W W' : X₀.Opens), V i W ⊓ V i W' ≤ V i (W ⊓ W'))
  (φ : ∀ (i j : 𝒰.ι), i < j → ((↑(V i (𝒰.U i ⊓ 𝒰.U j)) : Scheme.{u}) ≅ ↑(V j (𝒰.U i ⊓ 𝒰.U j))))
  (hφV : ∀ (i j : 𝒰.ι) (h : i < j) (W' : X₀.Opens),
    (φ i j h).hom ⁻¹ᵁ ((V j (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V j W') = (V i (𝒰.U i ⊓ 𝒰.U j)).ι ⁻¹ᵁ V i W')

def W3 (i j k : 𝒰.ι) : X₀.Opens := 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k

theorem W3_le_ij (i j k : 𝒰.ι) : W3 𝒰 i j k ≤ 𝒰.U i ⊓ 𝒰.U j := inf_le_left
theorem W3_le_jk (i j k : 𝒰.ι) : W3 𝒰 i j k ≤ 𝒰.U j ⊓ 𝒰.U k := inf_le_inf_right (𝒰.U k) inf_le_right
theorem W3_le_ki (i j k : 𝒰.ι) : W3 𝒰 i j k ≤ 𝒰.U k ⊓ 𝒰.U i :=
  le_inf inf_le_right (inf_le_left.trans inf_le_left)
theorem W3_rot (i j k : 𝒰.ι) : W3 𝒰 i j k ≤ W3 𝒰 j k i :=
  le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (inf_le_left.trans inf_le_left)

theorem pb_val (i j k : 𝒰.ι)
    (x : ↑(pullback (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι)) :
    ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).1 =
      ((pullback.snd (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).1 := by
  have h := pullback.condition (f := (V i (𝒰.U i ⊓ 𝒰.U j)).ι) (g := (V i (𝒰.U i ⊓ 𝒰.U k)).ι)
  have h' : ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ≫ (V i (𝒰.U i ⊓ 𝒰.U j)).ι).base x) =
      ((pullback.snd (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ≫ (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x) := by
    rw [h]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h'

include hVm hVinf in
theorem fst_mem (i j k : 𝒰.ι)
    (x : ↑(pullback (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι)) :
    ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).1 ∈ V i (W3 𝒰 i j k) := by
  have h1 : ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).1 ∈ V i (𝒰.U i ⊓ 𝒰.U j) :=
    ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).2
  have h2 : ((pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).1 ∈ V i (𝒰.U i ⊓ 𝒰.U k) := by
    rw [pb_val]; exact ((pullback.snd (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι).base x).2
  have h3 := hVinf i _ _ ⟨h1, h2⟩
  exact hVm i (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
    (𝒰.U i ⊓ 𝒰.U j) ⊓ (𝒰.U i ⊓ 𝒰.U k) ≤ W3 𝒰 i j k) h3

noncomputable def t'aux (i j k : 𝒰.ι) :
    pullback (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ⟶ ↑(V j (𝒰.U j ⊓ 𝒰.U k)) :=
  IsOpenImmersion.lift (V j (𝒰.U j ⊓ 𝒰.U k)).ι
    (pullback.fst _ _ ≫ t 𝒰 Y V hVm φ i j ≫ (V j (𝒰.U j ⊓ 𝒰.U i)).ι) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hVm j (W3_le_jk 𝒰 i j k)
        ((t_mem 𝒰 Y V hVm φ hφV i j (W3 𝒰 i j k) _).1 (fst_mem 𝒰 Y V hVm hVinf i j k x)))

@[reassoc]
theorem t'aux_ι (i j k : 𝒰.ι) :
    t'aux 𝒰 Y V hVm hVinf φ hφV i j k ≫ (V j (𝒰.U j ⊓ 𝒰.U k)).ι =
      pullback.fst _ _ ≫ t 𝒰 Y V hVm φ i j ≫ (V j (𝒰.U j ⊓ 𝒰.U i)).ι :=
  IsOpenImmersion.lift_fac _ _ _

noncomputable def t'O (i j k : 𝒰.ι) :
    pullback (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ⟶
      pullback (V j (𝒰.U j ⊓ 𝒰.U k)).ι (V j (𝒰.U j ⊓ 𝒰.U i)).ι :=
  pullback.lift (t'aux 𝒰 Y V hVm hVinf φ hφV i j k) (pullback.fst _ _ ≫ t 𝒰 Y V hVm φ i j)
    (by rw [t'aux_ι, Category.assoc])

@[reassoc]
theorem t'O_fst (i j k : 𝒰.ι) :
    t'O 𝒰 Y V hVm hVinf φ hφV i j k ≫ pullback.fst _ _ = t'aux 𝒰 Y V hVm hVinf φ hφV i j k :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem t'O_snd (i j k : 𝒰.ι) :
    t'O 𝒰 Y V hVm hVinf φ hφV i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t 𝒰 Y V hVm φ i j :=
  pullback.lift_snd _ _ _

noncomputable def q (i j k : 𝒰.ι) :
    pullback (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ⟶ ↑(V i (W3 𝒰 i j k)) :=
  IsOpenImmersion.lift ((Y i).homOfLE (hVm i (W3_le_ij 𝒰 i j k))) (pullback.fst _ _) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, fst_mem 𝒰 Y V hVm hVinf i j k x⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩)

@[reassoc]
theorem q_fac (i j k : 𝒰.ι) :
    q 𝒰 Y V hVm hVinf i j k ≫ (Y i).homOfLE (hVm i (W3_le_ij 𝒰 i j k)) = pullback.fst _ _ :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem q_ι (i j k : 𝒰.ι) :
    q 𝒰 Y V hVm hVinf i j k ≫ (V i (W3 𝒰 i j k)).ι =
      pullback.fst (V i (𝒰.U i ⊓ 𝒰.U j)).ι (V i (𝒰.U i ⊓ 𝒰.U k)).ι ≫ (V i (𝒰.U i ⊓ 𝒰.U j)).ι := by
  rw [← Scheme.homOfLE_ι (Y i) (hVm i (W3_le_ij 𝒰 i j k)), q_fac_assoc]

scoped instance mono_q (i j k : 𝒰.ι) : Mono (q 𝒰 Y V hVm hVinf i j k) := by
  have : Mono (q 𝒰 Y V hVm hVinf i j k ≫ (Y i).homOfLE (hVm i (W3_le_ij 𝒰 i j k))) := by
    rw [q_fac]; infer_instance
  exact mono_of_mono _ ((Y i).homOfLE (hVm i (W3_le_ij 𝒰 i j k)))

@[reassoc]
theorem t'O_q (i j k : 𝒰.ι) :
    t'O 𝒰 Y V hVm hVinf φ hφV i j k ≫ q 𝒰 Y V hVm hVinf j k i =
      q 𝒰 Y V hVm hVinf i j k ≫ R 𝒰 Y V hVm φ hφV i j (W3_le_ij 𝒰 i j k) ≫
        (Y j).homOfLE (hVm j (W3_rot 𝒰 i j k)) := by
  rw [← cancel_mono (V j (W3 𝒰 j k i)).ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, q_ι, t'O_fst_assoc, t'aux_ι, R_ι, q_fac_assoc]

variable (hcocR : ∀ (a b c : 𝒰.ι), a < b → b < c →
      ∃ (W : X₀.Opens) (_ : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ W) (h1 : W ≤ 𝒰.U a ⊓ 𝒰.U b)
        (h2 : W ≤ 𝒰.U b ⊓ 𝒰.U c) (h3 : W ≤ 𝒰.U a ⊓ 𝒰.U c),
        R 𝒰 Y V hVm φ hφV a c h3 = R 𝒰 Y V hVm φ hφV a b h1 ≫ R 𝒰 Y V hVm φ hφV b c h2)

include hcocR in
theorem cocycle_aux (i j k : 𝒰.ι) :
    t'O 𝒰 Y V hVm hVinf φ hφV i j k ≫ t'O 𝒰 Y V hVm hVinf φ hφV j k i ≫
      t'O 𝒰 Y V hVm hVinf φ hφV k i j = 𝟙 _ := by
  rw [← cancel_mono (q 𝒰 Y V hVm hVinf i j k), Category.id_comp, ← cancel_mono (V i (W3 𝒰 i j k)).ι]
  simp only [Category.assoc]
  rw [t'O_q_assoc 𝒰 Y V hVm hVinf φ hφV k i j, Scheme.homOfLE_ι, t'O_q_assoc 𝒰 Y V hVm hVinf φ hφV j k i,
    homOfLE_R_assoc 𝒰 Y V hVm φ hφV k i (W3_le_ij 𝒰 k i j) (W3_rot 𝒰 j k i), Scheme.homOfLE_ι,
    t'O_q_assoc 𝒰 Y V hVm hVinf φ hφV i j k,
    homOfLE_R_assoc 𝒰 Y V hVm φ hφV j k (W3_le_ij 𝒰 j k i) (W3_rot 𝒰 i j k),
    homOfLE_R_assoc 𝒰 Y V hVm φ hφV k i _ (W3_rot 𝒰 i j k), Scheme.homOfLE_ι,
    reassoc_of% (R_cocycle 𝒰 Y V hVm φ hφV hcocR (W3_le_ij 𝒰 i j k)
      ((W3_rot 𝒰 i j k).trans (W3_le_ij 𝒰 j k i))
      ((W3_rot 𝒰 i j k).trans ((W3_rot 𝒰 j k i).trans (W3_le_ij 𝒰 k i j))))]

noncomputable def glueData : Scheme.GlueData.{u} where
  J := 𝒰.ι
  U := Y
  V ij := ↑(V ij.1 (𝒰.U ij.1 ⊓ 𝒰.U ij.2))
  f i j := (V i (𝒰.U i ⊓ 𝒰.U j)).ι
  f_id i := by
    have e : V i (𝒰.U i ⊓ 𝒰.U i) = ⊤ := by rw [inf_idem]; exact hVtop i
    show IsIso (V i (𝒰.U i ⊓ 𝒰.U i)).ι
    rw [e]
    exact (Scheme.topIso (Y i)).isIso_hom
  f_open i j := inferInstance
  t i j := t 𝒰 Y V hVm φ i j
  t_id i := t_self 𝒰 Y V hVm φ i
  t' i j k := t'O 𝒰 Y V hVm hVinf φ hφV i j k
  t_fac i j k := t'O_snd 𝒰 Y V hVm hVinf φ hφV i j k
  cocycle i j k := cocycle_aux 𝒰 Y V hVm hVinf φ hφV hcocR i j k

end Glue

end OB4bAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos.OB4bAux"

open OB4bAux in
theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (𝒰 : A₀.OrderedAffineCover)

    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)
    (hcoc : ∀ r : 𝒰.Idx 2, (ρac r).hom = (ρab r).hom ≫ (ρbc r).hom) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of T')) (_ : Smooth fX) (gX : A₀ ⟶ X)
      (_ : IsPullback gX f₀ fX (Spec.map (CommRingCat.ofHom π)))
      (ιY : ∀ a, Y a ⟶ X),
      (∀ a, IsOpenImmersion (ιY a)) ∧
      (∀ a, ιY a ≫ fX = q a) ∧
      (∀ x : X, ∃ (a : 𝒰.ι) (y : Y a), (ιY a).base y = x) ∧
      (∀ a, g a ≫ ιY a = (𝒰.U a).ι ≫ gX) ∧
      (∀ (a b : 𝒰.ι) (h : a < b),
        (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ ιY a = (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ ιY b) := by
  classical

  have hcocR : ∀ (a b c : 𝒰.ι) (hab : a < b) (hbc : b < c),
      ∃ (W : A₀.Opens) (_ : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ W) (h1 : W ≤ 𝒰.U a ⊓ 𝒰.U b)
        (h2 : W ≤ 𝒰.U b ⊓ 𝒰.U c) (h3 : W ≤ 𝒰.U a ⊓ 𝒰.U c),
        R 𝒰 Y O hOm φ hφO a c h3 = R 𝒰 Y O hOm φ hφO a b h1 ≫ R 𝒰 Y O hOm φ hφO b c h2 := by
    intro a b c hab hbc
    have hsm : StrictMono ![a, b, c] := by simp [hab, hbc]
    let r : 𝒰.Idx 2 := ⟨![a, b, c], hsm⟩
    refine ⟨𝒰.inter r, ?_, le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1), le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2),
      le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2), ?_⟩
    · change _ ≤ ⨅ k, 𝒰.U (![a, b, c] k)
      refine le_iInf fun k => ?_
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => k.elim0) k) k) k
      · exact inf_le_left.trans inf_le_left
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right
    · rw [← R_eq_of_fac 𝒰 Y O hOm φ hφO hab (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1)) (ρab r).hom (hρab r),
        ← R_eq_of_fac 𝒰 Y O hOm φ hφO hbc (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2)) (ρbc r).hom (hρbc r),
        ← R_eq_of_fac 𝒰 Y O hOm φ hφO (lt_trans hab hbc) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))
          (ρac r).hom (hρac r)]
      exact hcoc r
  let D := OB4bAux.glueData 𝒰 Y O hOm hOtop hOinf φ hφO hcocR

  have t_over : ∀ i j : 𝒰.ι,
      t 𝒰 Y O hOm φ i j ≫ (O j (𝒰.U j ⊓ 𝒰.U i)).ι ≫ q j = (O i (𝒰.U i ⊓ 𝒰.U j)).ι ≫ q i := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [t_of_lt 𝒰 Y O hOm φ h, Category.assoc, Scheme.homOfLE_ι_assoc]; exact hφq i j h
    · rw [t_self]; simp
    · rw [t_of_gt 𝒰 Y O hOm φ h, Category.assoc]
      have e : (φ j i h).inv ≫ (O j (𝒰.U j ⊓ 𝒰.U i)).ι ≫ q j = (O i (𝒰.U j ⊓ 𝒰.U i)).ι ≫ q i := by
        rw [Iso.inv_comp_eq]; exact (hφq j i h).symm
      rw [e, Scheme.homOfLE_ι_assoc]
  have compat : ∀ a : (MultispanShape.prod D.J).L,
      D.diagram.fst a ≫ (fun i : D.J => q i) ((MultispanShape.prod D.J).fst a) =
        D.diagram.snd a ≫ (fun i : D.J => q i) ((MultispanShape.prod D.J).snd a) := by
    rintro ⟨i, j⟩
    show (O i (𝒰.U i ⊓ 𝒰.U j)).ι ≫ q i = (t 𝒰 Y O hOm φ i j ≫ (O j (𝒰.U j ⊓ 𝒰.U i)).ι) ≫ q j
    rw [Category.assoc, t_over]
  let fX : D.glued ⟶ Spec (CommRingCat.of T') := Multicoequalizer.desc D.diagram _ (fun i => q i) compat
  have hιfX : ∀ i, D.ι i ≫ fX = q i := fun i => Multicoequalizer.π_desc _ _ _ _ _
  haveI : ∀ i, IsOpenImmersion (D.ι i) := fun i => Scheme.GlueData.ι_isOpenImmersion D i

  have GC : ∀ (i j : 𝒰.ι) (h : i < j),
      (O i (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι i = (φ i j h).hom ≫ (O j (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι j := by
    intro i j h
    have gc := D.glue_condition i j
    change t 𝒰 Y O hOm φ i j ≫ (O j (𝒰.U j ⊓ 𝒰.U i)).ι ≫ D.ι j = (O i (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι i at gc
    rw [← gc, t_of_lt 𝒰 Y O hOm φ h, Category.assoc, Scheme.homOfLE_ι_assoc]

  have hsmooth : Smooth fX := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) D.openCover]
    intro i
    change Smooth (D.ι i ≫ fX)
    rw [hιfX]; exact hq i

  let 𝒱 : A₀.OpenCover := Scheme.Cover.mkOfCovers 𝒰.ι (fun j => ↑(𝒰.U j)) (fun j => (𝒰.U j).ι)
    (fun x => by
      have hx : x ∈ (⊤ : A₀.Opens) := trivial
      rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨j, hj⟩ := hx
      exact ⟨j, ⟨x, hj⟩, rfl⟩)
  let ψ : ∀ j : 𝒰.ι, (↑(𝒰.U j) : Scheme.{u}) ⟶ D.glued := fun j => g j ≫ D.ι j
  have key : ∀ (i j : 𝒰.ι) (h : i < j) {P : Scheme.{u}} (a : P ⟶ ↑(𝒰.U i)) (b : P ⟶ ↑(𝒰.U j)),
      a ≫ (𝒰.U i).ι = b ≫ (𝒰.U j).ι → a ≫ ψ i = b ≫ ψ j := by
    intro i j h P a b hab
    have hrange : Set.range (a ≫ (𝒰.U i).ι).base ⊆ Set.range (𝒰.U i ⊓ 𝒰.U j).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Scheme.Hom.comp_apply]; exact (a.base p).2
      · rw [hab, Scheme.Hom.comp_apply]; exact (b.base p).2
    obtain ⟨c, hc⟩ : ∃ c : P ⟶ ↑(𝒰.U i ⊓ 𝒰.U j), c ≫ (𝒰.U i ⊓ 𝒰.U j).ι = a ≫ (𝒰.U i).ι :=
      ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
    have ha : c ≫ A₀.homOfLE inf_le_left = a := by
      rw [← cancel_mono (𝒰.U i).ι, Category.assoc, Scheme.homOfLE_ι, hc]
    have hb : c ≫ A₀.homOfLE inf_le_right = b := by
      rw [← cancel_mono (𝒰.U j).ι, Category.assoc, Scheme.homOfLE_ι, hc, hab]
    obtain ⟨γ, γ', hγ, hγ', hγγ'⟩ := hφg i j h
    calc a ≫ ψ i = c ≫ (A₀.homOfLE inf_le_left ≫ g i) ≫ D.ι i := by rw [← ha]; simp only [ψ, Category.assoc]
      _ = c ≫ γ ≫ (O i (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι i := by rw [← hγ, Category.assoc]
      _ = c ≫ γ ≫ (φ i j h).hom ≫ (O j (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι j := by rw [GC i j h]
      _ = c ≫ γ' ≫ (O j (𝒰.U i ⊓ 𝒰.U j)).ι ≫ D.ι j := by rw [← hγγ', Category.assoc]
      _ = c ≫ (A₀.homOfLE inf_le_right ≫ g j) ≫ D.ι j := by rw [← hγ', Category.assoc]
      _ = b ≫ ψ j := by rw [← hb]; simp only [ψ, Category.assoc]
  have hcompat : ∀ i j : 𝒰.ι,
      pullback.fst (𝒱.f i) (𝒱.f j) ≫ ψ i = pullback.snd (𝒱.f i) (𝒱.f j) ≫ ψ j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key i j hij _ _ pullback.condition
    · rw [fst_eq_snd_of_mono_eq]
    · exact (key j i hji _ _ pullback.condition.symm).symm
  let gX : A₀ ⟶ D.glued := 𝒱.glueMorphisms ψ hcompat
  have hgX : ∀ i, (𝒰.U i).ι ≫ gX = g i ≫ D.ι i := fun i => 𝒱.ι_glueMorphisms ψ hcompat i
  have hpt : ∀ (j : 𝒰.ι) (x : ↑(𝒰.U j)), gX.base ((𝒰.U j).ι.base x) = (D.ι j).base ((g j).base x) := by
    intro j x
    rw [← Scheme.Hom.comp_apply, hgX j, Scheme.Hom.comp_apply]
    rfl

  have hcart : IsPullback gX f₀ fX (Spec.map (CommRingCat.ofHom π)) := by
    apply Scheme.isPullback_of_openCover gX f₀ fX _ D.openCover
    intro k
    have hrangeEq : Set.range (𝒰.U k).ι.base = Set.range (pullback.fst gX (D.openCover.f k)).base := by
      change Set.range (𝒰.U k).ι.base = Set.range (pullback.fst gX (D.ι k)).base
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      ext x
      constructor
      · intro hx
        exact ⟨(g k).base ⟨x, hx⟩, (hpt k ⟨x, hx⟩).symm⟩
      · rintro ⟨y, hy⟩
        obtain ⟨j, hj⟩ : ∃ j, x ∈ 𝒰.U j := by
          have hx : x ∈ (⊤ : A₀.Opens) := trivial
          rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx
          exact hx
        have h1 : (D.ι k).base y = (D.ι j).base ((g j).base ⟨x, hj⟩) := hy.trans (hpt j ⟨x, hj⟩)
        obtain ⟨z, hz, hz'⟩ := (Scheme.GlueData.ι_eq_iff D k j y ((g j).base ⟨x, hj⟩)).mp h1
        dsimp only at z hz hz'
        have hm : (g j).base ⟨x, hj⟩ ∈ O j (𝒰.U j ⊓ 𝒰.U k) := by
          rw [← hz']
          change ((t 𝒰 Y O hOm φ k j ≫ (O j (𝒰.U j ⊓ 𝒰.U k)).ι).base z) ∈ O j (𝒰.U j ⊓ 𝒰.U k)
          rw [Scheme.Hom.comp_apply]
          exact ((t 𝒰 Y O hOm φ k j).base z).2
        have hm' : (⟨x, hj⟩ : ↥(𝒰.U j)) ∈ g j ⁻¹ᵁ O j (𝒰.U j ⊓ 𝒰.U k) := hm
        rw [hO j] at hm'
        exact (TopologicalSpace.Opens.mem_inf.mp hm').2
    let e₁ : (↑(𝒰.U k) : Scheme.{u}) ≅ pullback gX (D.openCover.f k) :=
      IsOpenImmersion.isoOfRangeEq (𝒰.U k).ι (pullback.fst gX (D.openCover.f k)) hrangeEq
    have he₁ : e₁.hom ≫ pullback.fst gX (D.openCover.f k) = (𝒰.U k).ι :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    refine (hg k).of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · change g k ≫ 𝟙 _ = e₁.hom ≫ pullback.snd gX (D.openCover.f k)
      have hc : pullback.fst gX (D.openCover.f k) ≫ gX = pullback.snd gX (D.openCover.f k) ≫ D.openCover.f k :=
        pullback.condition
      rw [Category.comp_id]
      refine (cancel_mono (D.openCover.f k)).1 ?_
      rw [Category.assoc, ← hc, ← Category.assoc, he₁]
      change g k ≫ D.ι k = (𝒰.U k).ι ≫ gX
      rw [hgX]
    · change ((𝒰.U k).ι ≫ f₀) ≫ 𝟙 _ = e₁.hom ≫ pullback.fst gX (D.openCover.f k) ≫ f₀
      rw [Category.comp_id, ← Category.assoc, he₁]
    · change q k ≫ 𝟙 _ = 𝟙 _ ≫ D.ι k ≫ fX
      rw [Category.comp_id, Category.id_comp, hιfX]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact ⟨D.glued, fX, hsmooth, gX, hcart, D.ι, fun i => Scheme.GlueData.ι_isOpenImmersion D i, hιfX,
    D.ι_jointly_surjective, fun i => (hgX i).symm, GC⟩

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos (solution)
