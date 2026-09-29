-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_glued_of_overlap_isos_of_forall_base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/15236934-507d-5d97-937c-88cd6644b8d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace RG3aAux

section Restr

variable {X : Scheme.{0}}

noncomputable def restr {A C : X.Opens} (h : C ≤ A) (φ : (↑A : Scheme.{0}) ⟶ ↑A)
    (hφ : ∀ x : ↑A, φ.base x = x) : (↑C : Scheme.{0}) ⟶ ↑C :=
  IsOpenImmersion.lift (X.homOfLE h) (X.homOfLE h ≫ φ) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by rw [Scheme.Hom.comp_apply, hφ]⟩)

variable {A C : X.Opens} (h : C ≤ A) (φ : (↑A : Scheme.{0}) ⟶ ↑A) (hφ : ∀ x : ↑A, φ.base x = x)

@[reassoc]
theorem restr_fac : restr h φ hφ ≫ X.homOfLE h = X.homOfLE h ≫ φ :=
  IsOpenImmersion.lift_fac _ _ _

theorem restr_apply (x : ↑C) : (restr h φ hφ).base x = x := by
  apply (X.homOfLE h).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, restr_fac, Scheme.Hom.comp_apply, hφ]

theorem restr_unique {ψ : (↑C : Scheme.{0}) ⟶ ↑C} (hψ : ψ ≫ X.homOfLE h = X.homOfLE h ≫ φ) :
    ψ = restr h φ hφ := by
  rw [← cancel_mono (X.homOfLE h), hψ, restr_fac]

theorem restr_eq_id (h1 : φ = 𝟙 _) : restr h φ hφ = 𝟙 _ := by
  rw [← cancel_mono (X.homOfLE h), restr_fac, h1]; simp

theorem restr_comp (ψ : (↑A : Scheme.{0}) ⟶ ↑A) (hψ : ∀ x : ↑A, ψ.base x = x) :
    restr h φ hφ ≫ restr h ψ hψ =
      restr h (φ ≫ ψ) (fun x => by rw [Scheme.Hom.comp_apply, hφ, hψ]) := by
  rw [← cancel_mono (X.homOfLE h)]
  simp only [Category.assoc, restr_fac, restr_fac_assoc]

theorem homOfLE_restr {C' : X.Opens} (h' : C' ≤ C) :
    X.homOfLE h' ≫ restr h φ hφ = restr (h'.trans h) φ hφ ≫ X.homOfLE h' := by
  rw [← cancel_mono (X.homOfLE h)]
  simp only [Category.assoc, restr_fac, Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE_assoc]

end Restr

section T

variable {X₀ : Scheme.{0}} (𝒰 : X₀.OrderedAffineCover)

def O (i j : 𝒰.ι) : X₀.Opens := ⨅ k : Fin 2, 𝒰.U (![i, j] k)

theorem smono {i j : 𝒰.ι} (h : i < j) : StrictMono ![i, j] := by simp [h]

def pr {i j : 𝒰.ι} (h : i < j) : 𝒰.Idx 1 := ⟨![i, j], smono 𝒰 h⟩

theorem inter_pr {i j : 𝒰.ι} (h : i < j) : 𝒰.inter (pr 𝒰 h) = O 𝒰 i j := rfl

theorem O_le_left (i j : 𝒰.ι) : O 𝒰 i j ≤ 𝒰.U i := iInf_le _ 0
theorem O_le_right (i j : 𝒰.ι) : O 𝒰 i j ≤ 𝒰.U j := iInf_le _ 1
theorem le_O {W : X₀.Opens} {i j : 𝒰.ι} (hi : W ≤ 𝒰.U i) (hj : W ≤ 𝒰.U j) : W ≤ O 𝒰 i j :=
  le_iInf (Fin.forall_fin_two.2 ⟨hi, hj⟩)
theorem O_comm_le (i j : 𝒰.ι) : O 𝒰 i j ≤ O 𝒰 j i := le_O 𝒰 (O_le_right 𝒰 i j) (O_le_left 𝒰 i j)

noncomputable def κ (i j : 𝒰.ι) : (↑(O 𝒰 i j) : Scheme.{0}) ≅ ↑(O 𝒰 j i) :=
  ⟨X₀.homOfLE (O_comm_le 𝒰 i j), X₀.homOfLE (O_comm_le 𝒰 j i), by simp, by simp⟩

theorem κ_hom (i j : 𝒰.ι) : (κ 𝒰 i j).hom = X₀.homOfLE (O_comm_le 𝒰 i j) := rfl
theorem κ_inv (i j : 𝒰.ι) : (κ 𝒰 i j).inv = X₀.homOfLE (O_comm_le 𝒰 j i) := rfl

variable (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))

noncomputable def τO {i j : 𝒰.ι} (h : i < j) : (↑(O 𝒰 i j) : Scheme.{0}) ≅ ↑(O 𝒰 i j) := τ (pr 𝒰 h)

theorem τO_def {i j : 𝒰.ι} (h : i < j) : τO 𝒰 τ h = τ (pr 𝒰 h) := rfl

noncomputable def T (i j : 𝒰.ι) : (↑(O 𝒰 i j) : Scheme.{0}) ≅ ↑(O 𝒰 i j) :=
  if h : i < j then τO 𝒰 τ h
  else if h' : j < i then κ 𝒰 i j ≪≫ (τO 𝒰 τ h').symm ≪≫ κ 𝒰 j i
  else Iso.refl _

theorem T_of_lt {i j : 𝒰.ι} (h : i < j) : T 𝒰 τ i j = τO 𝒰 τ h := dif_pos h

theorem T_of_gt {i j : 𝒰.ι} (h : j < i) :
    T 𝒰 τ i j = κ 𝒰 i j ≪≫ (τO 𝒰 τ h).symm ≪≫ κ 𝒰 j i := by
  rw [T, dif_neg (not_lt.2 h.le), dif_pos h]

theorem T_self (i : 𝒰.ι) : T 𝒰 τ i i = Iso.refl _ := by
  rw [T, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

@[reassoc]
theorem κ_hom_inv_id (i j : 𝒰.ι) : (κ 𝒰 i j).hom ≫ (κ 𝒰 j i).hom = 𝟙 _ := by simp [κ]

theorem T_symm_hom (i j : 𝒰.ι) :
    (T 𝒰 τ j i).hom = (κ 𝒰 j i).hom ≫ (T 𝒰 τ i j).inv ≫ (κ 𝒰 i j).hom := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [T_of_gt 𝒰 τ h, T_of_lt 𝒰 τ h]; rfl
  · rw [T_self]; simp [κ]
  · rw [T_of_lt 𝒰 τ h, T_of_gt 𝒰 τ h]
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
    rw [Iso.inv_hom_id, Category.comp_id]

variable (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)

include hτpt in
theorem τO_apply {i j : 𝒰.ι} (h : i < j) (x : ↑(O 𝒰 i j)) : (τO 𝒰 τ h).hom.base x = x :=
  hτpt (pr 𝒰 h) x

include hτpt in
theorem τOinv_apply {i j : 𝒰.ι} (h : i < j) (x : ↑(O 𝒰 i j)) : (τO 𝒰 τ h).inv.base x = x := by
  have h1 := τO_apply 𝒰 τ hτpt h ((τO 𝒰 τ h).inv.base x)
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h1
  simpa using h1.symm

include hτpt in
theorem T_apply (i j : 𝒰.ι) (x : ↑(O 𝒰 i j)) : (T 𝒰 τ i j).hom.base x = x := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [T_of_lt 𝒰 τ h]; exact τO_apply 𝒰 τ hτpt h x
  · rw [T_self]; simp
  · rw [T_of_gt 𝒰 τ h]
    show (κ 𝒰 j i).hom.base ((τO 𝒰 τ h).inv.base ((κ 𝒰 i j).hom.base x)) = x
    apply Subtype.ext
    rw [κ_hom, Scheme.homOfLE_apply, τOinv_apply 𝒰 τ hτpt, κ_hom, Scheme.homOfLE_apply]

include hτpt in
theorem Tinv_apply (i j : 𝒰.ι) (x : ↑(O 𝒰 i j)) : (T 𝒰 τ i j).inv.base x = x := by
  have h := T_apply 𝒰 τ hτpt i j ((T 𝒰 τ i j).inv.base x)
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h
  simpa using h.symm

end T

section R

variable {X₀ : Scheme.{0}} (𝒰 : X₀.OrderedAffineCover)
  (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
  (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)

noncomputable def R {C : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) : (↑C : Scheme.{0}) ⟶ ↑C :=
  restr h (T 𝒰 τ i j).hom (T_apply 𝒰 τ hτpt i j)

@[reassoc]
theorem R_fac {C : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) :
    R 𝒰 τ hτpt h ≫ X₀.homOfLE h = X₀.homOfLE h ≫ (T 𝒰 τ i j).hom :=
  restr_fac _ _ _

@[reassoc]
theorem R_ι {C : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) :
    R 𝒰 τ hτpt h ≫ C.ι = X₀.homOfLE h ≫ (T 𝒰 τ i j).hom ≫ (O 𝒰 i j).ι := by
  rw [← Scheme.homOfLE_ι X₀ h, R_fac_assoc]

theorem R_apply {C : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) (x : ↑C) : (R 𝒰 τ hτpt h).base x = x :=
  restr_apply _ _ _ x

@[reassoc]
theorem homOfLE_R {C C' : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) (h' : C' ≤ C) :
    X₀.homOfLE h' ≫ R 𝒰 τ hτpt h = R 𝒰 τ hτpt (h'.trans h) ≫ X₀.homOfLE h' :=
  homOfLE_restr _ _ _ h'

theorem R_self {C : X₀.Opens} {i : 𝒰.ι} (h : C ≤ O 𝒰 i i) : R 𝒰 τ hτpt h = 𝟙 _ :=
  restr_eq_id _ _ _ (by rw [T_self]; rfl)

theorem R_R_symm {C : X₀.Opens} {i j : 𝒰.ι} (h : C ≤ O 𝒰 i j) (h' : C ≤ O 𝒰 j i) :
    R 𝒰 τ hτpt h ≫ R 𝒰 τ hτpt h' = 𝟙 _ := by
  have e1 : X₀.homOfLE h = X₀.homOfLE h' ≫ (κ 𝒰 j i).hom := by rw [κ_hom, Scheme.homOfLE_homOfLE]
  have e2 : X₀.homOfLE h' = X₀.homOfLE h ≫ (κ 𝒰 i j).hom := by rw [κ_hom, Scheme.homOfLE_homOfLE]
  rw [← cancel_mono (X₀.homOfLE h), Category.id_comp]
  calc (R 𝒰 τ hτpt h ≫ R 𝒰 τ hτpt h') ≫ X₀.homOfLE h
      = R 𝒰 τ hτpt h ≫ (R 𝒰 τ hτpt h' ≫ X₀.homOfLE h') ≫ (κ 𝒰 j i).hom := by
        rw [e1]; simp only [Category.assoc]
    _ = (R 𝒰 τ hτpt h ≫ X₀.homOfLE h) ≫ (κ 𝒰 i j).hom ≫ (T 𝒰 τ j i).hom ≫ (κ 𝒰 j i).hom := by
        rw [R_fac, e2]; simp only [Category.assoc]
    _ = X₀.homOfLE h ≫ ((T 𝒰 τ i j).hom ≫ (κ 𝒰 i j).hom ≫ (T 𝒰 τ j i).hom ≫ (κ 𝒰 j i).hom) := by
        rw [R_fac]; simp only [Category.assoc]
    _ = X₀.homOfLE h := by
        rw [T_symm_hom 𝒰 τ i j]
        simp only [Category.assoc, κ_hom_inv_id_assoc, κ_hom_inv_id, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id]

variable (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ X₀.homOfLE (𝒰.inter_le_inter_face r j)
            = X₀.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0)

theorem sa00 : Fin.succAbove (0 : Fin 3) 0 = 1 := by decide
theorem sa01 : Fin.succAbove (0 : Fin 3) 1 = 2 := by decide
theorem sa10 : Fin.succAbove (1 : Fin 3) 0 = 0 := by decide
theorem sa11 : Fin.succAbove (1 : Fin 3) 1 = 2 := by decide
theorem sa20 : Fin.succAbove (2 : Fin 3) 0 = 0 := by decide
theorem sa21 : Fin.succAbove (2 : Fin 3) 1 = 1 := by decide

theorem smono3 {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) : StrictMono ![a, b, c] := by simp [hab, hbc]

def tr {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) : 𝒰.Idx 2 := ⟨![a, b, c], smono3 𝒰 hab hbc⟩

theorem face_tr_0 {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) : 𝒰.face (tr 𝒰 hab hbc) 0 = pr 𝒰 hbc := by
  apply Subtype.ext; funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => k.elim0) k) k
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, sa00]; rfl
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply]; rfl

theorem face_tr_1 {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) :
    𝒰.face (tr 𝒰 hab hbc) 1 = pr 𝒰 (hab.trans hbc) := by
  apply Subtype.ext; funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => k.elim0) k) k
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, sa10]; rfl
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply]; rfl

theorem face_tr_2 {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) : 𝒰.face (tr 𝒰 hab hbc) 2 = pr 𝒰 hab := by
  apply Subtype.ext; funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => k.elim0) k) k
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, sa20]; rfl
  · simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply]; rfl

theorem transport_face {s s' : 𝒰.Idx 1} (e : s = s') {W : X₀.Opens} (hW : W ≤ 𝒰.inter s)
    (hW' : W ≤ 𝒰.inter s') (ρ : (↑W : Scheme.{0}) ⟶ ↑W)
    (hρ : ρ ≫ X₀.homOfLE hW = X₀.homOfLE hW ≫ (τ s).hom) :
    ρ ≫ X₀.homOfLE hW' = X₀.homOfLE hW' ≫ (τ s').hom := by
  subst e; exact hρ

include hcoc in

theorem R_sorted {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) {C : X₀.Opens}
    (h1 : C ≤ O 𝒰 a b) (h2 : C ≤ O 𝒰 b c) (h3 : C ≤ O 𝒰 a c) :
    R 𝒰 τ hτpt h3 = R 𝒰 τ hτpt h1 ≫ R 𝒰 τ hτpt h2 := by
  have hac := hab.trans hbc

  have ha : C ≤ 𝒰.U a := h1.trans (O_le_left 𝒰 a b)
  have hb : C ≤ 𝒰.U b := h1.trans (O_le_right 𝒰 a b)
  have hc : C ≤ 𝒰.U c := h2.trans (O_le_right 𝒰 b c)
  have hC : C ≤ 𝒰.inter (tr 𝒰 hab hbc) := by
    change C ≤ ⨅ k, 𝒰.U (![a, b, c] k)
    refine le_iInf fun k => ?_
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => k.elim0) k) k) k
    · exact ha
    · exact hb
    · exact hc
  have g2 : 𝒰.inter (tr 𝒰 hab hbc) ≤ O 𝒰 a b :=
    le_O 𝒰 (𝒰.inter_le (tr 𝒰 hab hbc) 0) (𝒰.inter_le (tr 𝒰 hab hbc) 1)
  have g0 : 𝒰.inter (tr 𝒰 hab hbc) ≤ O 𝒰 b c :=
    le_O 𝒰 (𝒰.inter_le (tr 𝒰 hab hbc) 1) (𝒰.inter_le (tr 𝒰 hab hbc) 2)
  have g1 : 𝒰.inter (tr 𝒰 hab hbc) ≤ O 𝒰 a c :=
    le_O 𝒰 (𝒰.inter_le (tr 𝒰 hab hbc) 0) (𝒰.inter_le (tr 𝒰 hab hbc) 2)
  obtain ⟨ρ, hρ, hρc⟩ := hcoc (tr 𝒰 hab hbc)
  have e2 : ρ 2 = R 𝒰 τ hτpt g2 := by
    refine restr_unique _ _ _ ?_
    rw [T_of_lt 𝒰 τ hab]
    exact transport_face 𝒰 τ (face_tr_2 𝒰 hab hbc) _ g2 _ (hρ 2)
  have e0 : ρ 0 = R 𝒰 τ hτpt g0 := by
    refine restr_unique _ _ _ ?_
    rw [T_of_lt 𝒰 τ hbc]
    exact transport_face 𝒰 τ (face_tr_0 𝒰 hab hbc) _ g0 _ (hρ 0)
  have e1 : ρ 1 = R 𝒰 τ hτpt g1 := by
    refine restr_unique _ _ _ ?_
    rw [T_of_lt 𝒰 τ hac]
    exact transport_face 𝒰 τ (face_tr_1 𝒰 hab hbc) _ g1 _ (hρ 1)
  rw [e0, e1, e2] at hρc

  rw [← cancel_mono (X₀.homOfLE hC), Category.assoc, ← homOfLE_R 𝒰 τ hτpt g0 hC, ← Category.assoc,
    ← homOfLE_R 𝒰 τ hτpt g2 hC, ← homOfLE_R 𝒰 τ hτpt g1 hC, hρc, Category.assoc]

include hcoc in

theorem R_cocycle {i j k : 𝒰.ι} {C : X₀.Opens}
    (hij : C ≤ O 𝒰 i j) (hjk : C ≤ O 𝒰 j k) (hki : C ≤ O 𝒰 k i) :
    R 𝒰 τ hτpt hij ≫ R 𝒰 τ hτpt hjk ≫ R 𝒰 τ hτpt hki = 𝟙 _ := by
  have hji : C ≤ O 𝒰 j i := hij.trans (O_comm_le 𝒰 i j)
  have hkj : C ≤ O 𝒰 k j := hjk.trans (O_comm_le 𝒰 j k)
  have hik : C ≤ O 𝒰 i k := hki.trans (O_comm_le 𝒰 k i)
  have RS := fun {a b : 𝒰.ι} (h : C ≤ O 𝒰 a b) (h' : C ≤ O 𝒰 b a) => R_R_symm 𝒰 τ hτpt h h'
  rcases lt_trichotomy i j with hij' | rfl | hji'
  · rcases lt_trichotomy j k with hjk' | rfl | hkj'
    ·
      rw [← Category.assoc, ← R_sorted 𝒰 τ hτpt hcoc hij' hjk' hij hjk hik, RS]
    ·
      rw [R_self, Category.id_comp, RS]
    · rcases lt_trichotomy i k with hik' | rfl | hki'
      ·
        rw [R_sorted 𝒰 τ hτpt hcoc hik' hkj' hik hkj hij, Category.assoc, reassoc_of% (RS hkj hjk), RS]
      ·
        rw [R_self, Category.comp_id, RS]
      ·
        have h1 := R_sorted 𝒰 τ hτpt hcoc hki' hij' hki hij hkj

        have h2 : R 𝒰 τ hτpt hki ≫ R 𝒰 τ hτpt hij ≫ R 𝒰 τ hτpt hjk = 𝟙 _ := by
          rw [← Category.assoc, ← h1, RS]
        calc R 𝒰 τ hτpt hij ≫ R 𝒰 τ hτpt hjk ≫ R 𝒰 τ hτpt hki
            = (R 𝒰 τ hτpt hik ≫ R 𝒰 τ hτpt hki) ≫ R 𝒰 τ hτpt hij ≫ R 𝒰 τ hτpt hjk ≫ R 𝒰 τ hτpt hki := by
              rw [RS, Category.id_comp]
          _ = R 𝒰 τ hτpt hik ≫ (R 𝒰 τ hτpt hki ≫ R 𝒰 τ hτpt hij ≫ R 𝒰 τ hτpt hjk) ≫ R 𝒰 τ hτpt hki := by
              simp only [Category.assoc]
          _ = 𝟙 _ := by rw [h2, Category.id_comp, RS]
  ·
    rw [R_self, Category.id_comp, RS]
  · rcases lt_trichotomy j k with hjk' | rfl | hkj'
    · rcases lt_trichotomy i k with hik' | rfl | hki'
      ·
        rw [R_sorted 𝒰 τ hτpt hcoc hji' hik' hji hik hjk, Category.assoc, reassoc_of% (RS hij hji), RS]
      ·
        rw [R_self, Category.comp_id, RS]
      ·
        rw [← R_sorted 𝒰 τ hτpt hcoc hjk' hki' hjk hki hji, RS]
    ·
      rw [R_self, Category.id_comp, RS]
    ·
      rw [R_sorted 𝒰 τ hτpt hcoc hkj' hji' hkj hji hki, reassoc_of% (RS hjk hkj), RS]

end R

section Glue

variable {X₀ : Scheme.{0}} (𝒰 : X₀.OrderedAffineCover)
  (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
  (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)

noncomputable def tO (i j : 𝒰.ι) : (↑(O 𝒰 i j) : Scheme.{0}) ⟶ ↑(O 𝒰 j i) :=
  (T 𝒰 τ i j).hom ≫ (κ 𝒰 i j).hom

include hτpt in
theorem tO_val (i j : 𝒰.ι) (x : ↑(O 𝒰 i j)) : ((tO 𝒰 τ i j).base x).1 = x.1 := by
  show ((κ 𝒰 i j).hom.base ((T 𝒰 τ i j).hom.base x)).1 = x.1
  rw [T_apply 𝒰 τ hτpt, κ_hom, Scheme.homOfLE_apply]

@[reassoc]
theorem tO_ι (i j : 𝒰.ι) : tO 𝒰 τ i j ≫ (O 𝒰 j i).ι = (T 𝒰 τ i j).hom ≫ (O 𝒰 i j).ι := by
  rw [tO, Category.assoc, κ_hom, Scheme.homOfLE_ι]

def C3 (i j k : 𝒰.ι) : X₀.Opens := 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k

theorem C3_le_ij (i j k : 𝒰.ι) : C3 𝒰 i j k ≤ O 𝒰 i j :=
  le_O 𝒰 (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
theorem C3_le_jk (i j k : 𝒰.ι) : C3 𝒰 i j k ≤ O 𝒰 j k :=
  le_O 𝒰 (inf_le_left.trans inf_le_right) inf_le_right
theorem C3_le_ki (i j k : 𝒰.ι) : C3 𝒰 i j k ≤ O 𝒰 k i :=
  le_O 𝒰 inf_le_right (inf_le_left.trans inf_le_left)
theorem C3_rot (i j k : 𝒰.ι) : C3 𝒰 i j k ≤ C3 𝒰 j k i :=
  le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (inf_le_left.trans inf_le_left)

theorem pb_val (i j k : 𝒰.ι)
    (x : ↑(pullback (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)))) :
    ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1 =
      ((pullback.snd (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1 := by
  have h := pullback.condition (f := X₀.homOfLE (O_le_left 𝒰 i j)) (g := X₀.homOfLE (O_le_left 𝒰 i k))
  have h' : (((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))) ≫ X₀.homOfLE (O_le_left 𝒰 i j)).base x).1 =
      (((pullback.snd (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))) ≫ X₀.homOfLE (O_le_left 𝒰 i k)).base x).1 := by rw [h]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.homOfLE_apply, Scheme.homOfLE_apply] at h'

noncomputable def t'aux (i j k : 𝒰.ι) :
    pullback (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)) ⟶ ↑(O 𝒰 j k) :=
  IsOpenImmersion.lift (X₀.homOfLE (O_le_left 𝒰 j k))
    (pullback.fst _ _ ≫ tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)) (by
      rintro _ ⟨x, rfl⟩
      have hz : ((pullback.fst _ _ ≫ tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)).base x).1 =
          ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1 := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.homOfLE_apply, tO_val 𝒰 τ hτpt]
      have hj : ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1
          ∈ 𝒰.U j := O_le_right 𝒰 i j ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).2
      have hk : ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1
          ∈ 𝒰.U k := by
        rw [pb_val]; exact O_le_right 𝒰 i k ((pullback.snd (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).2
      have hmem : ((pullback.fst _ _ ≫ tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)).base x).1 ∈ O 𝒰 j k := by
        rw [hz]; exact le_O 𝒰 inf_le_left inf_le_right ⟨hj, hk⟩
      exact ⟨⟨_, hmem⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩)

@[reassoc]
theorem t'aux_fac (i j k : 𝒰.ι) :
    t'aux 𝒰 τ hτpt i j k ≫ X₀.homOfLE (O_le_left 𝒰 j k) =
      pullback.fst _ _ ≫ tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i) :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem t'aux_ι (i j k : 𝒰.ι) :
    t'aux 𝒰 τ hτpt i j k ≫ (O 𝒰 j k).ι =
      pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)) ≫
        (T 𝒰 τ i j).hom ≫ (O 𝒰 i j).ι := by
  rw [← Scheme.homOfLE_ι X₀ (O_le_left 𝒰 j k), t'aux_fac_assoc, Scheme.homOfLE_ι, tO_ι]

noncomputable def t'O (i j k : 𝒰.ι) :
    pullback (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)) ⟶
      pullback (X₀.homOfLE (O_le_left 𝒰 j k)) (X₀.homOfLE (O_le_left 𝒰 j i)) :=
  pullback.lift (t'aux 𝒰 τ hτpt i j k) (pullback.fst _ _ ≫ tO 𝒰 τ i j)
    (by rw [t'aux_fac, Category.assoc])

@[reassoc]
theorem t'O_fst (i j k : 𝒰.ι) : t'O 𝒰 τ hτpt i j k ≫ pullback.fst _ _ = t'aux 𝒰 τ hτpt i j k :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem t'O_snd (i j k : 𝒰.ι) : t'O 𝒰 τ hτpt i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ tO 𝒰 τ i j :=
  pullback.lift_snd _ _ _

noncomputable def q (i j k : 𝒰.ι) :
    pullback (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)) ⟶ ↑(C3 𝒰 i j k) :=
  IsOpenImmersion.lift (X₀.homOfLE (C3_le_ij 𝒰 i j k)) (pullback.fst _ _) (by
    rintro _ ⟨x, rfl⟩
    have h1 : ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1
        ∈ O 𝒰 i j := ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).2
    have h2 : ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1
        ∈ 𝒰.U k := by
      rw [pb_val]; exact O_le_right 𝒰 i k ((pullback.snd (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).2
    have hmem : ((pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k))).base x).1
        ∈ C3 𝒰 i j k :=
      show _ ∈ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k from ⟨⟨O_le_left 𝒰 i j h1, O_le_right 𝒰 i j h1⟩, h2⟩
    exact ⟨⟨_, hmem⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩)

@[reassoc]
theorem q_fac (i j k : 𝒰.ι) : q 𝒰 i j k ≫ X₀.homOfLE (C3_le_ij 𝒰 i j k) = pullback.fst _ _ :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem q_ι (i j k : 𝒰.ι) :
    q 𝒰 i j k ≫ (C3 𝒰 i j k).ι =
      pullback.fst (X₀.homOfLE (O_le_left 𝒰 i j)) (X₀.homOfLE (O_le_left 𝒰 i k)) ≫ (O 𝒰 i j).ι := by
  rw [← Scheme.homOfLE_ι X₀ (C3_le_ij 𝒰 i j k), q_fac_assoc]

scoped instance mono_q (i j k : 𝒰.ι) : Mono (q 𝒰 i j k) := by
  have : Mono (q 𝒰 i j k ≫ X₀.homOfLE (C3_le_ij 𝒰 i j k)) := by rw [q_fac]; infer_instance
  exact mono_of_mono _ (X₀.homOfLE (C3_le_ij 𝒰 i j k))

@[reassoc]
theorem t'O_q (i j k : 𝒰.ι) :
    t'O 𝒰 τ hτpt i j k ≫ q 𝒰 j k i =
      q 𝒰 i j k ≫ R 𝒰 τ hτpt (C3_le_ij 𝒰 i j k) ≫ X₀.homOfLE (C3_rot 𝒰 i j k) := by
  rw [← cancel_mono (C3 𝒰 j k i).ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, q_ι, t'O_fst_assoc, t'aux_ι, R_ι, q_fac_assoc]

variable (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ X₀.homOfLE (𝒰.inter_le_inter_face r j)
            = X₀.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0)

include hcoc in
theorem cocycle_aux (i j k : 𝒰.ι) :
    t'O 𝒰 τ hτpt i j k ≫ t'O 𝒰 τ hτpt j k i ≫ t'O 𝒰 τ hτpt k i j = 𝟙 _ := by
  rw [← cancel_mono (q 𝒰 i j k), Category.id_comp, ← cancel_mono (C3 𝒰 i j k).ι]
  simp only [Category.assoc]
  rw [t'O_q_assoc 𝒰 τ hτpt k i j, Scheme.homOfLE_ι, t'O_q_assoc 𝒰 τ hτpt j k i,
    homOfLE_R_assoc 𝒰 τ hτpt (C3_le_ij 𝒰 k i j) (C3_rot 𝒰 j k i), Scheme.homOfLE_ι,
    t'O_q_assoc 𝒰 τ hτpt i j k, homOfLE_R_assoc 𝒰 τ hτpt (C3_le_ij 𝒰 j k i) (C3_rot 𝒰 i j k),
    homOfLE_R_assoc 𝒰 τ hτpt _ (C3_rot 𝒰 i j k), Scheme.homOfLE_ι,
    reassoc_of% (R_cocycle 𝒰 τ hτpt hcoc (C3_le_ij 𝒰 i j k) ((C3_rot 𝒰 i j k).trans (C3_le_ij 𝒰 j k i))
      ((C3_rot 𝒰 i j k).trans ((C3_rot 𝒰 j k i).trans (C3_le_ij 𝒰 k i j))))]

noncomputable def glueData : Scheme.GlueData.{0} where
  J := 𝒰.ι
  U i := ↑(𝒰.U i)
  V ij := ↑(O 𝒰 ij.1 ij.2)
  f i j := X₀.homOfLE (O_le_left 𝒰 i j)
  f_id i := ⟨⟨X₀.homOfLE (le_O 𝒰 le_rfl le_rfl), by simp, by simp⟩⟩
  f_open i j := inferInstance
  t i j := tO 𝒰 τ i j
  t_id i := by simp [tO, T_self, κ]
  t' i j k := t'O 𝒰 τ hτpt i j k
  t_fac i j k := t'O_snd 𝒰 τ hτpt i j k
  cocycle i j k := cocycle_aux 𝒰 τ hτpt hcoc i j k

theorem glueData_J : (glueData 𝒰 τ hτpt hcoc).J = 𝒰.ι := rfl
theorem glueData_U (i : 𝒰.ι) : (glueData 𝒰 τ hτpt hcoc).U i = ↑(𝒰.U i) := rfl
theorem glueData_V (i j : 𝒰.ι) : (glueData 𝒰 τ hτpt hcoc).V (i, j) = ↑(O 𝒰 i j) := rfl
theorem glueData_f (i j : 𝒰.ι) : (glueData 𝒰 τ hτpt hcoc).f i j = X₀.homOfLE (O_le_left 𝒰 i j) := rfl
theorem glueData_t (i j : 𝒰.ι) : (glueData 𝒰 τ hτpt hcoc).t i j = tO 𝒰 τ i j := rfl

theorem T_over {S : Scheme.{0}} (p : X₀ ⟶ S)
    (hτS : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ p = (𝒰.inter s).ι ≫ p) (i j : 𝒰.ι) :
    (T 𝒰 τ i j).hom ≫ (O 𝒰 i j).ι ≫ p = (O 𝒰 i j).ι ≫ p := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [T_of_lt 𝒰 τ h]; exact hτS (pr 𝒰 h)
  · rw [T_self]; simp
  · rw [T_of_gt 𝒰 τ h]
    have h1 : (τO 𝒰 τ h).inv ≫ (O 𝒰 j i).ι ≫ p = (O 𝒰 j i).ι ≫ p := by
      rw [Iso.inv_comp_eq]; exact (hτS (pr 𝒰 h)).symm
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, κ_hom, Scheme.homOfLE_ι_assoc]
    rw [h1, Scheme.homOfLE_ι_assoc]

end Glue

end RG3aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq.RG3aAux"

open RG3aAux in
theorem solution
    {X₀ S : Scheme.{0}} (p : X₀ ⟶ S) (𝒰 : X₀.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτS : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ p = (𝒰.inter s).ι ≫ p)
    (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)
    (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ X₀.homOfLE (𝒰.inter_le_inter_face r j)
            = X₀.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) :
    ∃ (X : Scheme.{0}) (fX : X ⟶ S) (ιU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ X),
      (∀ i, IsOpenImmersion (ιU i)) ∧
      (∀ i, ιU i ≫ fX = (𝒰.U i).ι ≫ p) ∧
      (∀ x : X, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιU i).base y = x) ∧
      (∀ s : 𝒰.Idx 1,
        X₀.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) = (τ s).hom ≫ X₀.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1)) ∧
      (∀ (i j : 𝒰.ι) (y : ↑(𝒰.U i)) (y' : ↑(𝒰.U j)),
        (ιU i).base y = (ιU j).base y' ↔ (𝒰.U i).ι.base y = (𝒰.U j).ι.base y') := by
  classical
  let D := RG3aAux.glueData 𝒰 τ hτpt hcoc
  have compat : ∀ a : (MultispanShape.prod D.J).L,
      D.diagram.fst a ≫ (fun i : D.J => (𝒰.U i).ι ≫ p) ((MultispanShape.prod D.J).fst a) =
        D.diagram.snd a ≫ (fun i : D.J => (𝒰.U i).ι ≫ p) ((MultispanShape.prod D.J).snd a) := by
    rintro ⟨i, j⟩
    show X₀.homOfLE (O_le_left 𝒰 i j) ≫ (𝒰.U i).ι ≫ p =
      (tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)) ≫ (𝒰.U j).ι ≫ p
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc, tO_ι_assoc]
    exact (T_over 𝒰 τ p hτS i j).symm
  refine ⟨D.glued, Multicoequalizer.desc D.diagram _ (fun i => (𝒰.U i).ι ≫ p) compat, D.ι,
    fun i => Scheme.GlueData.ι_isOpenImmersion D i, fun i => Multicoequalizer.π_desc _ _ _ _ _,
    D.ι_jointly_surjective, ?_, ?_⟩
  ·
    suffices H : ∀ (s' : 𝒰.Idx 1) (i j : 𝒰.ι) (h : i < j), pr 𝒰 h = s' →
        X₀.homOfLE (𝒰.inter_le s' 0) ≫ D.ι (s'.1 0) =
          (τ s').hom ≫ X₀.homOfLE (𝒰.inter_le s' 1) ≫ D.ι (s'.1 1) by
      intro s
      exact H s (s.1 0) (s.1 1) (s.2 (by decide)) (Subtype.ext (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)))
    rintro _ i j h rfl
    have gc := D.glue_condition i j
    change tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i) ≫ D.ι j = X₀.homOfLE (O_le_left 𝒰 i j) ≫ D.ι i at gc
    change X₀.homOfLE (O_le_left 𝒰 i j) ≫ D.ι i = (τO 𝒰 τ h).hom ≫ X₀.homOfLE (O_le_right 𝒰 i j) ≫ D.ι j
    rw [← gc, tO, T_of_lt 𝒰 τ h, κ_hom, Category.assoc, Scheme.homOfLE_homOfLE_assoc]
  ·
    intro i j y y'
    refine (Scheme.GlueData.ι_eq_iff D i j y y').trans ?_
    constructor
    · rintro ⟨x, hx, hx'⟩
      dsimp only at x hx hx'
      change y.1 = y'.1
      rw [← hx, ← hx']
      change ((X₀.homOfLE (O_le_left 𝒰 i j)).base x).1 =
        ((tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)).base x).1
      rw [Scheme.homOfLE_apply, Scheme.Hom.comp_apply, Scheme.homOfLE_apply, tO_val 𝒰 τ hτpt]
    · intro e
      change y.1 = y'.1 at e
      have hj : y.1 ∈ 𝒰.U j := by rw [e]; exact y'.2
      have hmem : y.1 ∈ O 𝒰 i j := le_O 𝒰 inf_le_left inf_le_right ⟨y.2, hj⟩
      refine Exists.intro (⟨y.1, hmem⟩ : O 𝒰 i j) ⟨?_, ?_⟩
      · change (X₀.homOfLE (O_le_left 𝒰 i j)).base ⟨y.1, hmem⟩ = y
        exact Subtype.ext (by rw [Scheme.homOfLE_apply])
      · change (tO 𝒰 τ i j ≫ X₀.homOfLE (O_le_left 𝒰 j i)).base ⟨y.1, hmem⟩ = y'
        apply Subtype.ext
        rw [Scheme.Hom.comp_apply, Scheme.homOfLE_apply, tO_val 𝒰 τ hτpt]
        exact e

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq (solution)
