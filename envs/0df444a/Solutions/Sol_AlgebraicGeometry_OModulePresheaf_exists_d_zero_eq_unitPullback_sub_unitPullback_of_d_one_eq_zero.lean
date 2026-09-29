-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d4004ad9-f1c6-5ecc-bb45-d303d7c4f24d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero

set_option autoImplicit false

universe u

namespace LamIndepAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

section Sheaf

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) {m : ℕ} (z : (OModulePresheaf.unit πY).cochain 𝒦 m)

noncomputable def pb (T : 𝒦.Idx m) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) : Γ(X, W) :=
  (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter T)).hom (z T))

theorem map_pb (T : 𝒦.Idx m) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ 𝒦.inter T) :
    (X.presheaf.map (homOfLE hW').op).hom (pb h 𝒦 z T W hW) = pb h 𝒦 z T W' hW'' := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem pb_congr {T T' : 𝒦.Idx m} (e : T = T') (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W ≤ h ⁻¹ᵁ 𝒦.inter T') :
    pb h 𝒦 z T W hW = pb h 𝒦 z T' W hW' := by
  subst e; rfl

theorem map_app_map_eq_pb (S : 𝒦.Idx (m + 1)) (i : Fin (m + 2)) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter S) :
    (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter S)).hom
      ((Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face S i)).op).hom (z (𝒦.face S i)))) =
      pb h 𝒦 z (𝒦.face S i) W (hW.trans (h.preimage_mono (𝒦.inter_le_inter_face S i))) := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality_assoc, ← X.presheaf.map_comp,
    ← CommRingCat.comp_apply]
  rfl

end Sheaf

section Pairs

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)

def pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exact hij)⟩

theorem pair_val {i j : 𝒦.ι} (hij : i < j) : (pair 𝒦 hij).1 = ![i, j] := rfl

theorem inf_le_inter_pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.U i ⊓ 𝒦.U j ≤ 𝒦.inter (pair 𝒦 hij) :=
  le_iInf fun k => by fin_cases k; exacts [inf_le_left, inf_le_right]

def triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.Idx 2 :=
  ⟨![a, b, c], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exacts [hab, hbc])⟩

theorem inf_le_inter_triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c ≤ 𝒦.inter (triple 𝒦 hab hbc) :=
  le_iInf fun k => by
    fin_cases k
    exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]

theorem face_triple_zero {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 0 = pair 𝒦 hbc := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_one {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 1 = pair 𝒦 (hab.trans hbc) := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_two {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 2 = pair 𝒦 hab := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

noncomputable def P {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) :=
  pb h 𝒦 z (pair 𝒦 hij) W (hW.trans (h.preimage_mono (inf_le_inter_pair 𝒦 hij)))

theorem map_P {i j : 𝒦.ι} (hij : i < j) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W)
    (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (P h 𝒦 z hij W hW) = P h 𝒦 z hij W' hW'' :=
  map_pb h 𝒦 z _ _ hW' _

theorem P_add_P (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c)
    (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c)) :
    P h 𝒦 z hab W (hW.trans (h.preimage_mono inf_le_left)) + P h 𝒦 z hbc W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      P h 𝒦 z (hab.trans hbc) W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by
  have hle : W ≤ h ⁻¹ᵁ 𝒦.inter (triple 𝒦 hab hbc) := hW.trans (h.preimage_mono (inf_le_inter_triple 𝒦 hab hbc))
  have hd := congrFun hz (triple 𝒦 hab hbc)
  rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_three] at hd
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_zsmul, neg_one_zsmul] at hd
  change (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 0)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 0)) +
        -(Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 1)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 1)) +
        (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 2)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 2))
      = (0 : Γ(Y, 𝒦.inter (triple 𝒦 hab hbc))) at hd
  have hd' := congrArg (fun y => (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter (triple 𝒦 hab hbc))).hom y)) hd
  simp only [map_add, map_neg, map_zero] at hd'
  rw [map_app_map_eq_pb, map_app_map_eq_pb, map_app_map_eq_pb,
    pb_congr h 𝒦 z (face_triple_zero 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hbc))),
    pb_congr h 𝒦 z (face_triple_one 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 (hab.trans hbc)))),
    pb_congr h 𝒦 z (face_triple_two 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono inf_le_left)).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hab)))] at hd'
  unfold P
  linear_combination hd'

noncomputable def Z (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) := by
  classical
  exact if hij : i < j then P h 𝒦 z hij W hW
    else if hji : j < i then -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _))))
    else 0

theorem Z_of_lt {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = P h 𝒦 z hij W hW := by
  classical
  simp only [Z, dif_pos hij]

theorem Z_of_gt {i j : 𝒦.ι} (hji : j < i) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _)))) := by
  classical
  simp only [Z, dif_neg (not_lt_of_gt hji), dif_pos hji]

theorem Z_self (i : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U i)) : Z h 𝒦 z i i W hW = 0 := by
  classical
  simp only [Z, dif_neg (lt_irrefl i)]

theorem Z_of_eq {i j : 𝒦.ι} (e : i = j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Z h 𝒦 z i j W hW = 0 := by
  subst e; exact Z_self h 𝒦 z i W hW

theorem map_Z (i j : 𝒦.ι) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (Z h 𝒦 z i j W hW) = Z h 𝒦 z i j W' hW'' := by
  classical
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_lt h 𝒦 z hij, map_P]
  · simp only [Z_self, map_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_gt h 𝒦 z hji, map_neg, map_P]

theorem Z_swap (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i)) :
    Z h 𝒦 z j i W hW' = -Z h 𝒦 z i j W hW := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_gt h 𝒦 z hij]
  · simp only [Z_self, neg_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_lt h 𝒦 z hji, neg_neg]

theorem Z_add_Z (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) (i j l : 𝒦.ι) (W : X.Opens)
    (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l)) :
    Z h 𝒦 z i j W (hW.trans (h.preimage_mono inf_le_left)) +
        Z h 𝒦 z j l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      Z h 𝒦 z i l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by

  have key : ∀ (a b c : 𝒦.ι) (hab : a < b) (hbc : b < c) (V : X.Opens) (hV : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c))
      (h₁ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b)) (h₂ : V ≤ h ⁻¹ᵁ (𝒦.U b ⊓ 𝒦.U c)) (h₃ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U c)),
      Z h 𝒦 z a b V h₁ + Z h 𝒦 z b c V h₂ = Z h 𝒦 z a c V h₃ := by
    intro a b c hab hbc V hV h₁ h₂ h₃
    rw [Z_of_lt h 𝒦 z hab, Z_of_lt h 𝒦 z hbc, Z_of_lt h 𝒦 z (hab.trans hbc)]
    exact P_add_P h 𝒦 z hz hab hbc V hV
  have hWij : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j) := hW.trans (h.preimage_mono inf_le_left)
  have hWjl : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))
  have hWil : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))
  have hWji : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i) := hWij.trans (le_of_eq (by rw [inf_comm]))
  have hWlj : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U j) := hWjl.trans (le_of_eq (by rw [inf_comm]))
  have hWli : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U i) := hWil.trans (le_of_eq (by rw [inf_comm]))
  have perm : ∀ (a b c : 𝒦.ι), W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l) →
      ({a, b, c} : Set 𝒦.ι) ⊆ {i, j, l} → W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c) := by
    intro a b c hW habc
    refine hW.trans (h.preimage_mono ?_)
    have mem : ∀ x ∈ ({i, j, l} : Set 𝒦.ι), 𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l ≤ 𝒦.U x := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]
    exact le_inf (le_inf (mem a (habc (by simp))) (mem b (habc (by simp)))) (mem c (habc (by simp)))
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · exact key i j l hij hjl W hW hWij hWjl hWil
    · rw [Z_self, add_zero]
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key i l j hil hlj W (perm i l j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWil hWlj hWij
        rw [Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key l i j hli hij W (perm l i j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWli hWij hWlj
        rw [Z_swap h 𝒦 z i l W hWil hWli, Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination e
  · rw [Z_self, zero_add]
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key j i l hji hil W (perm j i l hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWji hWil hWjl
        rw [Z_swap h 𝒦 z i j W hWij hWji] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key j l i hjl hli W (perm j l i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWjl hWli hWji
        rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z i l W hWil hWli] at e
        linear_combination e
    · rw [Z_self, add_zero]
    ·
      have e := key l j i hlj hji W (perm l j i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWlj hWji hWli
      rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z j l W hWjl hWlj, Z_swap h 𝒦 z i l W hWil hWli] at e
      linear_combination -e

end Pairs

section Branches

variable {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R')) {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

theorem inter_le_two (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (s : 𝒲.Idx 1) : 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U (lam (s.1 0)) ⊓ 𝒦.U (lam (s.1 1))) := by
  rw [Scheme.Hom.preimage_inf]
  exact le_inf ((𝒲.inter_le s 0).trans (hlam _)) ((𝒲.inter_le s 1).trans (hlam _))

theorem unitPullback_one_eq_Z (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)
    (s : 𝒲.Idx 1) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z s =
      Z h 𝒦 z (lam (s.1 0)) (lam (s.1 1)) (𝒲.inter s) (inter_le_two h 𝒲 𝒦 lam hlam s) := by
  classical
  have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
  rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_lt hlt)
      · exact absurd hab (ne_of_gt hlt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := by
      rw [Tuple.sort_eq_refl_iff_monotone]
      intro a b hab
      fin_cases a <;> fin_cases b
      · exact le_rfl
      · exact le_of_lt hlt
      · exact absurd hab (by decide)
      · exact le_rfl
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hlt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort, Equiv.Perm.sign_refl,
      Units.val_one, one_smul, Z_of_lt h 𝒦 z hlt]
    exact pb_congr h 𝒦 z hidx _ _ _
  ·
    have hninj : ¬ Function.Injective (lam ∘ s.1) := fun hinj => absurd (hinj (a₁ := 0) (a₂ := 1) heq) (by decide)
    rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hninj]
    exact (Z_of_eq h 𝒦 z heq _ _).symm
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_gt hgt)
      · exact absurd hab (ne_of_lt hgt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := by
      symm
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · intro a b hab
        fin_cases a <;> fin_cases b
        · exact le_rfl
        · exact le_of_lt (by simpa using hgt)
        · exact absurd hab (by decide)
        · exact le_rfl
      · intro a b hab hfab
        exact absurd ((Equiv.swap (0 : Fin 2) 1).injective (hinj hfab)) (ne_of_lt hab)
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hgt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort,
      Equiv.Perm.sign_swap (by decide), Units.val_neg, Units.val_one, neg_one_smul, Z_of_gt h 𝒦 z hgt]
    congr 1
    exact pb_congr h 𝒦 z hidx _ _ _

end Branches

end LamIndepAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LamIndepAux
open scoped TensorProduct

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit πX).cochain 𝒲 0,
      (OModulePresheaf.unit πX).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z - OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' 1 z := by
  classical

  have hle0 : ∀ t : 𝒲.Idx 0, 𝒲.inter t ≤ h ⁻¹ᵁ (𝒦.U (lam (t.1 0)) ⊓ 𝒦.U (lam' (t.1 0))) := fun t => by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf ((𝒲.inter_le t 0).trans (hlam _)) ((𝒲.inter_le t 0).trans (hlam' _))
  refine ⟨fun t => -Z h 𝒦 z (lam (t.1 0)) (lam' (t.1 0)) (𝒲.inter t) (hle0 t), ?_⟩
  funext s

  have hW : 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U (lam (s.1 0)) ⊓ 𝒦.U (lam' (s.1 0)) ⊓ 𝒦.U (lam (s.1 1)) ⊓ 𝒦.U (lam' (s.1 1))) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact le_inf (le_inf (le_inf ((𝒲.inter_le s 0).trans (hlam _)) ((𝒲.inter_le s 0).trans (hlam' _)))
      ((𝒲.inter_le s 1).trans (hlam _))) ((𝒲.inter_le s 1).trans (hlam' _))
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.sub_apply, unitPullback_one_eq_Z πX h 𝒲 𝒦 lam hlam z s,
    unitPullback_one_eq_Z πX h 𝒲 𝒦 lam' hlam' z s]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]

  have hb : ∀ (j : Fin 2), (OModulePresheaf.unit πX).res (𝒲.inter_le_inter_face s j)
      (-Z h 𝒦 z (lam ((𝒲.face s j).1 0)) (lam' ((𝒲.face s j).1 0)) (𝒲.inter (𝒲.face s j)) (hle0 (𝒲.face s j))) =
      -Z h 𝒦 z (lam ((𝒲.face s j).1 0)) (lam' ((𝒲.face s j).1 0)) (𝒲.inter s)
        ((𝒲.inter_le_inter_face s j).trans (hle0 (𝒲.face s j))) := by
    intro j
    show (X.presheaf.map (homOfLE (𝒲.inter_le_inter_face s j)).op).hom (-_) = _
    rw [map_neg, map_Z]
  rw [hb 0, hb 1]

  change -Z h 𝒦 z (lam (s.1 1)) (lam' (s.1 1)) (𝒲.inter s) _ + - -Z h 𝒦 z (lam (s.1 0)) (lam' (s.1 0)) (𝒲.inter s) _ =
    Z h 𝒦 z (lam (s.1 0)) (lam (s.1 1)) (𝒲.inter s) _ - Z h 𝒦 z (lam' (s.1 0)) (lam' (s.1 1)) (𝒲.inter s) _

  have ha : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam (s.1 0)) := (𝒲.inter_le s 0).trans (hlam _)
  have hb : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam (s.1 1)) := (𝒲.inter_le s 1).trans (hlam _)
  have ha' : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam' (s.1 0)) := (𝒲.inter_le s 0).trans (hlam' _)
  have hb' : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U (lam' (s.1 1)) := (𝒲.inter_le s 1).trans (hlam' _)
  have h3 : ∀ (x y w : 𝒦.ι), 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U x → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U y → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U w →
      𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U x ⊓ 𝒦.U y ⊓ 𝒦.U w) := by
    intro x y w hx hy hw
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact le_inf (le_inf hx hy) hw
  have h2 : ∀ (x y : 𝒦.ι), 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U x → 𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.U y → 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U x ⊓ 𝒦.U y) := by
    intro x y hx hy
    rw [Scheme.Hom.preimage_inf]
    exact le_inf hx hy
  have e1 := Z_add_Z h 𝒦 z hz (lam (s.1 0)) (lam' (s.1 0)) (lam (s.1 1)) (𝒲.inter s) (h3 _ _ _ ha ha' hb)
  have e2 := Z_add_Z h 𝒦 z hz (lam' (s.1 0)) (lam' (s.1 1)) (lam (s.1 1)) (𝒲.inter s) (h3 _ _ _ ha' hb' hb)
  have e3 := Z_swap h 𝒦 z (lam (s.1 1)) (lam' (s.1 1)) (𝒲.inter s) (h2 _ _ hb hb') (h2 _ _ hb' hb)
  linear_combination e1 + e2 - e3

end S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero (solution)
