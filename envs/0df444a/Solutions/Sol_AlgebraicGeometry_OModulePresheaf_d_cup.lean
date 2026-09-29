-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.d_cup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/52c04ddf-a1b3-5ead-811a-1035eba2aa1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_d_cup

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace CechCupLeibnizEngine

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

abbrev rO {U W : V.Opens} (hle : W ≤ U) (x : Γ(V, U)) : Γ(V, W) := (V.presheaf.map (homOfLE hle).op).hom x

omit [CommRing R] in
theorem rO_rO {U U' W : V.Opens} (h₁ : W ≤ U') (h₂ : U' ≤ U) (x : Γ(V, U)) :
    rO (V := V) h₁ (rO h₂ x) = rO (h₁.trans h₂) x := by
  simp only [rO]
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem unit_res_eq {U W : V.Opens} (hle : W ≤ U) (x : Γ(V, U)) :
    (OModulePresheaf.unit π).res hle x = rO hle x :=
  rfl

theorem res_congr {b : ℕ} (β : F.cochain K b) {w w' : K.Idx b} (e : w = w') {W : V.Opens}
    (hw : W ≤ K.inter w) (hw' : W ≤ K.inter w') : F.res hw (β w) = F.res hw' (β w') := by
  subst e; rfl

omit [CommRing R] in
theorem val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).1 = if i.1 < p.1 then i.1 else i.1 + 1 := by
  by_cases hi : Fin.castSucc i < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi, if_pos (by simpa [Fin.lt_def] using hi)]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hi), if_neg (by simpa [Fin.lt_def] using hi)]; rfl

section Idx

variable {a b n : ℕ} (h : a + b = n) (s : K.Idx (n + 1))

omit [CommRing R]

theorem front_face_of_le (j : Fin (n + 2)) (hj : j.1 ≤ a) :
    K.frontFace a b n h (K.face s j) =
      K.face (K.frontFace (a + 1) b (n + 1) (by omega) s) ⟨j.1, by omega⟩ := by
  apply Subtype.ext; funext i
  show s.1 (j.succAbove ⟨i.1, _⟩) = s.1 ⟨((⟨j.1, _⟩ : Fin (a + 2)).succAbove i).1, _⟩
  apply congrArg s.1; apply Fin.ext
  rw [val_succAbove, val_succAbove]

theorem back_face_of_le (j : Fin (n + 2)) (hj : j.1 ≤ a) :
    K.backFace a b n h (K.face s j) = K.backFace (a + 1) b (n + 1) (by omega) s := by
  apply Subtype.ext; funext i
  show s.1 (j.succAbove ⟨a + i.1, _⟩) = s.1 ⟨a + 1 + i.1, _⟩
  apply congrArg s.1; apply Fin.ext
  rw [val_succAbove]
  simp only
  rw [if_neg (by omega)]
  omega

theorem front_face_of_lt (j : Fin (n + 2)) (hj : a + 1 ≤ j.1) :
    K.frontFace a b n h (K.face s j) = K.frontFace a (b + 1) (n + 1) (by omega) s := by
  apply Subtype.ext; funext i
  show s.1 (j.succAbove ⟨i.1, _⟩) = s.1 ⟨i.1, _⟩
  apply congrArg s.1; apply Fin.ext
  rw [val_succAbove]
  simp only
  rw [if_pos (by omega)]

theorem back_face_of_lt (j : Fin (n + 2)) (y : Fin (b + 1)) (hj : j.1 = a + 1 + y.1) :
    K.backFace a b n h (K.face s j) = K.face (K.backFace a (b + 1) (n + 1) (by omega) s) y.succ := by
  apply Subtype.ext; funext i
  show s.1 (j.succAbove ⟨a + i.1, _⟩) = s.1 ⟨a + (y.succ.succAbove i).1, _⟩
  apply congrArg s.1; apply Fin.ext
  show (j.succAbove ⟨a + i.1, _⟩).1 = a + (y.succ.succAbove i).1
  rw [val_succAbove, val_succAbove]
  simp only [Fin.val_succ]
  by_cases hi : i.1 < y.1 + 1
  · rw [if_pos (by omega), if_pos hi]
  · rw [if_neg (by omega), if_neg hi]; omega

theorem face_front_last :
    K.face (K.frontFace (a + 1) b (n + 1) (by omega) s) (Fin.last (a + 1)) =
      K.frontFace a (b + 1) (n + 1) (by omega) s := by
  apply Subtype.ext; funext i
  show s.1 ⟨((Fin.last (a + 1)).succAbove i).1, _⟩ = s.1 ⟨i.1, _⟩
  apply congrArg s.1; apply Fin.ext
  simp [Fin.succAbove_last]

theorem face_back_zero :
    K.face (K.backFace a (b + 1) (n + 1) (by omega) s) 0 = K.backFace (a + 1) b (n + 1) (by omega) s := by
  apply Subtype.ext; funext i
  show s.1 ⟨a + ((0 : Fin (b + 2)).succAbove i).1, _⟩ = s.1 ⟨a + 1 + i.1, _⟩
  apply congrArg s.1; apply Fin.ext
  simp
  omega

end Idx

section Vals

variable {m : ℕ} (s : K.Idx m)

def Aval {c : ℕ} (u : K.Idx c) (hu : K.inter s ≤ K.inter u) (γ : (OModulePresheaf.unit π).cochain K c) :
    Γ(V, K.inter s) :=
  rO hu (γ u)

def Bval {c : ℕ} (w : K.Idx c) (hw : K.inter s ≤ K.inter w) (γ : F.cochain K c) : F.obj (K.inter s) :=
  F.res hw (γ w)

theorem Aval_congr {c : ℕ} {u u' : K.Idx c} (e : u = u') (hu : K.inter s ≤ K.inter u)
    (hu' : K.inter s ≤ K.inter u') (γ : (OModulePresheaf.unit π).cochain K c) :
    Aval (π := π) K s u hu γ = Aval K s u' hu' γ := by
  subst e; rfl

theorem Bval_congr {c : ℕ} {w w' : K.Idx c} (e : w = w') (hw : K.inter s ≤ K.inter w)
    (hw' : K.inter s ≤ K.inter w') (γ : F.cochain K c) :
    Bval F K s w hw γ = Bval F K s w' hw' γ := by
  subst e; rfl

theorem res_cup {a b c : ℕ} (h : a + b = c) (α : (OModulePresheaf.unit π).cochain K a) (β : F.cochain K b)
    (t : K.Idx c) (ht : K.inter s ≤ K.inter t) :
    F.res ht (F.cup K a b c h α β t) =
      Aval K s (K.frontFace a b c h t) (ht.trans (K.inter_le_inter_frontFace a b c h t)) α •
        Bval F K s (K.backFace a b c h t) (ht.trans (K.inter_le_inter_backFace a b c h t)) β := by
  rw [OModulePresheaf.cup_apply, F.res_smul, F.res_res]
  simp only [Aval, Bval, rO]
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem Aval_d {a : ℕ} (α : (OModulePresheaf.unit π).cochain K a) (t : K.Idx (a + 1))
    (ht : K.inter s ≤ K.inter t) :
    Aval K s t ht ((OModulePresheaf.unit π).d K a α) =
      ∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) • Aval K s (K.face t i) (ht.trans (K.inter_le_inter_face t i)) α := by
  simp only [Aval, rO]
  rw [OModulePresheaf.d_apply]
  change (V.presheaf.map (homOfLE ht).op).hom
      (∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (V.presheaf.map (homOfLE (K.inter_le_inter_face t i)).op).hom
          (show Γ(V, K.inter (K.face t i)) from α (K.face t i))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem Bval_d {b : ℕ} (β : F.cochain K b) (t : K.Idx (b + 1)) (ht : K.inter s ≤ K.inter t) :
    Bval F K s t ht (F.d K b β) =
      ∑ i : Fin (b + 2), ((-1 : ℤ) ^ (i : ℕ)) • Bval F K s (K.face t i) (ht.trans (K.inter_le_inter_face t i)) β := by
  simp only [Bval]
  rw [OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, F.res_res]

end Vals

theorem d_cup (a b n : ℕ) (h : a + b = n) (α : (OModulePresheaf.unit π).cochain K a) (β : F.cochain K b) :
    F.d K n (F.cup K a b n h α β) =
      F.cup K (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).d K a α) β
        + ((-1 : ℤ) ^ a) • F.cup K a (b + 1) (n + 1) (by omega) α (F.d K b β) := by
  have h1 : a + 1 + b = n + 1 := by omega
  have h2 : a + (b + 1) = n + 1 := by omega
  funext s
  rw [Pi.add_apply, Pi.smul_apply]

  set fr' := K.frontFace (a + 1) b (n + 1) h1 s with hfr'
  set bk := K.backFace (a + 1) b (n + 1) h1 s with hbk
  set fr := K.frontFace a (b + 1) (n + 1) h2 s with hfr
  set bk' := K.backFace a (b + 1) (n + 1) h2 s with hbk'
  have le_fr' : K.inter s ≤ K.inter fr' := K.inter_le_inter_frontFace _ _ _ h1 s
  have le_bk : K.inter s ≤ K.inter bk := K.inter_le_inter_backFace _ _ _ h1 s
  have le_fr : K.inter s ≤ K.inter fr := K.inter_le_inter_frontFace _ _ _ h2 s
  have le_bk' : K.inter s ≤ K.inter bk' := K.inter_le_inter_backFace _ _ _ h2 s

  have eL : F.d K n (F.cup K a b n h α β) s =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (Aval K s (K.frontFace a b n h (K.face s j))
            ((K.inter_le_inter_face s j).trans (K.inter_le_inter_frontFace a b n h _)) α •
          Bval F K s (K.backFace a b n h (K.face s j))
            ((K.inter_le_inter_face s j).trans (K.inter_le_inter_backFace a b n h _)) β) := by
    rw [OModulePresheaf.d_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [res_cup]
  have eR1 : F.cup K (a + 1) b (n + 1) h1 ((OModulePresheaf.unit π).d K a α) β s =
      ∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Aval K s (K.face fr' i) (le_fr'.trans (K.inter_le_inter_face fr' i)) α • Bval F K s bk le_bk β) := by
    have := res_cup F K s h1 ((OModulePresheaf.unit π).d K a α) β s (le_refl _)
    rw [F.res_refl_apply] at this
    rw [this, Aval_d, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_assoc]
  have eR2 : F.cup K a (b + 1) (n + 1) h2 α (F.d K b β) s =
      ∑ i : Fin (b + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Aval K s fr le_fr α • Bval F K s (K.face bk' i) (le_bk'.trans (K.inter_le_inter_face bk' i)) β) := by
    have := res_cup F K s h2 α (F.d K b β) s (le_refl _)
    rw [F.res_refl_apply] at this
    rw [this, Bval_d, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm]

  let e : Fin (a + 1) ⊕ Fin (b + 1) ≃ Fin (n + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have he_inl : ∀ x : Fin (a + 1), ((e (Sum.inl x) : Fin (n + 2)) : ℕ) = x := by
    intro x; simp [e]
  have he_inr : ∀ y : Fin (b + 1), ((e (Sum.inr y) : Fin (n + 2)) : ℕ) = a + 1 + y := by
    intro y; simp [e]

  set X := Aval K s fr le_fr α • Bval F K s bk le_bk β with hX
  have hInl : ∀ x : Fin (a + 1),
      ((-1 : ℤ) ^ ((e (Sum.inl x) : Fin (n + 2)) : ℕ)) •
        (Aval K s (K.frontFace a b n h (K.face s (e (Sum.inl x))))
            ((K.inter_le_inter_face s _).trans (K.inter_le_inter_frontFace a b n h _)) α •
          Bval F K s (K.backFace a b n h (K.face s (e (Sum.inl x))))
            ((K.inter_le_inter_face s _).trans (K.inter_le_inter_backFace a b n h _)) β) =
      ((-1 : ℤ) ^ ((Fin.castSucc x : Fin (a + 2)) : ℕ)) •
        (Aval K s (K.face fr' (Fin.castSucc x)) (le_fr'.trans (K.inter_le_inter_face fr' _)) α •
          Bval F K s bk le_bk β) := by
    intro x
    have hx : ((e (Sum.inl x) : Fin (n + 2)) : ℕ) ≤ a := by rw [he_inl]; omega
    have hidxA : K.frontFace a b n h (K.face s (e (Sum.inl x))) = K.face fr' (Fin.castSucc x) :=
      (front_face_of_le K h s _ hx).trans (congrArg (K.face fr') (Fin.ext (he_inl x)))
    have hidxB : K.backFace a b n h (K.face s (e (Sum.inl x))) = bk := back_face_of_le K h s _ hx
    rw [Aval_congr K s hidxA _ (le_fr'.trans (K.inter_le_inter_face fr' _)), Bval_congr F K s hidxB _ le_bk,
      he_inl, Fin.val_castSucc]
  have hInr : ∀ y : Fin (b + 1),
      ((-1 : ℤ) ^ ((e (Sum.inr y) : Fin (n + 2)) : ℕ)) •
        (Aval K s (K.frontFace a b n h (K.face s (e (Sum.inr y))))
            ((K.inter_le_inter_face s _).trans (K.inter_le_inter_frontFace a b n h _)) α •
          Bval F K s (K.backFace a b n h (K.face s (e (Sum.inr y))))
            ((K.inter_le_inter_face s _).trans (K.inter_le_inter_backFace a b n h _)) β) =
      ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ ((y.succ : Fin (b + 2)) : ℕ)) •
        (Aval K s fr le_fr α •
          Bval F K s (K.face bk' y.succ) (le_bk'.trans (K.inter_le_inter_face bk' _)) β)) := by
    intro y
    have hy : a + 1 ≤ ((e (Sum.inr y) : Fin (n + 2)) : ℕ) := by rw [he_inr]; omega
    have hidxA : K.frontFace a b n h (K.face s (e (Sum.inr y))) = fr := front_face_of_lt K h s _ hy
    have hidxB : K.backFace a b n h (K.face s (e (Sum.inr y))) = K.face bk' y.succ :=
      back_face_of_lt K h s _ y (he_inr y)
    rw [Aval_congr K s hidxA _ le_fr, Bval_congr F K s hidxB _ (le_bk'.trans (K.inter_le_inter_face bk' _)),
      smul_smul, ← pow_add, he_inr, Fin.val_succ]
    congr 1
    rw [show a + 1 + (y : ℕ) = a + ((y : ℕ) + 1) by omega]
  have hLast : ((-1 : ℤ) ^ ((Fin.last (a + 1) : Fin (a + 2)) : ℕ)) •
        (Aval K s (K.face fr' (Fin.last (a + 1))) (le_fr'.trans (K.inter_le_inter_face fr' _)) α •
          Bval F K s bk le_bk β) = -(((-1 : ℤ) ^ a) • X) := by
    rw [Aval_congr K s (face_front_last K h s) _ le_fr, Fin.val_last, pow_succ, mul_neg_one, neg_smul]
  have hZero : ((-1 : ℤ) ^ (((0 : Fin (b + 2)) : Fin (b + 2)) : ℕ)) •
        (Aval K s fr le_fr α • Bval F K s (K.face bk' 0) (le_bk'.trans (K.inter_le_inter_face bk' _)) β) = X := by
    rw [Bval_congr F K s (face_back_zero K h s) _ le_bk, Fin.val_zero, pow_zero, one_smul]

  rw [← e.sum_comp, Fintype.sum_sum_type] at eL
  simp only [hInl, hInr] at eL
  rw [Fin.sum_univ_castSucc, hLast] at eR1
  rw [Fin.sum_univ_succ, hZero] at eR2
  rw [eL, eR1, eR2, smul_add, Finset.smul_sum]
  abel

section Deg11

variable (s : K.Idx 2)
omit [CommRing R]

theorem frontFace_one_one : K.frontFace 1 1 2 rfl s = K.face s 2 := by
  apply Subtype.ext; funext i
  show s.1 ⟨i.1, _⟩ = s.1 ((2 : Fin 3).succAbove i)
  apply congrArg s.1; apply Fin.ext
  rw [val_succAbove]
  have := i.2
  simp only [Fin.isValue, Fin.val_two]
  rw [if_pos (by omega)]

theorem backFace_one_one : K.backFace 1 1 2 rfl s = K.face s 0 := by
  apply Subtype.ext; funext i
  show s.1 ⟨1 + i.1, _⟩ = s.1 ((0 : Fin 3).succAbove i)
  apply congrArg s.1; apply Fin.ext
  simp only [Fin.succAbove_zero, Fin.val_succ]
  omega

end Deg11

theorem cup_add_cup_swap_eq_d (α β : (t : K.Idx 1) → Γ(V, K.inter t))
    (hα : (OModulePresheaf.unit π).d K 1 α = 0) (hβ : (OModulePresheaf.unit π).d K 1 β = 0) :
    (OModulePresheaf.unit π).cup K 1 1 2 rfl α β + (OModulePresheaf.unit π).cup K 1 1 2 rfl β α =
      (OModulePresheaf.unit π).d K 1 (fun t => -(α t * β t)) := by
  funext s
  have hfr := frontFace_one_one K s
  have hbk := backFace_one_one K s

  have cα : Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) α - Aval (π := π) K s (K.face s 1) (K.inter_le_inter_face s 1) α
      + Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) α = 0 := by
    have := congrFun hα s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_three] at this
    simp [Aval, rO, unit_res_eq, pow_succ, sub_eq_add_neg] at this ⊢
    exact this
  have cβ : Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) β - Aval (π := π) K s (K.face s 1) (K.inter_le_inter_face s 1) β
      + Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) β = 0 := by
    have := congrFun hβ s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_three] at this
    simp [Aval, rO, unit_res_eq, pow_succ, sub_eq_add_neg] at this ⊢
    exact this

  have cupαβ : (OModulePresheaf.unit π).cup K 1 1 2 rfl α β s =
      Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) α * Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) β := by
    have := res_cup (OModulePresheaf.unit π) K s rfl α β s (le_refl _)
    rw [(OModulePresheaf.unit π).res_refl_apply] at this
    rw [this, Aval_congr K s hfr _ (K.inter_le_inter_face s 2), Bval_congr _ K s hbk _ (K.inter_le_inter_face s 0)]
    rfl
  have cupβα : (OModulePresheaf.unit π).cup K 1 1 2 rfl β α s =
      Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) β * Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) α := by
    have := res_cup (OModulePresheaf.unit π) K s rfl β α s (le_refl _)
    rw [(OModulePresheaf.unit π).res_refl_apply] at this
    rw [this, Aval_congr K s hfr _ (K.inter_le_inter_face s 2), Bval_congr _ K s hbk _ (K.inter_le_inter_face s 0)]
    rfl

  have dγ : (OModulePresheaf.unit π).d K 1 (fun t => -(α t * β t)) s =
      -(Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) α * Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) β)
        - -(Aval (π := π) K s (K.face s 1) (K.inter_le_inter_face s 1) α * Aval (π := π) K s (K.face s 1) (K.inter_le_inter_face s 1) β)
        + -(Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) α
            * Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) β) := by
    rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
    simp only [Aval, rO, unit_res_eq, map_mul, map_neg, pow_zero, pow_one, neg_one_sq, one_smul, neg_smul,
      Fin.val_zero, Fin.val_one, Fin.val_two, sub_eq_add_neg]
    rfl
  rw [Pi.add_apply, cupαβ, cupβα, dγ]

  change Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) α
        * Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) β
      + Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) β
        * Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) α = _
  linear_combination Aval (π := π) K s (K.face s 1) (K.inter_le_inter_face s 1) β * cα
    + (Aval (π := π) K s (K.face s 0) (K.inter_le_inter_face s 0) α
        + Aval (π := π) K s (K.face s 2) (K.inter_le_inter_face s 2) α) * cβ

end CechCupLeibnizEngine

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (a b n : ℕ) (h : a + b = n) (α : (OModulePresheaf.unit π).cochain K a) (β : F.cochain K b) :
    F.d K n (F.cup K a b n h α β) =
      F.cup K (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).d K a α) β
        + ((-1 : ℤ) ^ a) • F.cup K a (b + 1) (n + 1) (by omega) α (F.d K b β) :=
  CechCupLeibnizEngine.d_cup F K a b n h α β

end

end S_AlgebraicGeometry_OModulePresheaf_d_cup
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_d_cup (solution)
