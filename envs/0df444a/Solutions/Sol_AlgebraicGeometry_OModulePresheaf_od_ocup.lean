-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.od_ocup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7b2d81cb-01cc-53fc-b29e-3080b077d3db

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_od_ocup

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace OCechCupLeibnizEngine

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

theorem res_congr {b : ℕ} (β : F.ocochain K b) {w w' : K.OIdx b} (e : w = w') {W : V.Opens}
    (hw : W ≤ K.ointer w) (hw' : W ≤ K.ointer w') : F.res hw (β w) = F.res hw' (β w') := by
  subst e; rfl

omit [CommRing R] in
theorem val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).1 = if i.1 < p.1 then i.1 else i.1 + 1 := by
  by_cases hi : Fin.castSucc i < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi, if_pos (by simpa [Fin.lt_def] using hi)]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hi), if_neg (by simpa [Fin.lt_def] using hi)]; rfl

section Idx

variable {a b n : ℕ} (h : a + b = n) (s : K.OIdx (n + 1))

omit [CommRing R]

theorem front_face_of_le (j : Fin (n + 2)) (hj : j.1 ≤ a) :
    K.ofrontFace a b n h (K.oface s j) =
      K.oface (K.ofrontFace (a + 1) b (n + 1) (by omega) s) ⟨j.1, by omega⟩ := by
  funext i
  show s (j.succAbove ⟨i.1, _⟩) = s ⟨((⟨j.1, _⟩ : Fin (a + 2)).succAbove i).1, _⟩
  apply congrArg s; apply Fin.ext
  rw [val_succAbove, val_succAbove]

theorem back_face_of_le (j : Fin (n + 2)) (hj : j.1 ≤ a) :
    K.obackFace a b n h (K.oface s j) = K.obackFace (a + 1) b (n + 1) (by omega) s := by
  funext i
  show s (j.succAbove ⟨a + i.1, _⟩) = s ⟨a + 1 + i.1, _⟩
  apply congrArg s; apply Fin.ext
  rw [val_succAbove]
  simp only
  rw [if_neg (by omega)]
  omega

theorem front_face_of_lt (j : Fin (n + 2)) (hj : a + 1 ≤ j.1) :
    K.ofrontFace a b n h (K.oface s j) = K.ofrontFace a (b + 1) (n + 1) (by omega) s := by
  funext i
  show s (j.succAbove ⟨i.1, _⟩) = s ⟨i.1, _⟩
  apply congrArg s; apply Fin.ext
  rw [val_succAbove]
  simp only
  rw [if_pos (by omega)]

theorem back_face_of_lt (j : Fin (n + 2)) (y : Fin (b + 1)) (hj : j.1 = a + 1 + y.1) :
    K.obackFace a b n h (K.oface s j) = K.oface (K.obackFace a (b + 1) (n + 1) (by omega) s) y.succ := by
  funext i
  show s (j.succAbove ⟨a + i.1, _⟩) = s ⟨a + (y.succ.succAbove i).1, _⟩
  apply congrArg s; apply Fin.ext
  show (j.succAbove ⟨a + i.1, _⟩).1 = a + (y.succ.succAbove i).1
  rw [val_succAbove, val_succAbove]
  simp only [Fin.val_succ]
  by_cases hi : i.1 < y.1 + 1
  · rw [if_pos (by omega), if_pos hi]
  · rw [if_neg (by omega), if_neg hi]; omega

theorem face_front_last :
    K.oface (K.ofrontFace (a + 1) b (n + 1) (by omega) s) (Fin.last (a + 1)) =
      K.ofrontFace a (b + 1) (n + 1) (by omega) s := by
  funext i
  show s ⟨((Fin.last (a + 1)).succAbove i).1, _⟩ = s ⟨i.1, _⟩
  apply congrArg s; apply Fin.ext
  simp [Fin.succAbove_last]

theorem face_back_zero :
    K.oface (K.obackFace a (b + 1) (n + 1) (by omega) s) 0 = K.obackFace (a + 1) b (n + 1) (by omega) s := by
  funext i
  show s ⟨a + ((0 : Fin (b + 2)).succAbove i).1, _⟩ = s ⟨a + 1 + i.1, _⟩
  apply congrArg s; apply Fin.ext
  simp
  omega

end Idx

section Vals

variable {m : ℕ} (s : K.OIdx m)

def Aval {c : ℕ} (u : K.OIdx c) (hu : K.ointer s ≤ K.ointer u) (γ : (OModulePresheaf.unit π).ocochain K c) :
    Γ(V, K.ointer s) :=
  rO hu (γ u)

def Bval {c : ℕ} (w : K.OIdx c) (hw : K.ointer s ≤ K.ointer w) (γ : F.ocochain K c) : F.obj (K.ointer s) :=
  F.res hw (γ w)

theorem Aval_congr {c : ℕ} {u u' : K.OIdx c} (e : u = u') (hu : K.ointer s ≤ K.ointer u)
    (hu' : K.ointer s ≤ K.ointer u') (γ : (OModulePresheaf.unit π).ocochain K c) :
    Aval (π := π) K s u hu γ = Aval K s u' hu' γ := by
  subst e; rfl

theorem Bval_congr {c : ℕ} {w w' : K.OIdx c} (e : w = w') (hw : K.ointer s ≤ K.ointer w)
    (hw' : K.ointer s ≤ K.ointer w') (γ : F.ocochain K c) :
    Bval F K s w hw γ = Bval F K s w' hw' γ := by
  subst e; rfl

theorem res_cup {a b c : ℕ} (h : a + b = c) (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b)
    (t : K.OIdx c) (ht : K.ointer s ≤ K.ointer t) :
    F.res ht (F.ocup K a b c h α β t) =
      Aval K s (K.ofrontFace a b c h t) (ht.trans (K.ointer_le_ointer_ofrontFace a b c h t)) α •
        Bval F K s (K.obackFace a b c h t) (ht.trans (K.ointer_le_ointer_obackFace a b c h t)) β := by
  rw [OModulePresheaf.ocup_apply, F.res_smul, F.res_res]
  simp only [Aval, Bval, rO]
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem Aval_d {a : ℕ} (α : (OModulePresheaf.unit π).ocochain K a) (t : K.OIdx (a + 1))
    (ht : K.ointer s ≤ K.ointer t) :
    Aval K s t ht ((OModulePresheaf.unit π).od K a α) =
      ∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) • Aval K s (K.oface t i) (ht.trans (K.ointer_le_ointer_oface t i)) α := by
  simp only [Aval, rO]
  rw [OModulePresheaf.od_apply]
  change (V.presheaf.map (homOfLE ht).op).hom
      (∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (V.presheaf.map (homOfLE (K.ointer_le_ointer_oface t i)).op).hom
          (show Γ(V, K.ointer (K.oface t i)) from α (K.oface t i))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem Bval_d {b : ℕ} (β : F.ocochain K b) (t : K.OIdx (b + 1)) (ht : K.ointer s ≤ K.ointer t) :
    Bval F K s t ht (F.od K b β) =
      ∑ i : Fin (b + 2), ((-1 : ℤ) ^ (i : ℕ)) • Bval F K s (K.oface t i) (ht.trans (K.ointer_le_ointer_oface t i)) β := by
  simp only [Bval]
  rw [OModulePresheaf.od_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, F.res_res]

end Vals

theorem od_ocup (a b n : ℕ) (h : a + b = n) (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.od K n (F.ocup K a b n h α β) =
      F.ocup K (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).od K a α) β
        + ((-1 : ℤ) ^ a) • F.ocup K a (b + 1) (n + 1) (by omega) α (F.od K b β) := by
  have h1 : a + 1 + b = n + 1 := by omega
  have h2 : a + (b + 1) = n + 1 := by omega
  funext s
  rw [Pi.add_apply, Pi.smul_apply]

  set fr' := K.ofrontFace (a + 1) b (n + 1) h1 s with hfr'
  set bk := K.obackFace (a + 1) b (n + 1) h1 s with hbk
  set fr := K.ofrontFace a (b + 1) (n + 1) h2 s with hfr
  set bk' := K.obackFace a (b + 1) (n + 1) h2 s with hbk'
  have le_fr' : K.ointer s ≤ K.ointer fr' := K.ointer_le_ointer_ofrontFace _ _ _ h1 s
  have le_bk : K.ointer s ≤ K.ointer bk := K.ointer_le_ointer_obackFace _ _ _ h1 s
  have le_fr : K.ointer s ≤ K.ointer fr := K.ointer_le_ointer_ofrontFace _ _ _ h2 s
  have le_bk' : K.ointer s ≤ K.ointer bk' := K.ointer_le_ointer_obackFace _ _ _ h2 s

  have eL : F.od K n (F.ocup K a b n h α β) s =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (Aval K s (K.ofrontFace a b n h (K.oface s j))
            ((K.ointer_le_ointer_oface s j).trans (K.ointer_le_ointer_ofrontFace a b n h _)) α •
          Bval F K s (K.obackFace a b n h (K.oface s j))
            ((K.ointer_le_ointer_oface s j).trans (K.ointer_le_ointer_obackFace a b n h _)) β) := by
    rw [OModulePresheaf.od_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [res_cup]
  have eR1 : F.ocup K (a + 1) b (n + 1) h1 ((OModulePresheaf.unit π).od K a α) β s =
      ∑ i : Fin (a + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Aval K s (K.oface fr' i) (le_fr'.trans (K.ointer_le_ointer_oface fr' i)) α • Bval F K s bk le_bk β) := by
    have := res_cup F K s h1 ((OModulePresheaf.unit π).od K a α) β s (le_refl _)
    rw [F.res_refl_apply] at this
    rw [this, Aval_d, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_assoc]
  have eR2 : F.ocup K a (b + 1) (n + 1) h2 α (F.od K b β) s =
      ∑ i : Fin (b + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Aval K s fr le_fr α • Bval F K s (K.oface bk' i) (le_bk'.trans (K.ointer_le_ointer_oface bk' i)) β) := by
    have := res_cup F K s h2 α (F.od K b β) s (le_refl _)
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
        (Aval K s (K.ofrontFace a b n h (K.oface s (e (Sum.inl x))))
            ((K.ointer_le_ointer_oface s _).trans (K.ointer_le_ointer_ofrontFace a b n h _)) α •
          Bval F K s (K.obackFace a b n h (K.oface s (e (Sum.inl x))))
            ((K.ointer_le_ointer_oface s _).trans (K.ointer_le_ointer_obackFace a b n h _)) β) =
      ((-1 : ℤ) ^ ((Fin.castSucc x : Fin (a + 2)) : ℕ)) •
        (Aval K s (K.oface fr' (Fin.castSucc x)) (le_fr'.trans (K.ointer_le_ointer_oface fr' _)) α •
          Bval F K s bk le_bk β) := by
    intro x
    have hx : ((e (Sum.inl x) : Fin (n + 2)) : ℕ) ≤ a := by rw [he_inl]; omega
    have hidxA : K.ofrontFace a b n h (K.oface s (e (Sum.inl x))) = K.oface fr' (Fin.castSucc x) :=
      (front_face_of_le K h s _ hx).trans (congrArg (K.oface fr') (Fin.ext (he_inl x)))
    have hidxB : K.obackFace a b n h (K.oface s (e (Sum.inl x))) = bk := back_face_of_le K h s _ hx
    rw [Aval_congr K s hidxA _ (le_fr'.trans (K.ointer_le_ointer_oface fr' _)), Bval_congr F K s hidxB _ le_bk,
      he_inl, Fin.val_castSucc]
  have hInr : ∀ y : Fin (b + 1),
      ((-1 : ℤ) ^ ((e (Sum.inr y) : Fin (n + 2)) : ℕ)) •
        (Aval K s (K.ofrontFace a b n h (K.oface s (e (Sum.inr y))))
            ((K.ointer_le_ointer_oface s _).trans (K.ointer_le_ointer_ofrontFace a b n h _)) α •
          Bval F K s (K.obackFace a b n h (K.oface s (e (Sum.inr y))))
            ((K.ointer_le_ointer_oface s _).trans (K.ointer_le_ointer_obackFace a b n h _)) β) =
      ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ ((y.succ : Fin (b + 2)) : ℕ)) •
        (Aval K s fr le_fr α •
          Bval F K s (K.oface bk' y.succ) (le_bk'.trans (K.ointer_le_ointer_oface bk' _)) β)) := by
    intro y
    have hy : a + 1 ≤ ((e (Sum.inr y) : Fin (n + 2)) : ℕ) := by rw [he_inr]; omega
    have hidxA : K.ofrontFace a b n h (K.oface s (e (Sum.inr y))) = fr := front_face_of_lt K h s _ hy
    have hidxB : K.obackFace a b n h (K.oface s (e (Sum.inr y))) = K.oface bk' y.succ :=
      back_face_of_lt K h s _ y (he_inr y)
    rw [Aval_congr K s hidxA _ le_fr, Bval_congr F K s hidxB _ (le_bk'.trans (K.ointer_le_ointer_oface bk' _)),
      smul_smul, ← pow_add, he_inr, Fin.val_succ]
    congr 1
    rw [show a + 1 + (y : ℕ) = a + ((y : ℕ) + 1) by omega]
  have hLast : ((-1 : ℤ) ^ ((Fin.last (a + 1) : Fin (a + 2)) : ℕ)) •
        (Aval K s (K.oface fr' (Fin.last (a + 1))) (le_fr'.trans (K.ointer_le_ointer_oface fr' _)) α •
          Bval F K s bk le_bk β) = -(((-1 : ℤ) ^ a) • X) := by
    rw [Aval_congr K s (face_front_last K h s) _ le_fr, Fin.val_last, pow_succ, mul_neg_one, neg_smul]
  have hZero : ((-1 : ℤ) ^ (((0 : Fin (b + 2)) : Fin (b + 2)) : ℕ)) •
        (Aval K s fr le_fr α • Bval F K s (K.oface bk' 0) (le_bk'.trans (K.ointer_le_ointer_oface bk' _)) β) = X := by
    rw [Bval_congr F K s (face_back_zero K h s) _ le_bk, Fin.val_zero, pow_zero, one_smul]

  rw [← e.sum_comp, Fintype.sum_sum_type] at eL
  simp only [hInl, hInr] at eL
  rw [Fin.sum_univ_castSucc, hLast] at eR1
  rw [Fin.sum_univ_succ, hZero] at eR2
  rw [eL, eR1, eR2, smul_add, Finset.smul_sum]
  abel

end OCechCupLeibnizEngine

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.od K n (F.ocup K a b n hn α β) =
      F.ocup K (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).od K a α) β +
        ((-1 : ℤ) ^ a) • F.ocup K a (b + 1) (n + 1) (by omega) α (F.od K b β) :=
  OCechCupLeibnizEngine.od_ocup F K a b n hn α β

end

end S_AlgebraicGeometry_OModulePresheaf_od_ocup
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_od_ocup (solution)
