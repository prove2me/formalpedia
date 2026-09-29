-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.orev_ocup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1670983a-d058-5435-98c6-c6952d87de4c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_orev_ocup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace OrevOcupAux

open Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
variable (K : V.OrderedAffineCover)

abbrev rO {U W : V.Opens} (hle : W ≤ U) (x : Γ(V, U)) : Γ(V, W) := (V.presheaf.map (homOfLE hle).op).hom x

omit [CommRing R] in
theorem rO_rO {U U' W : V.Opens} (h₁ : W ≤ U') (h₂ : U' ≤ U) (x : Γ(V, U)) :
    rO (V := V) h₁ (rO h₂ x) = rO (h₁.trans h₂) x := by
  simp only [rO]
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

def Aval {m : ℕ} (s : K.OIdx m) {c : ℕ} (u : K.OIdx c) (hu : K.ointer s ≤ K.ointer u)
    (γ : (OModulePresheaf.unit π).ocochain K c) : Γ(V, K.ointer s) :=
  rO hu (γ u)

theorem Aval_congr {m : ℕ} (s : K.OIdx m) {c : ℕ} {u u' : K.OIdx c} (e : u = u') (hu : K.ointer s ≤ K.ointer u)
    (hu' : K.ointer s ≤ K.ointer u') (γ : (OModulePresheaf.unit π).ocochain K c) :
    Aval (π := π) K s u hu γ = Aval K s u' hu' γ := by
  subst e; rfl

theorem ocup_apply_eq {a b c : ℕ} (h : a + b = c) (α : (OModulePresheaf.unit π).ocochain K a)
    (β : (OModulePresheaf.unit π).ocochain K b) (t : K.OIdx c) :
    (OModulePresheaf.unit π).ocup K a b c h α β t =
      Aval K t (K.ofrontFace a b c h t) (K.ointer_le_ointer_ofrontFace a b c h t) α *
        Aval K t (K.obackFace a b c h t) (K.ointer_le_ointer_obackFace a b c h t) β :=
  rfl

theorem res_ocup {m : ℕ} (s : K.OIdx m) {a b c : ℕ} (h : a + b = c) (α : (OModulePresheaf.unit π).ocochain K a)
    (β : (OModulePresheaf.unit π).ocochain K b) (t : K.OIdx c) (ht : K.ointer s ≤ K.ointer t) :
    (OModulePresheaf.unit π).res ht ((OModulePresheaf.unit π).ocup K a b c h α β t) =
      Aval K s (K.ofrontFace a b c h t) (ht.trans (K.ointer_le_ointer_ofrontFace a b c h t)) α *
        Aval K s (K.obackFace a b c h t) (ht.trans (K.ointer_le_ointer_obackFace a b c h t)) β := by
  rw [OModulePresheaf.ocup_apply, (OModulePresheaf.unit π).res_smul, (OModulePresheaf.unit π).res_res]
  simp only [Aval, rO]
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem Aval_orev {m : ℕ} (s : K.OIdx m) {c : ℕ} (u : K.OIdx c) (hu : K.ointer s ≤ K.ointer u)
    (γ : (OModulePresheaf.unit π).ocochain K c) :
    Aval K s u hu ((OModulePresheaf.unit π).orev K c γ) =
      ((-1 : ℤ) ^ (c * (c + 1) / 2)) • Aval K s (u ∘ Fin.rev) (hu.trans (K.ointer_le_ointer_comp_rev u)) γ := by
  simp only [Aval, rO]
  rw [OModulePresheaf.orev_apply]
  change (V.presheaf.map (homOfLE hu).op).hom (((-1 : ℤ) ^ (c * (c + 1) / 2)) •
      (V.presheaf.map (homOfLE (K.ointer_le_ointer_comp_rev u)).op).hom (show Γ(V, _) from γ (u ∘ Fin.rev))) = _
  rw [map_zsmul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

omit [CommRing R] in

theorem sign_identity (a b : ℕ) :
    (-1 : ℤ) ^ ((a + b) * (a + b + 1) / 2) =
      (-1 : ℤ) ^ (a * b) * ((-1 : ℤ) ^ (b * (b + 1) / 2) * (-1 : ℤ) ^ (a * (a + 1) / 2)) := by
  have ha := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self a)
  have hb := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self b)
  have hE : (a + b) * (a + b + 1) / 2 = a * (a + 1) / 2 + b * (b + 1) / 2 + a * b := by
    have : (a + b) * (a + b + 1) = 2 * (a * (a + 1) / 2 + b * (b + 1) / 2 + a * b) := by
      rw [mul_add 2, mul_add 2, ha, hb]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hE, pow_add, pow_add]
  ring

theorem final_ring {S : Type*} [CommRing S] (A B : S) (ea eb en s : ℤ) (h : en = s * (eb * ea)) :
    en • (A * B) = s • ((eb • B) * (ea • A)) := by
  subst h
  simp only [zsmul_eq_mul]
  push_cast
  ring

end OrevOcupAux

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover OrevOcupAux in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : (OModulePresheaf.unit π).ocochain K b) :
    (OModulePresheaf.unit π).orev K n ((OModulePresheaf.unit π).ocup K a b n hn α β) =
      ((-1 : ℤ) ^ (a * b)) • (OModulePresheaf.unit π).ocup K b a n (by omega)
        ((OModulePresheaf.unit π).orev K b β) ((OModulePresheaf.unit π).orev K a α) := by
  classical
  subst hn
  have hn' : b + a = a + b := Nat.add_comm b a
  funext t

  have hP : K.ofrontFace a b (a + b) rfl (t ∘ Fin.rev) = (K.obackFace b a (a + b) hn' t) ∘ Fin.rev := by
    funext j
    show t (Fin.rev ⟨j.1, _⟩) = t ⟨b + (Fin.rev j).1, _⟩
    apply congrArg t; apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hQ : K.obackFace a b (a + b) rfl (t ∘ Fin.rev) = (K.ofrontFace b a (a + b) hn' t) ∘ Fin.rev := by
    funext j
    show t (Fin.rev ⟨a + j.1, _⟩) = t ⟨(Fin.rev j).1, _⟩
    apply congrArg t; apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [Pi.smul_apply, orev_apply, res_ocup K t rfl α β (t ∘ Fin.rev) (K.ointer_le_ointer_comp_rev t),
    ocup_apply_eq K hn', Aval_orev, Aval_orev,
    Aval_congr K t hP _ ((K.ointer_le_ointer_obackFace b a (a + b) hn' t).trans (K.ointer_le_ointer_comp_rev _)) α,
    Aval_congr K t hQ _ ((K.ointer_le_ointer_ofrontFace b a (a + b) hn' t).trans (K.ointer_le_ointer_comp_rev _)) β]
  exact final_ring (S := Γ(V, K.ointer t)) _ _ _ _ _ _ (sign_identity a b)

end S_AlgebraicGeometry_OModulePresheaf_orev_ocup
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_orev_ocup (solution)
