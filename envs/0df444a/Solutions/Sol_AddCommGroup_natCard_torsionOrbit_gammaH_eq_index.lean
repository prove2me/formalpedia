-- Prove2me | solution 1 for AddCommGroup.natCard_torsionOrbit_gammaH_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a586b085-2fda-5e34-bcb0-3c3f7cb56804

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups

noncomputable section

namespace P2MKcXHCount

section Orb

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]

theorem nsmul_eq_mod_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : n • P = (n % M) • P := by
  conv_lhs => rw [← Nat.mod_add_div n M, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

theorem val_natCast_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : ((n : ZMod M).val) • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul hP]

theorem val_mul_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u * v).val • P = u.val • (v.val • P) := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul hP, mul_nsmul']

theorem val_add_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u + v).val • P = u.val • P + v.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul hP, add_nsmul]

theorem val_neg_nsmul {P : A} (hP : M • P = 0) (u : ZMod M) : (-u).val • P = -(u.val • P) := by
  have h : (-u + u).val • P = 0 := by rw [neg_add_cancel, ZMod.val_zero, zero_nsmul]
  rw [val_add_nsmul hP] at h
  exact eq_neg_of_add_eq_zero_left h

theorem val_sub_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u - v).val • P = u.val • P - v.val • P := by
  rw [sub_eq_add_neg, val_add_nsmul hP, val_neg_nsmul hP, ← sub_eq_add_neg]

theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem nsmul_val_nsmul {P : A} (hP : M • P = 0) (n : ℕ) (u : ZMod M) :
    n • (u.val • P) = ((n : ZMod M) * u).val • P := by
  rw [val_mul_nsmul hP, val_natCast_nsmul (by rw [nsmul_left_comm, hP, nsmul_zero])]

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_orb_self {P : A} (hP : M • P = 0) : P ∈ orb H P :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul hP]⟩

theorem nsmul_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : M • T = 0 := by
  obtain ⟨u, -, rfl⟩ := hT
  rw [nsmul_left_comm, hP, nsmul_zero]

theorem orb_eq_of_mem {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : orb H T = orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  ext W
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v * u, Subgroup.mul_mem _ hv hu, ?_⟩
    rw [Units.val_mul, val_mul_nsmul hP]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * u⁻¹, Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hu), ?_⟩
    rw [← val_mul_nsmul hP, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem neg_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : -T ∈ orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  refine ⟨-1 * u, Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu, ?_⟩
  rw [Units.val_mul, val_mul_nsmul hP, Units.val_neg, Units.val_one, val_neg_nsmul, val_one_nsmul]
  all_goals rw [nsmul_left_comm, hP, nsmul_zero]

theorem orb_neg {P : A} (hP : M • P = 0) : orb H (-P) = orb H P :=
  orb_eq_of_mem H hP (neg_mem_orb H hP (mem_orb_self H hP))

theorem image_orb {B : Type*} [AddCommGroup B] (m : A →+ B) (P : A) :
    m '' orb H P = orb H (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

variable {H}

theorem XH.nsmul_eq_zero (s : XH A M H) {T : A} (hT : T ∈ s.1) : M • T = 0 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT
  exact nsmul_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

theorem XH.eq_orb_of_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : s.1 = orb H T := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact (orb_eq_of_mem H (nsmul_of_addOrderOf_eq hP) hT).symm

theorem XH.neg_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : -T ∈ s.1 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact neg_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

def mapX {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) (s : XH A M H) :
    XH B M H :=
  ⟨m '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    exact ⟨m P, by rw [addOrderOf_injective m hm, hP], by rw [hs, image_orb]⟩⟩

@[scoped simp] theorem mapX_val {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) : (mapX m hm s).1 = m '' s.1 := rfl

theorem mapX_mapX {B C : Type*} [AddCommGroup B] [AddCommGroup C] (m : B →+ C) (m' : A →+ B)
    (hm : Function.Injective m) (hm' : Function.Injective m') (s : XH A M H) :
    mapX m hm (mapX m' hm' s) = mapX (m.comp m') (hm.comp hm') s :=
  XH.ext' (by simp [Set.image_image])

theorem mapX_congr {B : Type*} [AddCommGroup B] {m m' : A →+ B} (hm : Function.Injective m)
    (hm' : Function.Injective m') (h : m = m') (s : XH A M H) : mapX m hm s = mapX m' hm' s := by
  subst h; rfl

theorem mapX_id' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  have : (m : A → A) = id := funext h
  simp [this]

theorem mapX_neg' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = -a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  rw [mapX_val, hs, image_orb, h, orb_neg H (nsmul_of_addOrderOf_eq hP)]

theorem mapX_eq_of_forall_mem {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) (s' : XH B M H) (h : ∀ T ∈ s.1, m T ∈ s'.1) : mapX m hm s = s' := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  have hPs : P ∈ s.1 := by rw [hs]; exact mem_orb_self H (nsmul_of_addOrderOf_eq hP)
  rw [mapX_val, hs, image_orb, XH.eq_orb_of_mem s' (h P hPs)]

theorem mapX_injective {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) :
    Function.Injective (mapX (M := M) (H := H) m hm) := fun s s' h =>
  XH.ext' ((Set.image_injective.mpr hm) (congrArg Subtype.val h))

end Orb

section Level

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

abbrev ent (M : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((g i j : ℤ) : ZMod M)

abbrev row (M : ℕ) (g : SL(2, ℤ)) : V M := (ent M g 1 0, ent M g 1 1)

def ract (v : V M) (g : SL(2, ℤ)) : V M :=
  (v.1 * ent M g 0 0 + v.2 * ent M g 1 0, v.1 * ent M g 0 1 + v.2 * ent M g 1 1)

theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent M (g * h) i j = ent M g i 0 * ent M h 0 j + ent M g i 1 * ent M h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem ent_one (i j : Fin 2) : ent M 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

theorem ent_neg (g : SL(2, ℤ)) (i j : Fin 2) : ent M (-g) i j = -ent M g i j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_neg]
  rw [Matrix.neg_apply]
  push_cast
  rfl

theorem ract_one (v : V M) : ract v 1 = v := by
  simp only [ract, ent_one]
  simp

theorem ract_mul (v : V M) (g h : SL(2, ℤ)) : ract v (g * h) = ract (ract v g) h := by
  simp only [ract, ent_mul]
  ext <;> ring

theorem ract_neg_one (v : V M) : ract v (-1) = -v := by
  simp only [ract, ent_neg, ent_one]
  ext <;> simp

theorem row_eq_ract (g : SL(2, ℤ)) : row M g = ract ((0 : ZMod M), (1 : ZMod M)) g := by
  simp [ract]

theorem row_one : row M 1 = ((0 : ZMod M), (1 : ZMod M)) := by
  rw [row_eq_ract, ract_one]

def ractHom (M : ℕ) (g : SL(2, ℤ)) : V M →+ V M where
  toFun v := ract v g
  map_zero' := by simp [ract]
  map_add' v w := by simp only [ract]; ext <;> simp <;> ring

@[scoped simp] theorem ractHom_apply (g : SL(2, ℤ)) (v : V M) : ractHom M g v = ract v g := rfl

theorem ract_injective (g : SL(2, ℤ)) : Function.Injective (fun v : V M => ract v g) := by
  intro v w h
  have := congrArg (fun z => ract z g⁻¹) h
  simpa only [← ract_mul, mul_inv_cancel, ract_one] using this

theorem ractHom_injective (g : SL(2, ℤ)) : Function.Injective (ractHom M g) := ract_injective g

theorem ractHom_comp (g h : SL(2, ℤ)) :
    (ractHom M h).comp (ractHom M g) = ractHom M (g * h) := by
  ext v <;> simp [ract_mul]

variable (H)

scoped instance actXV : MulAction SL(2, ℤ) (XH (V M) M H) where
  smul g s := mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s
  one_smul s := mapX_id' _ (fun v => by simp [ract_one]) s
  mul_smul g h s := by
    show mapX (ractHom M (g * h)⁻¹) _ s = mapX (ractHom M g⁻¹) _ (mapX (ractHom M h⁻¹) _ s)
    rw [mapX_mapX]
    exact mapX_congr _ _ (by rw [ractHom_comp, mul_inv_rev]) s

variable {H}

theorem smul_def (g : SL(2, ℤ)) (s : XH (V M) M H) :
    g • s = mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s := rfl

theorem smul_val (g : SL(2, ℤ)) (s : XH (V M) M H) :
    (g • s).1 = (fun v => ract v g⁻¹) '' s.1 := rfl

theorem neg_one_smul' (s : XH (V M) M H) : (-1 : SL(2, ℤ)) • s = s := by
  rw [smul_def]
  refine mapX_neg' _ (fun v => ?_) s
  rw [ractHom_apply]
  have : (-1 : SL(2, ℤ))⁻¹ = -1 := by rw [inv_eq_iff_mul_eq_one, neg_mul_neg, one_mul]
  rw [this, ract_neg_one]

theorem neg_smul' (g : SL(2, ℤ)) (s : XH (V M) M H) : (-g) • s = g • s := by
  rw [← neg_one_mul, mul_smul, neg_one_smul']

section WithLevel

variable (hL1 : ∀ v : V M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2)
  (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M)
  (hL3 : ∀ a b : SL(2, ℤ), orb H (row M a) = orb H (row M b) ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1))

def X0 (H : Subgroup (ZMod M)ˣ) (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M) : XH (V M) M H :=
  ⟨orb H ((0 : ZMod M), (1 : ZMod M)), _, by simpa [row_one] using hL2 1, rfl⟩

theorem X0_val : (X0 H hL2).1 = orb H (row M 1) := by rw [row_one]; rfl

theorem smul_X0_val (g : SL(2, ℤ)) : (g • X0 H hL2).1 = orb H (row M g⁻¹) := by
  rw [smul_val, show (X0 H hL2).1 = orb H ((0 : ZMod M), 1) from rfl,
    show (fun v : V M => ract v g⁻¹) = ractHom M g⁻¹ from rfl, image_orb, ractHom_apply, ← row_eq_ract]

include hL1 in
theorem exists_smul_X0_eq (s : XH (V M) M H) : ∃ g : SL(2, ℤ), g • X0 H hL2 = s := by
  obtain ⟨v, hv, hs⟩ := s.2
  obtain ⟨a, ha1, ha2⟩ := hL1 v hv
  refine ⟨a⁻¹, XH.ext' ?_⟩
  rw [smul_X0_val, inv_inv, hs]
  congr 1
  exact Prod.ext ha1 ha2

include hL3 in
theorem stabilizer_X0 :
    MulAction.stabilizer SL(2, ℤ) (X0 H hL2) = CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  ext g
  have h3 := hL3 1 g⁻¹
  rw [inv_one, mul_one] at h3
  rw [MulAction.mem_stabilizer_iff, ← Subgroup.inv_mem_iff (x := g), ← h3, ← X0_val (hL2 := hL2),
    ← smul_X0_val (hL2 := hL2)]
  exact ⟨fun h => congrArg Subtype.val h.symm, fun h => (XH.ext' h).symm⟩

include hL1 hL2 hL3 in

theorem natCard_XV :
    Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  haveI : MulAction.IsPretransitive SL(2, ℤ) (XH (V M) M H) := ⟨fun s t => by
    obtain ⟨g, rfl⟩ := exists_smul_X0_eq hL1 hL2 s
    obtain ⟨h, rfl⟩ := exists_smul_X0_eq hL1 hL2 t
    exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩
  rw [Subgroup.index_eq_card, ← stabilizer_X0 hL2 hL3]
  have e1 : XH (V M) M H ≃ MulAction.orbit SL(2, ℤ) (X0 H hL2) :=
    (Equiv.Set.univ _).symm.trans (Equiv.setCongr (MulAction.orbit_eq_univ SL(2, ℤ) (X0 H hL2)).symm)
  exact Nat.card_congr (e1.trans (MulAction.orbitEquivQuotientStabilizer SL(2, ℤ) (X0 H hL2)))

end WithLevel

end Level

section Transport

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)

def iota : V M →+ A :=
  ((Submodule.torsionBy ℤ A M).subtype.toAddMonoidHom).comp e.toAddMonoidHom

theorem iota_apply (c : V M) : iota e c = ((e c : Submodule.torsionBy ℤ A M) : A) := rfl

theorem iota_injective : Function.Injective (iota e) := by
  intro c d h
  rw [iota_apply, iota_apply] at h
  exact e.injective (Subtype.ext h)

theorem exists_iota_eq (T : A) (hT : M • T = 0) : ∃ c : V M, iota e c = T := by
  have hT' : T ∈ Submodule.torsionBy ℤ A M := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hT
  refine ⟨e.symm ⟨T, hT'⟩, ?_⟩
  rw [iota_apply, AddEquiv.apply_symm_apply]

def theta (s : XH (V M) M H) : XH A M H := mapX (iota e) (iota_injective e) s

theorem theta_bijective : Function.Bijective (theta (H := H) e) := by
  refine ⟨mapX_injective (iota e) (iota_injective e), fun t => ?_⟩
  obtain ⟨Q, hQ, ht⟩ := t.2
  obtain ⟨c, rfl⟩ := exists_iota_eq e Q (nsmul_of_addOrderOf_eq hQ)
  refine ⟨⟨orb H c, c, ?_, rfl⟩, XH.ext' ?_⟩
  · rwa [addOrderOf_injective _ (iota_injective e)] at hQ
  · show iota e '' orb H c = t.1
    rw [image_orb, ht]

include e in
theorem natCard_XH_eq : Nat.card (XH A M H) = Nat.card (XH (V M) M H) :=
  (Nat.card_eq_of_bijective _ (theta_bijective (H := H) e)).symm

end Transport

end P2MKcXHCount
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.P2MKcXHCount"

open P2MKcXHCount in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card {s : Set A // ∃ P : A, addOrderOf P = M ∧
        s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  obtain ⟨hL1, hL2, hL3⟩ := CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff M H
  have hXV : Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index :=
    natCard_XV hL1 hL2 hL3
  have h := natCard_XH_eq (H := H) e
  rw [hXV] at h
  exact h

end
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.P2MKcXHCount"

end S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index
end P2MW
export P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index (solution)
