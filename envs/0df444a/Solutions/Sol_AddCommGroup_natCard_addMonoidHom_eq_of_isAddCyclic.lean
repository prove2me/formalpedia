-- Prove2me | solution 1 for AddCommGroup.natCard_addMonoidHom_eq_of_isAddCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9a3874d8-9fed-5209-ba48-a3adb38d7657

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic

set_option autoImplicit false
open CategoryTheory

namespace HomCountAux

theorem mem_zmultiples_of_smul_eq_zero {q m : ℕ} (hq : 0 < q) (hqm : q ∣ m) (hm : m ≠ 0)
    (y : ZMod m) (hy : q • y = 0) : y ∈ AddSubgroup.zmultiples (((m / q : ℕ) : ZMod m)) := by
  haveI : NeZero m := ⟨hm⟩
  obtain ⟨d, hd⟩ := hqm
  have hd0 : d ≠ 0 := by rintro rfl; exact hm (by simpa using hd)
  have hdq : m / q = d := by rw [hd, Nat.mul_div_cancel_left _ hq]
  have h1 : ((q * y.val : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hy]
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hq ((dvd_of_eq hd.symm).trans h1)
  refine ⟨k, ?_⟩
  show (k : ℤ) • (((m / q : ℕ) : ZMod m)) = y
  rw [hdq, ← ZMod.natCast_zmod_val y, hk, Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast, mul_comm]

theorem natCard_torsion_eq {q m : ℕ} (hq : 0 < q) (hqm : q ∣ m) (hm : m ≠ 0) :
    Nat.card {y : ZMod m // q • y = 0} = q := by
  haveI : NeZero m := ⟨hm⟩
  have hc : q • (((m / q : ℕ) : ZMod m)) = 0 := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hqm, ZMod.natCast_self]
  have hset : ∀ y : ZMod m, q • y = 0 ↔ y ∈ AddSubgroup.zmultiples (((m / q : ℕ) : ZMod m)) := by
    intro y
    constructor
    · exact mem_zmultiples_of_smul_eq_zero hq hqm hm y
    · rintro ⟨k, rfl⟩
      show q • ((k : ℤ) • (((m / q : ℕ) : ZMod m))) = 0
      rw [smul_comm, hc, smul_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset)]
  show Nat.card (AddSubgroup.zmultiples (((m / q : ℕ) : ZMod m))) = q
  obtain ⟨d, hd⟩ := hqm
  have hd0 : d ≠ 0 := by rintro rfl; exact hm (by simpa using hd)
  have hdq : m / q = d := by rw [hd, Nat.mul_div_cancel_left _ hq]
  rw [Nat.card_zmultiples, hdq, ZMod.addOrderOf_coe' m hd0, hd, Nat.gcd_mul_left_left,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]

theorem natCard_hom_zmod_zmod {q m : ℕ} (hq : 0 < q) (hqm : q ∣ m) (hm : m ≠ 0) :
    Nat.card (ZMod q →+ ZMod m) = q := by
  haveI : NeZero m := ⟨hm⟩

  have e1 : (ZMod q →+ ZMod m) ≃ {f : ℤ →+ ZMod m // f q = 0} := (ZMod.lift q).symm
  have e2 : {f : ℤ →+ ZMod m // f q = 0} ≃ {y : ZMod m // q • y = 0} :=
    { toFun := fun f => ⟨f.1 1, by
        have hf : zmultiplesHom (ZMod m) (f.1 1) = f.1 :=
          (Equiv.apply_eq_iff_eq_symm_apply (zmultiplesHom (ZMod m))).mpr rfl
        have h2 : (zmultiplesHom (ZMod m) (f.1 1)) (q : ℤ) = f.1 (q : ℤ) := by rw [hf]
        rw [zmultiplesHom_apply, natCast_zsmul] at h2
        rw [h2]
        exact f.2⟩
      invFun := fun y => ⟨(zmultiplesHom (ZMod m)) y.1, by
        show (zmultiplesHom (ZMod m) y.1) ((q : ℕ) : ℤ) = 0
        rw [zmultiplesHom_apply, natCast_zsmul]
        exact y.2⟩
      left_inv := fun f => by
        apply Subtype.ext
        exact (Equiv.apply_eq_iff_eq_symm_apply (zmultiplesHom (ZMod m))).mpr rfl
      right_inv := fun y => by
        apply Subtype.ext
        show (zmultiplesHom (ZMod m) y.1) 1 = y.1
        rw [zmultiplesHom_apply, one_zsmul] }
  rw [Nat.card_congr e1, Nat.card_congr e2]
  exact natCard_torsion_eq hq hqm hm

end HomCountAux

open HomCountAux in
set_option maxHeartbeats 3200000 in
theorem solution {X Y : Type} [AddCommGroup X] [Finite X] [AddCommGroup Y] [Finite Y]
    [IsAddCyclic Y] (hX : ∀ x : X, Nat.card Y • x = 0) :
    Nat.card (X →+ Y) = Nat.card X := by
  classical
  have hm0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'

  let eY : ZMod (Nat.card Y) ≃+ Y := zmodAddCyclicAddEquiv ‹IsAddCyclic Y›

  obtain ⟨ι, hι, p, hp, e, ⟨eX⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite X

  have e1 : (X →+ Y) ≃ ((DirectSum ι fun i => ZMod (p i ^ e i)) →+ ZMod (Nat.card Y)) :=
    { toFun := fun f => eY.symm.toAddMonoidHom.comp (f.comp eX.symm.toAddMonoidHom)
      invFun := fun g => eY.toAddMonoidHom.comp (g.comp eX.toAddMonoidHom)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  have e2 : ((DirectSum ι fun i => ZMod (p i ^ e i)) →+ ZMod (Nat.card Y)) ≃ ((i : ι) → (ZMod (p i ^ e i) →+ ZMod (Nat.card Y))) :=
    (DFinsupp.liftAddHom (β := fun i => ZMod (p i ^ e i)) (γ := ZMod (Nat.card Y))).symm.toEquiv
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_pi]

  have hdiv : ∀ i, p i ^ e i ∣ Nat.card Y := by
    intro i
    haveI : NeZero (p i ^ e i) := ⟨(pow_pos (hp i).pos _).ne'⟩
    have h := congrArg eX (hX (eX.symm (DirectSum.of (fun i => ZMod (p i ^ e i)) i 1)))
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h
    have h2 := addOrderOf_dvd_of_nsmul_eq_zero h
    rwa [addOrderOf_injective (DirectSum.of (fun i => ZMod (p i ^ e i)) i) (DirectSum.of_injective i) 1,
      ZMod.addOrderOf_one] at h2
  rw [Finset.prod_congr rfl fun i _ => natCard_hom_zmod_zmod (pow_pos (hp i).pos _) (hdiv i) hm0]

  have e3 : (DirectSum ι fun i => ZMod (p i ^ e i)) ≃ ((i : ι) → ZMod (p i ^ e i)) := DFinsupp.equivFunOnFintype
  rw [Nat.card_congr eX.toEquiv, Nat.card_congr e3, Nat.card_pi]
  simp [Nat.card_zmod]

end S_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic
end P2MW
export P2MW.S_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic (solution)
