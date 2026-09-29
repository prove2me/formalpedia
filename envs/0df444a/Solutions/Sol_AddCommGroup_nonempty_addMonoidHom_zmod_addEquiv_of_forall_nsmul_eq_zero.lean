-- Prove2me | solution 1 for AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/08eaa002-f0e2-545a-be39-376d701d38a0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero

set_option autoImplicit false

open scoped BigOperators

universe u

namespace PoleB1

theorem exists_addMonoidHom_injective_forall_nsmul_eq_zero_iff {M n : ℕ} [NeZero M] (hn : n ∣ M) :
    ∃ g : ZMod n →+ ZMod M, Function.Injective g ∧ ∀ y : ZMod M, n • y = 0 ↔ y ∈ Set.range g := by
  obtain ⟨q, hq⟩ := hn
  have hM : M ≠ 0 := NeZero.ne M
  have hn0 : n ≠ 0 := by rintro rfl; rw [zero_mul] at hq; exact hM hq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hM hq
  haveI : NeZero n := ⟨hn0⟩
  have hkill : (zmultiplesHom (ZMod M) (q : ZMod M)) (n : ℤ) = 0 := by
    show (n : ℤ) • (q : ZMod M) = 0
    rw [zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ← hq, ZMod.natCast_self]
  let g : ZMod n →+ ZMod M := ZMod.lift n ⟨zmultiplesHom (ZMod M) (q : ZMod M), hkill⟩
  have hg : ∀ z : ℤ, g (z : ZMod n) = ((z * q : ℤ) : ZMod M) := by
    intro z
    rw [show g (z : ZMod n) = (zmultiplesHom (ZMod M) (q : ZMod M)) z from ZMod.lift_coe n _ z]
    show z • (q : ZMod M) = _
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  refine ⟨g, ?_, ?_⟩
  · intro x₁ x₂ h
    obtain ⟨z₁, rfl⟩ := ZMod.intCast_surjective x₁
    obtain ⟨z₂, rfl⟩ := ZMod.intCast_surjective x₂
    rw [hg, hg] at h
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    rw [← sub_mul, hq, Nat.cast_mul] at h
    exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0) h
  · intro y
    constructor
    · intro hy
      obtain ⟨w, rfl⟩ := ZMod.intCast_surjective y
      have : ((n * w : ℤ) : ZMod M) = 0 := by
        rw [Int.cast_mul, Int.cast_natCast, ← nsmul_eq_mul]; exact hy
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hq, Nat.cast_mul] at this
      obtain ⟨v, hv⟩ := Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hn0) this
      refine ⟨(v : ZMod n), ?_⟩
      rw [hg, mul_comm, ← hv]
    · rintro ⟨x, rfl⟩
      rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

def torsionSub (n : ℕ) (D : Type*) [AddCommGroup D] : AddSubgroup D where
  carrier := {y | n • y = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, nsmul_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_nsmul, ha, neg_zero]

theorem mem_torsionSub {n : ℕ} {D : Type*} [AddCommGroup D] (y : D) : y ∈ torsionSub n D ↔ n • y = 0 := Iff.rfl

noncomputable def homZModEquivTorsion (n : ℕ) (D : Type*) [AddCommGroup D] :
    (ZMod n →+ D) ≃+ torsionSub n D where
  toFun f := ⟨f 1, by rw [mem_torsionSub, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero]⟩
  invFun y := ZMod.lift n ⟨zmultiplesHom D y.1, by
    show (n : ℤ) • y.1 = 0
    rw [natCast_zsmul]; exact y.2⟩
  left_inv f := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [ZMod.lift_coe]
    show z • f 1 = f z
    rw [← map_zsmul, zsmul_eq_mul, mul_one]
  right_inv y := by
    apply Subtype.ext
    dsimp only
    rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) from Int.cast_one.symm, ZMod.lift_coe]
    simp
  map_add' f f' := by
    apply Subtype.ext; rfl

theorem nonempty_addEquiv_hom_zmod_zmod {d n : ℕ} [NeZero d] (hn : n ∣ d) :
    Nonempty ((ZMod n →+ ZMod d) ≃+ ZMod n) := by
  obtain ⟨g, hinj, hrange⟩ := exists_addMonoidHom_injective_forall_nsmul_eq_zero_iff (M := d) hn

  have hTR : torsionSub n (ZMod d) = g.range := by
    ext y
    rw [mem_torsionSub, AddMonoidHom.mem_range, hrange]
    constructor <;> (rintro ⟨x, hx⟩; exact ⟨x, hx⟩)
  exact ⟨(homZModEquivTorsion n (ZMod d)).trans ((AddEquiv.addSubgroupCongr hTR).trans (AddMonoidHom.ofInjective hinj).symm)⟩

theorem nonempty_addEquiv_addMonoidHom_zmod (L : Type u) [AddCommGroup L] [Finite L] {d : ℕ} [NeZero d]
    (hd : ∀ x : L, d • x = 0) : Nonempty ((L →+ ZMod d) ≃+ L) := by
  classical
  obtain ⟨ι, hι, nn, hnn, ⟨eL⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' L

  let eP : L ≃ₗ[ℤ] ((i : ι) → ZMod (nn i)) :=
    eL.toIntLinearEquiv.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (nn i)))

  have hdiv : ∀ i, nn i ∣ d := by
    intro i
    haveI : NeZero (nn i) := ⟨by have := hnn i; omega⟩
    have h1 : d • eP.symm (Pi.single i (1 : ZMod (nn i))) = 0 := hd _
    have h2 : d • (Pi.single i (1 : ZMod (nn i)) : (j : ι) → ZMod (nn j)) = 0 := by
      have := congrArg eP h1
      rwa [map_nsmul, LinearEquiv.apply_symm_apply, map_zero] at this
    have h3 := congrFun h2 i
    rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at h3
    exact (ZMod.natCast_eq_zero_iff d (nn i)).mp h3

  have hcomp : ∀ i, Nonempty ((ZMod (nn i) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ZMod (nn i)) := fun i => by
    obtain ⟨e⟩ := nonempty_addEquiv_hom_zmod_zmod (d := d) (hdiv i)
    exact ⟨((addMonoidHomLequivInt (A := ZMod (nn i)) (B := ZMod d) ℤ).symm.trans e.toIntLinearEquiv)⟩
  have ec : ∀ i, (ZMod (nn i) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ZMod (nn i) := fun i => (hcomp i).some

  let E1 : (L →+ ZMod d) ≃ₗ[ℤ] (L →ₗ[ℤ] ZMod d) := addMonoidHomLequivInt ℤ
  let E2 : (L →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] (((i : ι) → ZMod (nn i)) →ₗ[ℤ] ZMod d) := LinearEquiv.congrLeft (ZMod d) ℤ eP
  let E3 : (((i : ι) → ZMod (nn i)) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ((i : ι) → (ZMod (nn i) →ₗ[ℤ] ZMod d)) :=
    (LinearMap.lsum ℤ (fun i => ZMod (nn i)) ℤ).symm
  let E4 : ((i : ι) → (ZMod (nn i) →ₗ[ℤ] ZMod d)) ≃ₗ[ℤ] ((i : ι) → ZMod (nn i)) := LinearEquiv.piCongrRight ec
  exact ⟨(E1.trans (E2.trans (E3.trans (E4.trans eP.symm)))).toAddEquiv⟩

end PoleB1

theorem solution
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L) := by
  exact PoleB1.nonempty_addEquiv_addMonoidHom_zmod L hd

end S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
end P2MW
export P2MW.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero (solution)
