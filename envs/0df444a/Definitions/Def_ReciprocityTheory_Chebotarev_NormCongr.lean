-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
-- name    : ReciprocityTheory_Chebotarev_NormCongr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:04.079943+00:00
-- url     : https://prove2.me/theorems/f53fa380-0a3c-4bc6-b4b0-3d42f7c2c679
-- title:
--   Norm Congr
-- statement:
--   Definitions and structural lemmas for Norm Congr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormCongr.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Cheb
open Module
theorem norm_modEq_of_sub_mem_span {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (m : ℤ) {α α' : S} (h : α - α' ∈ Ideal.span {(m : S)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := by
  classical
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp h
  have hα : α = α' + algebraMap ℤ S m * β := by
    rw [algebraMap_int_eq, eq_intCast, mul_comm, hβ]; ring
  rw [Int.modEq_iff_dvd, ← Int.natAbs_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  symm
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hα, map_add, map_mul,
    AlgHom.commutes]
  have key : ∀ M : Matrix (Module.Free.ChooseBasisIndex ℤ S) (Module.Free.ChooseBasisIndex ℤ S) ℤ,
      ((Int.castRingHom (ZMod m.natAbs)) M.det : ZMod m.natAbs) = ((Int.castRingHom (ZMod m.natAbs)).mapMatrix M).det :=
    fun M => RingHom.map_det _ M
  simp only [eq_intCast] at key
  rw [key, key]
  congr 1
  have h0 : ((m : ZMod m.natAbs)) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 0 m m.natAbs).mpr (by simp)
    simpa using this.symm
  have hM : (Int.castRingHom (ZMod m.natAbs)).mapMatrix
      ((algebraMap ℤ (Matrix (Free.ChooseBasisIndex ℤ S) (Free.ChooseBasisIndex ℤ S) ℤ)) m) = 0 := by
    rw [eq_intCast, map_intCast]
    ext i j
    by_cases hij : i = j <;> simp [hij, h0, Matrix.diagonal, ← Matrix.diagonal_intCast']
  rw [map_add, map_mul, hM, zero_mul, add_zero]
theorem absNorm_dvd_algebraNorm {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] {b : Ideal S} {α : S} (h : α ∈ b) :
    (Ideal.absNorm b : ℤ) ∣ Algebra.norm ℤ α :=
  Ideal.absNorm_dvd_norm_of_mem h
theorem norm_div_absNorm_modEq {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (l : ℤ) {b : Ideal S} {α α' : S} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : S)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] := by
  have hm := norm_modEq_of_sub_mem_span _ h
  obtain ⟨a, ha⟩ := absNorm_dvd_algebraNorm hα
  obtain ⟨c, hc⟩ := absNorm_dvd_algebraNorm hα'
  rw [ha, hc] at hm ⊢
  by_cases hN : (Ideal.absNorm b : ℤ) = 0
  · rw [hN, Int.ediv_zero, Int.ediv_zero]
  rw [Int.mul_ediv_cancel_left _ hN, Int.mul_ediv_cancel_left _ hN]
  rw [mul_comm l] at hm
  exact Int.ModEq.mul_left_cancel' hN hm
example {E : Type*} [Field E] [NumberField E] (m : ℤ) {α α' : NumberField.RingOfIntegers E}
    (h : α - α' ∈ Ideal.span {(m : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := norm_modEq_of_sub_mem_span m h
example {E : Type*} [Field E] [NumberField E] (l : ℤ) {b : Ideal (NumberField.RingOfIntegers E)}
    {α α' : NumberField.RingOfIntegers E} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] :=
  norm_div_absNorm_modEq l hα hα' h
end ReciprocityTheory.Cheb


