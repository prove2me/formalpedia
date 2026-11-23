-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:36.790138+00:00
-- url     : https://prove2.me/theorems/8c9008d2-5f53-4bea-bc01-6f49012ea05d
-- title:
--   Laurent
-- statement:
--   Definitions and structural lemmas for Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
theorem dL_coeff (f : LaurentSeries R) (n : ℤ) :
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1) := by
  show (LaurentSeries.hasseDeriv R 1 f).coeff n = _
  rw [LaurentSeries.hasseDeriv_coeff]
  simp [Ring.choose_one_right, zsmul_eq_mul]
theorem uPow_mul_coeff (m n : ℤ) (f : LaurentSeries R) :
    (uPow m * f).coeff n = f.coeff (n - m) := by
  first
    | (have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)
    | (have h := HahnSeries.single_mul_coeff_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)
theorem C_mul_coeff (r : R) (f : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C r * f).coeff n = r * f.coeff n := by
  rw [HahnSeries.C_mul_eq_smul]
  first | rw [HahnSeries.coeff_smul, smul_eq_mul] | rw [HahnSeries.smul_coeff, smul_eq_mul] | simp
theorem toL_coeff_nat (f : R⟦X⟧) (n : ℕ) : (toL f).coeff (n : ℤ) = coeff n f := by
  exact HahnSeries.ofPowerSeries_apply_coeff f n
theorem toL_coeff_neg (f : R⟦X⟧) {n : ℤ} (hn : n < 0) : (toL f).coeff n = 0 := by
  first
    | (rw [PowerSeries.coeff_coe, if_pos hn])
    | (simp only [toL, HahnSeries.ofPowerSeries_apply]
       rw [HahnSeries.embDomain_notin_range]
       rintro ⟨k, hk⟩
       simp at hk
       omega)
theorem uPow_zero : (uPow 0 : LaurentSeries R) = 1 := rfl
theorem uPow_add (m n : ℤ) : (uPow (m + n) : LaurentSeries R) = uPow m * uPow n := by
  show HahnSeries.single (m + n) (1 : R) = HahnSeries.single m 1 * HahnSeries.single n 1
  rw [HahnSeries.single_mul_single, mul_one]
theorem uPow_mul_neg (n : ℤ) : (uPow n : LaurentSeries R) * uPow (-n) = 1 := by
  rw [← uPow_add]
  first | rw [add_neg_cancel] | rw [add_neg_self] | rw [add_right_neg]
  exact uPow_zero
theorem toL_C (r : R) : toL (C r) = (HahnSeries.C r : LaurentSeries R) := by
  first
    | exact HahnSeries.ofPowerSeries_C r
    | simp [toL]
theorem exists_uPow_mul_toL (f : LaurentSeries R) :
    ∃ (m : ℤ) (F : R⟦X⟧), f = uPow m * toL F := by
  refine ⟨f.order, f.powerSeriesPart, ?_⟩
  first
    | exact (LaurentSeries.single_order_mul_powerSeriesPart f).symm
    | (show f = uPow f.order * HahnSeries.ofPowerSeries ℤ R f.powerSeriesPart
       rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
       change f = uPow f.order * (uPow (-f.order) * f)
       rw [← mul_assoc, uPow_mul_neg, one_mul])
theorem dL_uPow_mul (m : ℤ) (f : LaurentSeries R) :
    dL (uPow m * f) = uPow m * dL f + HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f := by
  rw [show HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f
      = HahnSeries.C ((m : ℤ) : R) * (uPow (m - 1) * f) from mul_assoc _ _ _]
  ext n
  first | rw [HahnSeries.add_coeff] | rw [HahnSeries.coeff_add] | rw [HahnSeries.add_coeff']
  rw [dL_coeff, uPow_mul_coeff, uPow_mul_coeff, dL_coeff, C_mul_coeff, uPow_mul_coeff]
  have h1 : n + 1 - m = n - m + 1 := by ring
  have h2 : n - (m - 1) = n - m + 1 := by ring
  rw [h1, h2]
  push_cast
  ring
theorem dL_toL (f : R⟦X⟧) : dL (toL f) = toL (derivative R f) := by
  ext n
  rw [dL_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [toL_coeff_neg _ hn]
    rcases lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h
    · rw [toL_coeff_neg _ h, mul_zero]
    · rw [h]
      simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hk, toL_coeff_nat, toL_coeff_nat, PowerSeries.coeff_derivative]
    push_cast
    ring
theorem dL_mul (f g : LaurentSeries R) : dL (f * g) = f * dL g + g * dL f := by
  obtain ⟨m, F, rfl⟩ := exists_uPow_mul_toL f
  obtain ⟨k, G, rfl⟩ := exists_uPow_mul_toL g
  have e : uPow m * toL F * (uPow k * toL G) = uPow (m + k) * toL (F * G) := by
    rw [uPow_add, map_mul]; ring
  have h0 : (uPow (m + k) : LaurentSeries R) = uPow m * uPow k := uPow_add m k
  have h1 : (uPow (m + k - 1) : LaurentSeries R) = uPow (m - 1) * uPow k := by
    rw [← uPow_add]; congr 1; ring
  have h2 : (uPow (m + k - 1) : LaurentSeries R) = uPow m * uPow (k - 1) := by
    rw [← uPow_add]; congr 1; ring
  have h3 : (HahnSeries.C (((m + k : ℤ)) : R) : LaurentSeries R)
      = HahnSeries.C ((m : ℤ) : R) + HahnSeries.C ((k : ℤ) : R) := by
    rw [Int.cast_add, map_add]
  rw [e, dL_uPow_mul, dL_toL, Derivation.leibniz]
  simp only [dL_uPow_mul, dL_toL, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  linear_combination (toL F * toL (derivative R G) + toL G * toL (derivative R F)) * h0
    + (toL F * toL G * uPow (m + k - 1)) * h3
    + (HahnSeries.C ((m : ℤ) : R) * toL F * toL G) * h1
    + (HahnSeries.C ((k : ℤ) : R) * toL F * toL G) * h2
theorem dL_C (r : R) : dL (HahnSeries.C r : LaurentSeries R) = 0 := by
  rw [← toL_C, dL_toL]
  first | rw [PowerSeries.derivative_C, map_zero] | simp
def derivationOfLeibniz {k A M : Type*} [CommSemiring k] [CommSemiring A] [AddCommGroup M]
    [Algebra k A] [Module A M] [Module k M] (D : A → M)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hsmul : ∀ (r : k) (a : A), D (r • a) = r • D a)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation k A M :=
  Derivation.mk' { toFun := D, map_add' := hadd, map_smul' := hsmul } hmul
def dLDR (R : Type u) [CommRing R] : Derivation R (LaurentSeries R) (LaurentSeries R) :=
  derivationOfLeibniz (fun f => dL f) (fun a b => map_add dL a b)
    (fun r f => by
      rw [Algebra.smul_def, HahnSeries.algebraMap_apply', ← HahnSeries.C_mul_eq_smul]
      change dL (toL (C r) * f) = _
      rw [toL_C, dL_mul, dL_C, mul_zero, add_zero])
    (fun f g => by rw [smul_eq_mul, smul_eq_mul, dL_mul])
def dLD (R : Type u) [CommRing R] : Derivation ℤ (LaurentSeries R) (LaurentSeries R) :=
  derivationOfLeibniz (fun f => dL f) (fun a b => map_add dL a b)
    (fun r f => by
      rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul, dL_mul,
        ← map_intCast (HahnSeries.C : R →+* LaurentSeries R), dL_C, mul_zero, add_zero])
    (fun f g => by rw [smul_eq_mul, smul_eq_mul, dL_mul])
end Formalism.L2.Th1.A


