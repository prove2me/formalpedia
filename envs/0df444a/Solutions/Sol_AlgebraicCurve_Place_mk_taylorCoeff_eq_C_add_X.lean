-- Prove2me | solution 1 for AlgebraicCurve.Place.mk_taylorCoeff_eq_C_add_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0b130989-0a20-5ac3-a74d-e77ff4d29abe

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace P2MG2
open AlgebraicCurve AlgebraicCurve.Place Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem taylorRem_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorRem v t 0 r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [taylorRem_succ, ih, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq, map_zero,
      sub_self, zero_mul]

theorem taylorCoeff_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorCoeff v t r 0 = 0 := by
  rw [taylorCoeff_eq, taylorRem_zero_fun, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]

theorem taylorRem_algebraMap_one (v : Place K F) (t : F) (c : K) :
    taylorRem v t (algebraMap K F c) 1 = 0 := by
  show (taylorRem v t (algebraMap K F c) 0 - _) * t⁻¹ = 0
  rw [taylorRem_zero, v.evalAt_algebraMap_eq, sub_self, zero_mul]

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {g : F} (hg0 : g ≠ 0) (hpos : 0 < v.ord g) :
    v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hg0 hpos.le
  have hnu : ¬ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    change v.ord g = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by simpa [mem_nonunits_iff] using hnu)
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end P2MG2

open P2MG2 in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z : F} (hz : z ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1) :
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n z)
      = PowerSeries.C (v.evalAt z) + PowerSeries.X := by
  set t : F := z - algebraMap K F (v.evalAt z) with htdef
  have ht0 : t ≠ 0 := by rintro h; rw [h] at ht; simp [Place.ord_zero] at ht
  have h1 : taylorRem v t z 1 = 1 := by
    show (taylorRem v t z 0 - _) * t⁻¹ = 1
    rw [taylorRem_zero, ← htdef, mul_inv_cancel₀ ht0]
  ext n
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  rcases n with _ | n
  · simp [taylorCoeff_zero]
  · rw [taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, h1, ← map_one (algebraMap K F),
      taylorCoeff_algebraMap]
    rcases n with _ | n
    · simp
    · rw [if_neg (Nat.succ_ne_zero _), if_neg (Nat.succ_ne_zero _), if_neg (by omega), add_zero]

end S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X
end P2MW
export P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X (solution)
