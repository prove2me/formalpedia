-- Prove2me | solution 1 for AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fe614c67-9825-520e-bef0-4b1567a53759

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero
import Theorems.Thm_IsLocalRing_hensel_lift_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero

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
    {K F : Type*} [Field K] [Field F] [Algebra K F] {L : Type*} [Field L] (ι : K →+* L)
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (Y : PowerSeries L) (hY0 : PowerSeries.constantCoeff Y = ι (v.evalAt y))
    (hY : (G.map (Polynomial.mapRingHom (PowerSeries.C.comp ι))).evalEval
        (PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X) Y = 0) :
    Y = PowerSeries.map ι
          (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) := by
  set a : PowerSeries L := PowerSeries.map ι
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) with ha
  set x : PowerSeries L := PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X with hx
  set p : Polynomial (Polynomial (PowerSeries L)) := G.map (Polynomial.mapRingHom (PowerSeries.C.comp ι))
    with hp

  set f : Polynomial (PowerSeries L) := p.map (Polynomial.evalRingHom x) with hf
  have hfeval : ∀ b, f.eval b = p.evalEval x b := fun b => Polynomial.map_evalRingHom_eval x b p

  have hK := evalEval_C_add_X_mk_taylorCoeff_eq_zero v hv hz hy ht G hG
  have ha_root : f.IsRoot a := by
    rw [Polynomial.IsRoot, hfeval]
    have := congrArg (PowerSeries.map ι) hK
    rw [map_zero, ← Polynomial.map_mapRingHom_evalEval, Polynomial.map_map, Polynomial.mapRingHom_comp]
      at this
    have hcomp : (PowerSeries.map ι).comp (algebraMap K (PowerSeries K)) = PowerSeries.C.comp ι := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, ← PowerSeries.C_eq_algebraMap, PowerSeries.map_C]
    rw [hcomp, map_add, PowerSeries.map_C, PowerSeries.map_X] at this
    exact this

  have hb_root : f.IsRoot Y := by rw [Polynomial.IsRoot, hfeval]; exact hY

  have ha0 : PowerSeries.constantCoeff a = ι (v.evalAt y) := by
    rw [ha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, taylorCoeff_zero]
  have hmem : Y - a ∈ IsLocalRing.maximalIdeal (PowerSeries L) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, map_sub, hY0, ha0, sub_self]

  have hunit : IsUnit (f.derivative.eval a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    rw [hf, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval, hp, Polynomial.derivative_map,
      ← Polynomial.map_mapRingHom_evalEval PowerSeries.constantCoeff, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
    have hcc : PowerSeries.constantCoeff.comp (PowerSeries.C.comp ι) = ι := by
      refine RingHom.ext fun c => ?_
      simp [PowerSeries.constantCoeff_C]
    rw [hcc, hx, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero, ha0,
      Polynomial.map_mapRingHom_evalEval ι, _root_.map_ne_zero ι]
    exact hsep
  exact (IsLocalRing.hensel_lift_unique ha_root hb_root hmem hunit).symm

end S_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero (solution)
