-- Prove2me | solution 1 for AlgebraicCurve.Place.mk_taylorCoeff_evalEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e9ce2664-b1b0-58d0-ac03-07d06ae69268

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval

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
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K)) :
    (PowerSeries.mk fun n =>
        taylorCoeff v t n ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y))
      = (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.mk fun n => taylorCoeff v t n z) (PowerSeries.mk fun n => taylorCoeff v t n y) := by

  let O := v.toValuationSubring
  let φ : O →+* PowerSeries K :=
    { toFun := fun f => PowerSeries.mk fun n => taylorCoeff v t n (f : F)
      map_one' := by
        ext n
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, OneMemClass.coe_one, ← map_one (algebraMap K F),
          taylorCoeff_algebraMap]
      map_mul' := fun f g => by
        ext n
        rw [PowerSeries.coeff_mk, MulMemClass.coe_mul, PowerSeries.coeff_mul,
          taylorCoeff_mul v hv ht f.2 g.2 n]
        simp only [PowerSeries.coeff_mk]
      map_zero' := by
        ext n
        rw [PowerSeries.coeff_mk, ZeroMemClass.coe_zero, taylorCoeff_zero_fun, map_zero]
      map_add' := fun f g => by
        ext n
        rw [PowerSeries.coeff_mk, AddMemClass.coe_add, taylorCoeff_add v hv ht f.2 g.2 n, map_add,
          PowerSeries.coeff_mk, PowerSeries.coeff_mk] }
  have hφ : ∀ f : O, φ f = PowerSeries.mk fun n => taylorCoeff v t n (f : F) := fun _ => rfl

  have hφC : φ.comp (algebraMap K O) = algebraMap K (PowerSeries K) := by
    refine RingHom.ext fun c => ?_
    ext n
    rw [RingHom.comp_apply, hφ, PowerSeries.coeff_mk, Place.coe_algebraMap,
      taylorCoeff_algebraMap, ← PowerSeries.C_eq_algebraMap, PowerSeries.coeff_C]

  have hOF : (algebraMap O F).comp (algebraMap K O) = algebraMap K F := (IsScalarTower.algebraMap_eq K O F).symm
  have hsub : ∀ f : O, algebraMap O F f = (f : F) := fun _ => rfl
  have hA : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y
      = (((G.map (Polynomial.mapRingHom (algebraMap K O))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ : O) : F) := by
    rw [← hsub, ← Polynomial.map_mapRingHom_evalEval (algebraMap O F), Polynomial.map_map,
      Polynomial.mapRingHom_comp, hOF]
    rfl
  rw [hA, ← hφ, ← Polynomial.map_mapRingHom_evalEval φ, Polynomial.map_map, Polynomial.mapRingHom_comp, hφC]
  rfl

end S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval
end P2MW
export P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval (solution)
