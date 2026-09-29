-- Prove2me | solution 1 for AlgebraicCurve.Place.taylorCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/80d10f1a-be8d-5c1d-967f-61c83db75614

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
import Theorems.Thm_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_taylorCoeff_mul

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

namespace P2MJetT6
open AlgebraicCurve AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem mem_of_ord_eq_one (v : Place K F) {t : F} (ht : v.ord t = 1) : t ∈ v.toValuationSubring := by
  have ht0 : t ≠ 0 := by rintro rfl; simp [Place.ord_zero] at ht
  exact v.mem_toValuationSubring_of_ord_nonneg_alt ht0 (by omega)

theorem evalAt_mul_eq_zero_of_ord_eq_one (v : Place K F) {t h : F}
    (ht : v.ord t = 1) (hh : h ∈ v.toValuationSubring) : v.evalAt (t * h) = 0 := by
  by_cases h0 : t * h = 0
  · rw [h0, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]
  have ht0 : t ≠ 0 := left_ne_zero_of_mul h0
  have hh0 : h ≠ 0 := right_ne_zero_of_mul h0
  have hmem : t * h ∈ v.toValuationSubring := mul_mem (mem_of_ord_eq_one v ht) hh
  have hpos : 0 < v.ord (t * h) := by
    rw [v.ord_mul ht0 hh0, ht]; have := ord_nonneg_of_mem v hh hh0; omega
  have hnu : ¬ IsUnit (⟨t * h, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    change v.ord (t * h) = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨t * h, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by simpa [mem_nonunits_iff] using hnu)
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem taylorRem_one (v : Place K F) (t f : F) :
    taylorRem v t f 1 = (f - algebraMap K F (v.evalAt f)) * t⁻¹ := rfl

end P2MJetT6

open P2MJetT6 in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f * g)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, taylorCoeff v t x.1 f * taylorCoeff v t x.2 g := by
  induction r generalizing f g with
  | zero =>
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, taylorCoeff_zero, taylorCoeff_zero,
      taylorCoeff_zero]
    exact v.evalAt_mul_of_mem hv hf hg
  | succ r ih =>
    have hf1 : taylorRem v t f 1 ∈ v.toValuationSubring := taylorRem_mem_toValuationSubring v hv ht hf 1
    have hg1 : taylorRem v t g 1 ∈ v.toValuationSubring := taylorRem_mem_toValuationSubring v hv ht hg 1
    have hrem : taylorRem v t (f * g) 1
        = f * taylorRem v t g 1 + (v.evalAt g) • taylorRem v t f 1 := by
      rw [taylorRem_one, taylorRem_one, taylorRem_one, v.evalAt_mul_of_mem hv hf hg, map_mul,
        Algebra.smul_def]
      ring
    have hsm : (v.evalAt g) • taylorRem v t f 1 ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hf1
    rw [taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, hrem,
      taylorCoeff_add v hv ht (mul_mem hf hg1) hsm r, taylorCoeff_smul v hv ht hf1 _ r,
      ih hf hg1, Finset.Nat.antidiagonal_succ', Finset.sum_cons, Finset.sum_map]
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
      Function.Embedding.coe_refl, id_eq, Nat.succ_eq_add_one,
      taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, taylorCoeff_zero]
    ring

end S_AlgebraicCurve_Place_taylorCoeff_mul
end P2MW
export P2MW.S_AlgebraicCurve_Place_taylorCoeff_mul (solution)
