-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8a0e0540-b26c-5327-984c-f57743890bac

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff fibre chartAlg_le_chartAlg"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open Polynomial
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
  (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]

theorem exists_mem_mul_mem_adjoin (M : Submonoid R) [IsLocalization M K] (S : Set F) {c : F} (hc : c ∈ Algebra.adjoin K S) :
    ∃ m : M, algebraMap R F m * c ∈ Algebra.adjoin R S := by
  induction hc using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, by rw [OneMemClass.coe_one, map_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap q =>
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.surj M q
    refine ⟨m, ?_⟩
    have : algebraMap R F m * algebraMap K F q = algebraMap R F r := by
      rw [IsScalarTower.algebraMap_apply R K F (m : R), IsScalarTower.algebraMap_apply R K F r, ← map_mul,
        mul_comm, h]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m * n, ?_⟩
    have : algebraMap R F ((m * n : M) : R) * (y + z) =
        algebraMap R F n * (algebraMap R F m * y) + algebraMap R F m * (algebraMap R F n * z) := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hm)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m * n, ?_⟩
    have : algebraMap R F ((m * n : M) : R) * (y * z) =
        (algebraMap R F m * y) * (algebraMap R F n * z) := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact Subalgebra.mul_mem _ hm hn

theorem exists_mem_mul_mem_chartAlg (M : Submonoid R) [IsLocalization M K] (S : Set F) {x : F} (hx : x ∈ chartAlg K F S) :
    ∃ m : M, algebraMap R F m * x ∈ chartAlg R F S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff K F).mp hx
  have hcoeff : ∀ i, ∃ m : M, algebraMap R F m * (p.coeff i : F) ∈ Algebra.adjoin R S :=
    fun i => exists_mem_mul_mem_adjoin R K F M S (p.coeff i).2
  choose n hn using hcoeff
  set Mp : M := ∏ i ∈ Finset.range (p.natDegree + 1), n i with hMp
  have hdvd : ∀ i ≤ p.natDegree, ∃ k : M, Mp = n i * k := fun i hi => by
    refine ⟨∏ j ∈ (Finset.range (p.natDegree + 1)).erase i, n j, ?_⟩
    rw [hMp, ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))]
  set c : F := algebraMap R F (Mp : R) with hc
  set q : F[X] := (p.map (algebraMap (Algebra.adjoin K S) F)).scaleRoots c with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (c * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin R S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · obtain ⟨k, hk⟩ := hdvd i hi.le
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hi
      have hdeg : p.natDegree - i = d + 1 := by omega
      have hck : c = algebraMap R F (n i) * algebraMap R F k := by
        rw [hc, hk, Submonoid.coe_mul, map_mul]
      rw [hdeg, pow_succ, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : F) * (c ^ d * c)
          = (c ^ d * algebraMap R F k) * (algebraMap R F (n i) * (p.coeff i : F)) by rw [hck]; ring]
      refine mul_mem (mul_mem (pow_mem ?_ d) (Subalgebra.algebraMap_mem _ _)) (hn i)
      rw [hc]; exact Subalgebra.algebraMap_mem _ _
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin R S) F) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨Mp, (mem_chartAlg_iff R F).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, ← hc, hqroot]

theorem exists_eq_mk'_one_tmul (M : Submonoid R) [IsLocalization M K] (S : Set F) (z : K ⊗[R] ↥(chartAlg R F S)) :
    ∃ (m : M) (a : chartAlg R F S), z = (IsLocalization.mk' K (1 : R) m) ⊗ₜ a := by
  have key : ∀ (m n : M) (a : chartAlg R F S),
      (IsLocalization.mk' K (1 : R) m) ⊗ₜ[R] a =
        (IsLocalization.mk' K (1 : R) (m * n)) ⊗ₜ[R] (((n : M) : R) • a) := by
    intro m n a
    rw [← TensorProduct.smul_tmul, IsLocalization.smul_mk']
    congr 1
    rw [IsLocalization.mk'_eq_iff_eq]
    simp only [mul_one, Submonoid.coe_mul]
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, by simp⟩
  | tmul q a =>
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M q
    refine ⟨m, r • a, ?_⟩
    rw [← TensorProduct.smul_tmul, IsLocalization.smul_mk', mul_one]
  | add y z hy hz =>
    obtain ⟨m, a, rfl⟩ := hy
    obtain ⟨n, b, rfl⟩ := hz
    refine ⟨m * n, ((n : M) : R) • a + ((m : M) : R) • b, ?_⟩
    rw [TensorProduct.tmul_add, ← key m n a, mul_comm m n, ← key n m b]

noncomputable def tensorToField (S : Set F) : K ⊗[R] ↥(chartAlg R F S) →ₐ[K] F :=
  Algebra.TensorProduct.lift (Algebra.ofId K F) ((chartAlg R F S).val) (fun _ _ => Commute.all _ _)

theorem tensorToField_tmul (S : Set F) (q : K) (a : chartAlg R F S) :
    tensorToField R K F S (q ⊗ₜ a) = q • (a : F) := by
  simp [tensorToField, Algebra.smul_def]

theorem tensorToField_injective (M : Submonoid R) [IsLocalization M K] (S : Set F) : Function.Injective (tensorToField R K F S) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨m, a, rfl⟩ := exists_eq_mk'_one_tmul R K F M S z
  rw [tensorToField_tmul, Algebra.smul_def, mul_eq_zero] at hz
  rcases hz with h | h
  · exfalso
    have h1 : algebraMap K F (IsLocalization.mk' K (1 : R) m) * algebraMap K F (algebraMap R K (m : R)) = 1 := by
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  · rw [show a = 0 from Subtype.ext h, TensorProduct.tmul_zero]

theorem range_tensorToField (M : Submonoid R) [IsLocalization M K] (S : Set F) : (tensorToField R K F S).range = chartAlg K F S := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨m, a, rfl⟩ := exists_eq_mk'_one_tmul R K F M S z
    change tensorToField R K F S _ ∈ _
    rw [tensorToField_tmul]
    exact Subalgebra.smul_mem _ (chartAlg_le_chartAlg R F K S a.2) _
  · intro x hx
    obtain ⟨m, hmx⟩ := exists_mem_mul_mem_chartAlg R K F M S hx
    refine ⟨(IsLocalization.mk' K (1 : R) m) ⊗ₜ ⟨algebraMap R F m * x, hmx⟩, ?_⟩
    change tensorToField R K F S _ = x
    rw [tensorToField_tmul]
    change IsLocalization.mk' K (1 : R) m • (algebraMap R F m * x) = x
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K F (m : R), ← mul_assoc, ← map_mul,
      IsLocalization.mk'_spec, map_one, map_one, one_mul]

theorem exists_algEquiv_tensor_chartAlg_impl (M : Submonoid R) [IsLocalization M K] (S : Set F) :
    ∃ e : K ⊗[R] ↥(chartAlg R F S) ≃ₐ[K] ↥(chartAlg K F S),
      ∀ (q : K) (b : ↥(chartAlg R F S)), ((e (q ⊗ₜ b) : ↥(chartAlg K F S)) : F) = q • (b : F) := by
  refine ⟨(AlgEquiv.ofInjective _ (tensorToField_injective R K F M S)).trans
    (Subalgebra.equivOfEq _ _ (range_tensorToField R K F M S)), fun q b => ?_⟩
  exact tensorToField_tmul R K F S q b

end AlgebraicCurve.TwoChartIntegralModel

end

open scoped TensorProduct in
open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg.AlgebraicCurve.TwoChartIntegralModel in
theorem solution.{u} (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
    (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
    (M : Submonoid R) [IsLocalization M K] (S : Set F) :
    ∃ e : K ⊗[R] ↥(chartAlg R F S) ≃ₐ[K] ↥(chartAlg K F S),
      ∀ (q : K) (b : ↥(chartAlg R F S)), ((e (q ⊗ₜ b) : ↥(chartAlg K F S)) : F) = q • (b : F) :=
  AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg_impl R K F M S

end S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg (solution)
