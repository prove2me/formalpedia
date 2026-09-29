-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ed1cc094-bad7-5bb1-a687-6f81518a0b82

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr

set_option autoImplicit false

open Polynomial AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

open Algebra Polynomial Matrix

namespace W4R

open AlgebraicCurve.TwoChartIntegralModel

section clone
variable {A : Type u} [CommRing A] {K : Type u} [Field K] {L : Type u} [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

theorem discr_smul_coord_mem_bot [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hcl : ∀ x : K, IsIntegral A x → x ∈ (⊥ : Subalgebra A K))
    {B : PowerBasis K L} (hint : IsIntegral A B.gen) {z : L} (hz : IsIntegral A z) (i : Fin B.dim) :
    discr K B.basis • (B.basis.equivFun z i) ∈ (⊥ : Subalgebra A K) := by
  classical
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  rw [← H, ← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec,
    one_mulVec] at cramer
  rw [discr_def, ← Pi.smul_apply, ← congr_fun cramer i, cramer_apply, det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact hcl _ (isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact hcl _ (isIntegral_trace <| (hint.pow _).mul (hint.pow _))

end clone

theorem mem_bot_of_isIntegral_chartAlg (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (S : Set F)
    (x : F) (hx : IsIntegral (chartAlg R F S) x) : x ∈ (⊥ : Subalgebra (chartAlg R F S) F) := by
  letI : Algebra (Algebra.adjoin R S) (chartAlg R F S) := (Subalgebra.inclusion (adjoin_le_chartAlg R F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin R S) (chartAlg R F S) F := IsScalarTower.of_algebraMap_eq (fun y => rfl)
  haveI : Algebra.IsIntegral (Algebra.adjoin R S) (chartAlg R F S) := ⟨fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin R S) (chartAlg R F S) F) Subtype.val_injective).mp y.2⟩
  have : IsIntegral (Algebra.adjoin R S) x := isIntegral_trans x hx
  exact ⟨⟨x, this⟩, rfl⟩

end W4R

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (F' : Type u) [Field F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (B : PowerBasis F F') (hgen : IsIntegral R B.gen)
    (hdisc : ∃ d : Rˣ, algebraMap R F (d : R) = Algebra.discr F (fun i : Fin B.dim => B.gen ^ (i : ℕ)))
    (S : Set F) :
    (∀ x : F', x ∈ chartAlg R F' (algebraMap F F' '' S) ↔
        ∃ b : Fin B.dim → ↥(chartAlg R F S), x = ∑ i, algebraMap F F' (b i : F) * B.gen ^ (i : ℕ)) ∧
    (∀ b b' : Fin B.dim → ↥(chartAlg R F S),
        (∑ i, algebraMap F F' (b i : F) * B.gen ^ (i : ℕ)) = ∑ i, algebraMap F F' (b' i : F) * B.gen ^ (i : ℕ) → b = b') := by
  classical
  obtain ⟨d, hd⟩ := hdisc
  have hdisc' : algebraMap R F (d : R) = Algebra.discr F B.basis := by rw [hd, PowerBasis.coe_basis]

  have hsum : ∀ c : Fin B.dim → F, (∑ i, algebraMap F F' (c i) * B.gen ^ (i : ℕ)) = ∑ i, c i • B.basis i := by
    intro c; refine Finset.sum_congr rfl fun i _ => ?_; rw [Algebra.smul_def, PowerBasis.coe_basis]

  have hmapS : ∀ y : F, y ∈ chartAlg R F S → algebraMap F F' y ∈ chartAlg R F' (algebraMap F F' '' S) := by
    intro y hy
    rw [mem_chartAlg_iff] at hy ⊢
    have hle : (Algebra.adjoin R S).map (IsScalarTower.toAlgHom R F F') ≤ Algebra.adjoin R (algebraMap F F' '' S) := by
      rw [AlgHom.map_adjoin]; rfl
    have h1 : IsIntegral ((Algebra.adjoin R S).map (IsScalarTower.toAlgHom R F F')) (algebraMap F F' y) :=
      hy.map_of_comp_eq (((IsScalarTower.toAlgHom R F F').subalgebraMap (Algebra.adjoin R S)).toRingHom)
        (algebraMap F F') (by ext; rfl)
    exact h1.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F') (by ext; rfl)
  have hgen' : B.gen ∈ chartAlg R F' (algebraMap F F' '' S) := by
    rw [mem_chartAlg_iff]; exact hgen.tower_top
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, ?_⟩
  ·
    rw [mem_chartAlg_iff] at hx

    have hRS : Algebra.adjoin R (algebraMap F F' '' S) ≤ (chartAlg R F' (algebraMap F F' '' S)).restrictScalars R := by
      rw [Algebra.adjoin_le_iff]; intro y hy; exact subset_chartAlg R F' _ hy
    have hxB : IsIntegral (chartAlg R F S) x := by

      have hle : Algebra.adjoin R (algebraMap F F' '' S) ≤ (⊥ : Subalgebra (chartAlg R F S) F').restrictScalars R := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨s, hs, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, Algebra.mem_bot]
        exact ⟨⟨s, subset_chartAlg R F S hs⟩, (IsScalarTower.algebraMap_apply (chartAlg R F S) F F' _).symm⟩
      have h1 : IsIntegral ((⊥ : Subalgebra (chartAlg R F S) F').restrictScalars R) x :=
        hx.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F') (by ext; rfl)
      have h2 : IsIntegral (⊥ : Subalgebra (chartAlg R F S) F') x := h1
      haveI : Algebra.IsIntegral (chartAlg R F S) (⊥ : Subalgebra (chartAlg R F S) F') :=
        ⟨fun y => by
          obtain ⟨r, hr⟩ := Algebra.mem_bot.mp y.2
          have hy : IsIntegral (chartAlg R F S) ((⊥ : Subalgebra (chartAlg R F S) F').val y) := by
            show IsIntegral (chartAlg R F S) (y : F')
            rw [← hr]; exact isIntegral_algebraMap
          exact (isIntegral_algHom_iff (⊥ : Subalgebra (chartAlg R F S) F').val Subtype.val_injective).mp hy⟩
      haveI : IsScalarTower (chartAlg R F S) (⊥ : Subalgebra (chartAlg R F S) F') F' := IsScalarTower.subalgebra' _ _ _ _
      exact isIntegral_trans x h2
    have hgenB : IsIntegral (chartAlg R F S) B.gen := hgen.tower_top
    refine ⟨fun i => ⟨B.basis.equivFun x i, ?_⟩, ?_⟩
    · have hmem := W4R.discr_smul_coord_mem_bot (W4R.mem_bot_of_isIntegral_chartAlg R F S) hgenB hxB i
      rw [← hdisc', Algebra.mem_bot] at hmem
      obtain ⟨r, hr⟩ := hmem

      have : B.basis.equivFun x i = algebraMap R F ((d⁻¹ : Rˣ) : R) * (r : F) := by
        have e : (r : F) = algebraMap R F (d : R) * B.basis.equivFun x i := by
          have := hr; rw [smul_eq_mul] at this; exact this
        rw [e, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [this]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) r.2
    · rw [hsum]
      exact (B.basis.sum_equivFun x).symm
  ·
    rintro ⟨b, rfl⟩
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hmapS _ (b i).2) (Subalgebra.pow_mem _ hgen' _)
  ·
    intro b b' h
    rw [hsum, hsum] at h
    have hc : (fun i => (b i : F)) = fun i => (b' i : F) := by
      have := B.basis.repr_sum_self (fun i => (b i : F))
      have h' := B.basis.repr_sum_self (fun i => (b' i : F))
      rw [h] at this
      exact (this.symm.trans h')
    funext i; exact Subtype.ext (congr_fun hc i)

end S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr (solution)
