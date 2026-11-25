-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:22.030155+00:00
-- url     : https://prove2.me/theorems/f46b7f47-3619-4118-a331-227853d1d603
-- title:
--   POrbit Chart Quot
-- statement:
--   Definitions and structural lemmas for POrbit Chart Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartQuot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι] in

theorem val_chartEval_eq_aeval_div (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : chartRing x c) : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]
    simp [chartEval, chartRatio]
omit [Fintype ι] [DecidableEq ι] in

theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨a, ha⟩
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, Subtype.ext ?_⟩
  have h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
    MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]
  exact AlgHom.congr_fun h f
omit [Fintype ι] [DecidableEq ι] in

theorem mem_ker_chartEval_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ RingHom.ker (chartEval x c) ↔ aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0 := by
  rw [RingHom.mem_ker, ← val_chartEval_eq_aeval_div]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)
theorem aeval_blockScale_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (t : ι → Ω) (w : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    aeval (fun p ↦ t p.1 * w p) g = (∏ k, t k ^ m k) * aeval w g := by
  have h : algebraMap ℤ Ω = Int.castRingHom Ω := Subsingleton.elim _ _
  rw [aeval_def, aeval_def, h]
  exact eval₂_scale_of_isWeightedHomogeneous t w hg
theorem ker_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    RingHom.ker (chartEval x c) = orbitIdeal x ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
  set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ
  set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz
  apply le_antisymm
  · intro f hf
    rw [mem_ker_chartEval_iff] at hf
    set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN
    have hle : ∀ m ∈ compDegs f, m ≤ N := fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm
    set F := ∑ m ∈ compDegs f,
      weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF
    have hFJ : f - F ∈ J := by
      have h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1 := by
        intro d
        rw [chartMonomial, map_prod]
        refine Finset.prod_eq_one fun k _ ↦ ?_
        have hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨k, rfl⟩
        rw [map_pow, hk, one_pow]
      rw [← Ideal.Quotient.eq, hF, map_sum]
      simp only [map_mul, h1, mul_one]
      conv_lhs => rw [← sum_compDegs f]
      rw [map_sum]
    have hFP : F ∈ orbitIdeal x := by
      have hhom : IsWeightedHomogeneous (coordDeg n) F N := by
        have : F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N := by
          refine Submodule.sum_mem _ fun m hm ↦ ?_
          have h2 := (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
            (isWeightedHomogeneous_chartMonomial c (N - m))
          rwa [add_tsub_cancel_of_le (hle m hm)] at h2
        exact this
      rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]
      have hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p := by
        funext p
        simp only [hz, flatCone]
        rw [mul_div_cancel₀ _ (hc p.1)]
      have hterm : ∀ m ∈ compDegs f,
          aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) =
            (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f) := by
        intro m hm
        have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z
          (weightedHomogeneousComponent_isWeightedHomogeneous m f)
        have hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k) := by
          simp [chartMonomial, map_prod, flatCone]
        have hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Nat.add_sub_cancel' (hle m hm k)]
        rw [map_mul, hmon, hpow]
        rw [hy]
        rw [hs]
        ring
      rw [hF, map_sum]
      refine (Finset.sum_congr rfl hterm).trans ?_
      rw [← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]
    have : f = F + (f - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)
  · refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [mem_ker_chartEval_iff]
      rw [orbitIdeal, mem_mCoordIdeal_iff] at hf
      rw [← sum_compDegs f, map_sum]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x)
        (weightedHomogeneousComponent_isWeightedHomogeneous m f)
      have hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) =
          fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p := by
        funext p
        rw [div_eq_inv_mul]
        rfl
      rw [hz', hs]
      refine mul_eq_zero_of_right _ ?_
      have h0 := hf m
      rw [aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)] at h0 ⊢
      exact h0
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, mem_ker_chartEval_iff]
      simp [div_self (hc k)]
theorem OrbitChartQuot.proof : OrbitChartQuot.Statement := by
  intro ι _ _ n x c hc V hV
  have hsurj := chartEval_surjective x c
  let g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V :=
    (Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hsurj
  have hker : RingHom.ker g =
      V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
    ext f
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint,
      Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc,
      ← sup_assoc, sup_eq_left.mpr hV]
  exact ⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩
example : Nonempty ((chartRing samplePoint (fun _ ↦ 0) ⧸
      chartPoint samplePoint (fun _ ↦ 0) (orbitIdeal samplePoint)) ≃+*
    (MvPolynomial (Coord (fun _ : Unit ↦ 1)) ℤ ⧸ (orbitIdeal samplePoint ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, 0⟩ : MvPolynomial (Coord (fun _ : Unit ↦ 1)) ℤ) - 1)))) :=
  OrbitChartQuot.proof Unit _ samplePoint _ (fun _ ↦ by simp [samplePoint]) _ le_rfl
end
end GroundTheory.Heights₂.Heights


