-- Prove2me | solution 1 for AsymptoticOperator.hasDiscreteEigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:51:57.547359+00:00
-- url     : https://prove2.me/submissions/e314fee2-b4bb-4c20-86cc-f2539ec90f71

import Theorems.Thm_AsymptoticOperator_compact_resolvent
import Theorems.Thm_AsymptoticOperator_isSymmetric
import Theorems.Thm_AsymptoticOperator_exists_not_eigenvalue_of_isFormalAdjoint
import Theorems.Thm_AsymptoticOperator_exists_hilbertBasis_eigenvectors_of_isCompactOperator
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Filter Topology ConleyZehnder AsymptoticOperator

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    HasDiscreteEigenbasis (asymptoticOperator S) := by
  set A := asymptoticOperator S with hA
  have hsym : A.IsFormalAdjoint A := isSymmetric S hS
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  haveI : SecondCountableTopology (L2 n) := Lp.SecondCountableTopology
  obtain ⟨μ, hμ⟩ := exists_not_eigenvalue_of_isFormalAdjoint A hsym
  have hker : eigenspace A μ = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply hμ f
    have h := LinearMap.mem_ker.mp hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      sub_eq_zero] at h
    exact h
  obtain ⟨R, hRc, hR1, -⟩ := compact_resolvent S hS μ hker
  choose hdom hRA using hR1
  have hRsym : (R : L2 n →ₗ[ℝ] L2 n).IsSymmetric := by
    intro g h
    simp only [ContinuousLinearMap.coe_coe]
    have h0 := hsym ⟨R g, hdom g⟩ ⟨R h, hdom h⟩
    conv_lhs => rw [← hRA h]
    conv_rhs => rw [← hRA g]
    rw [inner_sub_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right, h0]
  have hRinj : Function.Injective R := by
    intro g h hgh
    rw [← hRA g, ← hRA h]
    have he : (⟨R g, hdom g⟩ : A.domain) = ⟨R h, hdom h⟩ := Subtype.ext hgh
    rw [he, hgh]
  obtain ⟨ι, b, ν, hbν, hν0, hνt⟩ :=
    exists_hilbertBasis_eigenvectors_of_isCompactOperator R hRc hRsym hRinj
  refine ⟨ι, b, fun i => μ + (ν i)⁻¹, ?_, ?_⟩
  · intro i
    have hb : R ((ν i)⁻¹ • b i) = b i := by
      rw [map_smul, hbν i, smul_smul, inv_mul_cancel₀ (hν0 i), one_smul]
    have hbd : b i ∈ A.domain := hb ▸ hdom _
    refine ⟨hbd, ?_⟩
    have h1 := hRA ((ν i)⁻¹ • b i)
    have h2 : (⟨b i, hbd⟩ : A.domain) = ⟨R ((ν i)⁻¹ • b i), hdom _⟩ := Subtype.ext hb.symm
    rw [h2, add_smul]
    generalize A ⟨R ((ν i)⁻¹ • b i), hdom _⟩ = y at h1 ⊢
    rw [hb] at h1
    rw [← h1]
    abel
  · have habs : Tendsto (fun i => |ν i|) cofinite (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun i => abs_pos.mpr (hν0 i)⟩
      simpa [Function.comp_def] using (continuous_abs.tendsto 0).comp hνt
    have hinv : Tendsto (fun i => |ν i|⁻¹ + -|μ|) cofinite atTop :=
      (tendsto_inv_nhdsGT_zero.comp habs).atTop_add tendsto_const_nhds
    refine tendsto_atTop_mono (fun i => ?_) hinv
    have := abs_add_le (μ + (ν i)⁻¹) (-μ)
    simp only [add_neg_cancel_comm, abs_neg, abs_inv] at this
    linarith
