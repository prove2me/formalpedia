-- Prove2me | solution 1 for Auto.matCost_average_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:11:53.300937+00:00
-- url     : https://prove2.me/submissions/bc7fafbc-3ae5-4899-8b2d-0cf749c52ea5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_quadForm_mono
public import Theorems.Thm_Auto_matIntegral_apply
public import Theorems.Thm_Auto_ofReal_integral_le_lintegral
public import Theorems.Thm_Auto_re_trace_mul_matIntegral
public import Theorems.Thm_Auto_integrable_re_trace_mul
public import Theorems.Thm_Auto_matIntegral_posSemidef
public import Theorems.Thm_Auto_hsRe_eq_re_trace
public import Theorems.Thm_Auto_hsRe_mul_left_eq
public import Theorems.Thm_Auto_hsRe_mul_right_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
namespace Auto
theorem _root_.solution [IsProbabilityMeasure ν] {T K : Z → Matrix n n ℂ}
    (hTm : Measurable T) (hT : ∀ z, (T z).PosSemidef)
    (hTi : ∀ i j, Integrable (fun z => T z i j) ν)
    (hKi : ∀ i j, Integrable (fun z => K z i j) ν) :
    matCost (matIntegral ν T) (matIntegral ν K) ≤ ∫⁻ z, matCost (T z) (K z) ∂ν := by
  set S : Z → Matrix n n ℂ := fun z => CFC.sqrt (T z)
  have hSm : Measurable S := by
    have hc : Continuous (fun a : {a : Matrix n n ℂ // 0 ≤ a} => CFC.sqrt a.1) :=
      continuousOn_iff_continuous_domRestrict.1 CFC.continuousOn_sqrt
    exact hc.measurable.comp (hTm.subtype_mk (h := fun z => (hT z).nonneg))
  have hSH : ∀ z, (S z).IsHermitian := fun z => (CFC.sqrt_nonneg (T z)).posSemidef.1
  have hSS : ∀ z, S z * S z = T z := fun z => CFC.sqrt_mul_sqrt_self _ (hT z).nonneg
  have hSentry : ∀ i j, Measurable fun z => S z i j := fun i j =>
    (show Continuous (fun A : Matrix n n ℂ => A i j) from (continuous_apply j).comp (continuous_apply i)).measurable.comp hSm
  have htr : ∀ z, hsSq (S z) = ∑ k, (T z k k).re := by
    intro z
    rw [← re_trace_conjTranspose_mul_self, (hSH z).eq, hSS z, Matrix.trace, Complex.re_sum]
    rfl
  have hSi : ∀ i j, Integrable (fun z => S z i j) ν := by
    intro i j
    have hg : Integrable (fun z => 1 + ∑ k, (T z k k).re) ν := (integrable_const (1 : ℝ)).add
        (integrable_finsetSum Finset.univ fun k _ => (hTi k k).re)
    refine Integrable.mono' hg (hSentry i j).aestronglyMeasurable (Filter.Eventually.of_forall fun z
        => ?_)
    refine (norm_entry_le_sqrt_hsSq (S z) i j).trans ?_
    rw [htr z]
    have h0 : 0 ≤ ∑ k, (T z k k).re := by rw [← htr z]; exact hsSq_nonneg _
    exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  set A := matIntegral ν S
  have hA : A.PosSemidef := matIntegral_posSemidef (fun z => (CFC.sqrt_nonneg _).posSemidef) hSi
  have hmulA : ∀ (B : Z → Matrix n n ℂ), (∀ i j, Integrable (fun z => B z i j) ν) →
      ∀ (C : Matrix n n ℂ) i j, Integrable (fun z => (B z * C) i j) ν ∧
        Integrable (fun z => (C * B z) i j) ν ∧
        ∫ z, (B z * C) i j ∂ν = (matIntegral ν B * C) i j ∧
        ∫ z, (C * B z) i j ∂ν = (C * matIntegral ν B) i j := by
    intro B hB C i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hB i k).mul_const _
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hB k j).const_mul _
    · simp only [Matrix.mul_apply, matIntegral_apply]
      calc ∫ z, ∑ k, B z i k * C k j ∂ν = ∑ k, ∫ z, B z i k * C k j ∂ν :=
            integral_finsetSum _ fun k _ => (hB i k).mul_const _
        _ = _ := Finset.sum_congr rfl fun k _ => integral_mul_const _ _
    · simp only [Matrix.mul_apply, matIntegral_apply]
      calc ∫ z, ∑ k, C i k * B z k j ∂ν = ∑ k, ∫ z, C i k * B z k j ∂ν :=
            integral_finsetSum _ fun k _ => (hB k j).const_mul _
        _ = _ := Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hA2 : (matIntegral ν T - A * A).PosSemidef := by
    set M : Z → Matrix n n ℂ := fun z => (S z - A)ᴴ * (S z - A)
    have hMe : ∀ z, M z = T z - S z * A - A * S z + A * A := by
      intro z
      simp only [M, Matrix.conjTranspose_sub, (hSH z).eq, hA.1.eq, Matrix.sub_mul,
        Matrix.mul_sub, hSS z]
      abel
    have hMi : ∀ i j, Integrable (fun z => M z i j) ν := by
      intro i j
      simp only [hMe, Matrix.add_apply, Matrix.sub_apply]
      exact (((hTi i j).sub (hmulA S hSi A i j).1).sub (hmulA S hSi A i j).2.1).add
          (integrable_const _)
    have hpsd := matIntegral_posSemidef (fun z => Matrix.posSemidef_conjTranspose_mul_self (S z -
        A)) hMi
    convert hpsd using 1
    ext i j
    have hI1 := (hmulA S hSi A i j).1
    have hI2 := (hmulA S hSi A i j).2.1
    have e1 : ∫ z, ((S z - A)ᴴ * (S z - A)) i j ∂ν =
        ∫ z, (T z i j - (S z * A) i j - (A * S z) i j + (A * A) i j) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      have := congrFun (congrFun (hMe z) i) j
      simp only [Matrix.add_apply, Matrix.sub_apply] at this
      exact this
    have e2 : ∫ z, (T z i j - (S z * A) i j - (A * S z) i j + (A * A) i j) ∂ν = (∫ z, T z i j ∂ν) -
        (∫ z, (S z * A) i j ∂ν) - (∫ z, (A * S z) i j ∂ν) + (A * A) i j := by
      have h1 : Integrable (fun z => T z i j - (S z * A) i j - (A * S z) i j) ν := ((hTi i j).sub
          hI1).sub hI2
      calc _ = (∫ z, (T z i j - (S z * A) i j - (A * S z) i j) ∂ν) + ∫ _z, (A * A) i j ∂ν :=
            integral_add h1 (integrable_const _)
        _ = _ := by
          rw [integral_const, probReal_univ, one_smul]
          congr 1
          calc _ = (∫ z, (T z i j - (S z * A) i j) ∂ν) - ∫ z, (A * S z) i j ∂ν :=
                integral_sub ((hTi i j).sub hI1) hI2
            _ = _ := by rw [integral_sub (hTi i j) hI1]
    change matIntegral ν T i j - (A * A) i j = matIntegral ν (fun z => (S z - A)ᴴ * (S z - A)) i j
    rw [matIntegral_apply, matIntegral_apply, e1, e2, (hmulA S hSi A i j).2.2.1, (hmulA S hSi A i
        j).2.2.2]
    ring
  have hle : A ≤ CFC.sqrt (matIntegral ν T) := by
    rw [← CFC.sqrt_mul_self A hA.nonneg]
    exact CFC.sqrt_le_sqrt _ _ (Matrix.le_iff.2 hA2)
  refine iSup_le fun X => ?_
  have hq := quadForm_mono (Matrix.le_iff.1 hle) X
  have hlin1 : hsRe (matIntegral ν K) X = ∫ z, hsRe (K z) X ∂ν := by
    rw [hsRe_comm, hsRe_eq_re_trace, re_trace_mul_matIntegral hKi]
    congr 1; funext z; rw [hsRe_comm]; rfl
  have hlin2 : hsRe X (A * X) = ∫ z, hsRe X (S z * X) ∂ν := by
    rw [hsRe_mul_left_eq, re_trace_mul_matIntegral hSi]
    congr 1; funext z; rw [hsRe_mul_left_eq]
  have hlin3 : hsRe X (X * A) = ∫ z, hsRe X (X * S z) ∂ν := by
    rw [hsRe_mul_right_eq, re_trace_mul_matIntegral hSi]
    congr 1; funext z; rw [hsRe_mul_right_eq]
  have hi1 : Integrable (fun z => hsRe (K z) X) ν := by
    have := integrable_re_trace_mul hKi Xᴴ
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← hsRe_eq_re_trace, hsRe_comm]
  have hi2 : Integrable (fun z => hsRe X (S z * X)) ν := by
    have := integrable_re_trace_mul hSi (X * Xᴴ)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [hsRe_mul_left_eq]
  have hi3 : Integrable (fun z => hsRe X (X * S z)) ν := by
    have := integrable_re_trace_mul hSi (Xᴴ * X)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [hsRe_mul_right_eq]
  have hi23 : Integrable (fun z => hsRe X (S z * X) + hsRe X (X * S z)) ν := hi2.add hi3
  have hi123 : Integrable (fun z => 2 * hsRe (K z) X - (hsRe X (S z * X) + hsRe X (X * S z))) ν :=
      (hi1.const_mul 2).sub hi23
  have hci : Integrable (fun z => (3 / 2) * costInt (S z) (K z) X) ν := hi123.const_mul _
  have hcomp : (3 / 2) * costInt (CFC.sqrt (matIntegral ν T)) (matIntegral ν K) X ≤
      ∫ z, (3 / 2) * costInt (S z) (K z) X ∂ν := by
    rw [integral_const_mul]
    unfold costInt
    have e : ∫ z, (2 * hsRe (K z) X - (hsRe X (S z * X) + hsRe X (X * S z))) ∂ν =
        2 * hsRe (matIntegral ν K) X - (hsRe X (A * X) + hsRe X (X * A)) := by
      rw [integral_sub (hi1.const_mul 2) hi23, integral_const_mul, integral_add hi2 hi3,
        ← hlin1, ← hlin2, ← hlin3]
    rw [e]
    nlinarith [hq]
  calc ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (matIntegral ν T)) (matIntegral ν K) X)
      ≤ ENNReal.ofReal (∫ z, (3 / 2) * costInt (S z) (K z) X ∂ν) :=
        ENNReal.ofReal_le_ofReal hcomp
    _ ≤ ∫⁻ z, ENNReal.ofReal ((3 / 2) * costInt (S z) (K z) X) ∂ν :=
        ofReal_integral_le_lintegral hci
    _ ≤ ∫⁻ z, matCost (T z) (K z) ∂ν :=
        lintegral_mono fun z => le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (T z))
            (K z) X)) X
end Auto
