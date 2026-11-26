-- Prove2me | Definitions.Def_Spectral_PVM_Unbounded
-- name    : Spectral_PVM_Unbounded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:00:40.424102+00:00
-- url     : https://prove2.me/theorems/6407eef9-44d4-5c02-b2f1-e425a2bb1125
-- title:
--   Unbounded
-- statement:
--   Definitions and structural lemmas for Unbounded, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Theorems.Thm_PVM_integral_mul
import Theorems.Thm_PVM_integral_sub
import Theorems.Thm_PVM_monotone
import Theorems.Thm_PVM_norm_sq_simpleIntegral
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_piecewise_const
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
import Theorems.Thm_exists_bounded_simpleFunc_tendstoUniformly
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def PVM.scalarContent (E_pvm : PVM E) (x : E) (S : Set ℝ) : ℝ :=
  (@inner ℂ E _ (E_pvm.proj S x) x).re
theorem PVM.scalarContent_nonneg (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    0 ≤ E_pvm.scalarContent x S := by
  change 0 ≤ (@inner ℂ E _ (E_pvm.proj S x) x).re
  have h := E_pvm.monotone MeasurableSet.empty hS (Set.empty_subset S) x
  rw [E_pvm.empty, zero_apply, inner_zero_left, Complex.zero_re] at h
  exact h
theorem PVM.scalarContent_empty (E_pvm : PVM E) (x : E) :
    E_pvm.scalarContent x ∅ = 0 := by
  change (@inner ℂ E _ (E_pvm.proj ∅ x) x).re = 0
  rw [E_pvm.empty, zero_apply, inner_zero_left, Complex.zero_re]
theorem PVM.scalarContent_countably_additive_tendsto (E_pvm : PVM E) (x : E)
    (S : ℕ → Set ℝ) (hmeas : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise (Disjoint on S)) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, E_pvm.scalarContent x (S i))
      Filter.atTop (nhds (E_pvm.scalarContent x (⋃ i, S i))) := by
  have hSOT := E_pvm.countably_additive S hmeas hpair x
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hSOT (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hre := (Complex.continuous_re.tendsto _).comp hinner
  convert hre using 1
  · funext n
    change (∑ i ∈ Finset.range n,
      (@inner ℂ E _ (E_pvm.proj (S i) x) x).re) =
        (@inner ℂ E _ (∑ i ∈ Finset.range n, E_pvm.proj (S i) x) x).re
    rw [sum_inner, Complex.re_sum]
  · rfl
noncomputable def PVM.scalarMeasure (E_pvm : PVM E) (x : E) :
    MeasureTheory.Measure ℝ :=
  Measure.ofMeasurable
    (fun S _ => ENNReal.ofReal (E_pvm.scalarContent x S))
    (by rw [E_pvm.scalarContent_empty, ENNReal.ofReal_zero])
    (by
      intro S hmeas hpair
      have hnonneg : ∀ i, 0 ≤ E_pvm.scalarContent x (S i) :=
        fun i => E_pvm.scalarContent_nonneg x (S i) (hmeas i)
      have hHasSum : HasSum (fun i => E_pvm.scalarContent x (S i))
          (E_pvm.scalarContent x (⋃ i, S i)) :=
        (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
          (E_pvm.scalarContent_countably_additive_tendsto x S hmeas hpair)
      rw [← hHasSum.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg hnonneg hHasSum.summable])
theorem PVM.scalarMeasure_apply (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarMeasure x S = ENNReal.ofReal (E_pvm.scalarContent x S) := by
  exact Measure.ofMeasurable_apply S hS
theorem PVM.scalarContent_eq_norm_sq (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent x S = ‖E_pvm.proj S x‖ ^ 2 := by
  have hproj := E_pvm.isOrthogonalProjection S hS
  change (@inner ℂ E _ (E_pvm.proj S x) x).re = ‖E_pvm.proj S x‖ ^ 2
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  rw [hproj.1.adjoint_eq]
  exact congr_arg (fun T : E →L[ℂ] E => (@inner ℂ E _ (T x) x).re) hproj.2.symm
theorem PVM.scalarMeasure_univ (E_pvm : PVM E) (x : E) :
    E_pvm.scalarMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [E_pvm.scalarMeasure_apply x Set.univ MeasurableSet.univ,
    E_pvm.scalarContent_eq_norm_sq x Set.univ MeasurableSet.univ,
    E_pvm.univ, one_apply_eq_self]
theorem PVM.scalarMeasure_lt_top (E_pvm : PVM E) (x : E) (S : Set ℝ) :
    E_pvm.scalarMeasure x S < ⊤ := by
  calc
    E_pvm.scalarMeasure x S ≤ E_pvm.scalarMeasure x Set.univ :=
      measure_mono (Set.subset_univ S)
    _ = ENNReal.ofReal (‖x‖ ^ 2) := E_pvm.scalarMeasure_univ x
    _ < ⊤ := ENNReal.ofReal_lt_top
noncomputable instance PVM.scalarMeasure_isFiniteMeasure (E_pvm : PVM E) (x : E) :
    IsFiniteMeasure (E_pvm.scalarMeasure x) where
  measure_univ_lt_top := E_pvm.scalarMeasure_lt_top x Set.univ
theorem PVM.ofReal_norm_sq_simpleIntegral (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) (x : E) :
    ENNReal.ofReal (‖E_pvm.simpleIntegral f x‖ ^ 2) =
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) := by
  rw [E_pvm.norm_sq_simpleIntegral f x]
  change ENNReal.ofReal
      (∑ z ∈ f.range, ‖z‖ ^ 2 * E_pvm.scalarContent x (f ⁻¹' {z})) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun z hz =>
    mul_nonneg (sq_nonneg ‖z‖)
      (E_pvm.scalarContent_nonneg x (f ⁻¹' {z}) (f.measurableSet_fiber z)))]
  let g : ℂ → ENNReal := fun z => (↑‖z‖₊ : ENNReal) ^ 2
  have hfun : (fun t => (↑‖f t‖₊ : ENNReal) ^ 2) = fun t => f.map g t := by
    funext t
    rw [SimpleFunc.map_apply]
  rw [hfun, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ENNReal.ofReal_mul (sq_nonneg ‖z‖),
    E_pvm.scalarMeasure_apply x (f ⁻¹' {z}) (f.measurableSet_fiber z),
    ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]
  rfl
theorem PVM.ofReal_norm_sq_integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) (x : E) :
    ENNReal.ofReal (‖E_pvm.integral f hf hbdd x‖ ^ 2) =
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) := by
  obtain ⟨C, hC⟩ := hbdd
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  obtain ⟨s, hs, hsC⟩ :=
    exists_bounded_simpleFunc_tendstoUniformly f hf C hC
  have hop := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    f hf ⟨C, hC⟩ s hs
  have hval : Filter.Tendsto (fun n => E_pvm.simpleIntegral (s n) x)
      Filter.atTop (nhds (E_pvm.integral f hf ⟨C, hC⟩ x)) := by
    exact (Continuous.continuousAt
      (Continuous.clm_apply continuous_id continuous_const)).tendsto.comp hop
  have hleft : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖E_pvm.simpleIntegral (s n) x‖ ^ 2))
      Filter.atTop
      (nhds (ENNReal.ofReal (‖E_pvm.integral f hf ⟨C, hC⟩ x‖ ^ 2))) := by
    exact ENNReal.tendsto_ofReal (hval.norm.pow 2)
  have hright : Filter.Tendsto
      (fun n => ∫⁻ t, ‖s n t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x))
      Filter.atTop (nhds (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x))) := by
    apply tendsto_lintegral_of_dominated_convergence
      (fun _ => ENNReal.ofReal (C ^ 2))
    · intro n
      exact ((s n).measurable.nnnorm.pow_const 2).coe_nnreal_ennreal
    · intro n
      apply ae_of_all
      intro t
      change ‖s n t‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2)
      calc
        ‖s n t‖ₑ ^ 2 = ENNReal.ofReal (‖s n t‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg (s n t)) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal (C ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg (s n t)) hC_nonneg).2 (hsC n t))
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (E_pvm.scalarMeasure_lt_top x Set.univ).ne
    · apply ae_of_all
      intro t
      have hst : Filter.Tendsto (fun n => s n t) Filter.atTop (nhds (f t)) :=
        hs.tendsto_at t
      have hreal := ENNReal.tendsto_ofReal (hst.norm.pow 2)
      convert hreal using 1
      · ext n
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm]
      · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm]
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext n
  exact E_pvm.ofReal_norm_sq_simpleIntegral (s n) x
theorem PVM.scalarContent_smul (E_pvm : PVM E) (c : ℂ) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent (c • x) S = ‖c‖ ^ 2 * E_pvm.scalarContent x S := by
  rw [E_pvm.scalarContent_eq_norm_sq (c • x) S hS,
    E_pvm.scalarContent_eq_norm_sq x S hS, map_smul, norm_smul]
  ring
theorem PVM.scalarContent_add_le (E_pvm : PVM E) (x y : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent (x + y) S ≤
      2 * (E_pvm.scalarContent x S + E_pvm.scalarContent y S) := by
  rw [E_pvm.scalarContent_eq_norm_sq (x + y) S hS,
    E_pvm.scalarContent_eq_norm_sq x S hS,
    E_pvm.scalarContent_eq_norm_sq y S hS, map_add]
  exact ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (norm_add_le _ _)).trans add_sq_le
@[simp]
theorem PVM.scalarMeasure_zero (E_pvm : PVM E) :
    E_pvm.scalarMeasure (0 : E) = 0 := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply 0 S hS,
    E_pvm.scalarContent_eq_norm_sq 0 S hS, map_zero, norm_zero,
    zero_pow (by omega), ENNReal.ofReal_zero]
  rfl
theorem PVM.scalarMeasure_smul (E_pvm : PVM E) (c : ℂ) (x : E) :
    E_pvm.scalarMeasure (c • x) =
      ENNReal.ofReal (‖c‖ ^ 2) • E_pvm.scalarMeasure x := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply (c • x) S hS,
    E_pvm.scalarContent_smul c x S hS,
    ENNReal.ofReal_mul (sq_nonneg ‖c‖), Measure.smul_apply, smul_eq_mul,
    E_pvm.scalarMeasure_apply x S hS]
theorem PVM.scalarMeasure_add_le (E_pvm : PVM E) (x y : E) :
    E_pvm.scalarMeasure (x + y) ≤
      (2 : ENNReal) • (E_pvm.scalarMeasure x + E_pvm.scalarMeasure y) := by
  apply Measure.le_iff.2
  intro S hS
  rw [E_pvm.scalarMeasure_apply (x + y) S hS, Measure.smul_apply,
    smul_eq_mul, Measure.add_apply, E_pvm.scalarMeasure_apply x S hS,
    E_pvm.scalarMeasure_apply y S hS]
  calc
    ENNReal.ofReal (E_pvm.scalarContent (x + y) S) ≤
        ENNReal.ofReal
          (2 * (E_pvm.scalarContent x S + E_pvm.scalarContent y S)) :=
      ENNReal.ofReal_le_ofReal (E_pvm.scalarContent_add_le x y S hS)
    _ = (2 : ENNReal) *
        (ENNReal.ofReal (E_pvm.scalarContent x S) +
          ENNReal.ofReal (E_pvm.scalarContent y S)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add
          (E_pvm.scalarContent_nonneg x S hS)
          (E_pvm.scalarContent_nonneg y S hS)]
      norm_num
noncomputable def PVM.squareIntegrableDomain (E_pvm : PVM E)
    (f : ℝ → ℂ) : Submodule ℂ E where
  carrier := {x | ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤}
  zero_mem' := by
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (0 : E))) < ⊤
    rw [E_pvm.scalarMeasure_zero, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro x y hx hy
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x + y))) < ⊤
    have hle := lintegral_mono' (E_pvm.scalarMeasure_add_le x y)
      (le_refl (fun t : ℝ => (↑(‖f t‖₊ ^ 2) : ENNReal)))
    refine hle.trans_lt ?_
    rw [lintegral_smul_measure, lintegral_add_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) ((ENNReal.add_lt_top).2 ⟨hx, hy⟩)
  smul_mem' := by
    intro c x hx
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (c • x))) < ⊤
    rw [E_pvm.scalarMeasure_smul c x, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx
noncomputable def PVM.spectralTruncation (f : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if ‖f t‖ ≤ n then f t else 0
theorem PVM.spectralTruncation_measurable (f : ℝ → ℂ) (hf : Measurable f)
    (n : ℕ) : Measurable (PVM.spectralTruncation f n) := by
  unfold PVM.spectralTruncation
  exact Measurable.ite (measurableSet_le hf.norm measurable_const) hf measurable_const
theorem PVM.norm_spectralTruncation_le (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    ‖PVM.spectralTruncation f n t‖ ≤ n := by
  by_cases h : ‖f t‖ ≤ n
  · rw [PVM.spectralTruncation, if_pos h]
    exact h
  · rw [PVM.spectralTruncation, if_neg h, norm_zero]
    exact Nat.cast_nonneg n
noncomputable def PVM.truncatedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) : E →L[ℂ] E :=
  E_pvm.integral (PVM.spectralTruncation f n)
    (PVM.spectralTruncation_measurable f hf n)
    ⟨n, PVM.norm_spectralTruncation_le f n⟩
theorem PVM.norm_spectralTruncation_sub_le (f : ℝ → ℂ)
    (n m : ℕ) (t : ℝ) :
    ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖ ≤ m + n := by
  calc
    ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖ ≤
        ‖PVM.spectralTruncation f m t‖ + ‖PVM.spectralTruncation f n t‖ :=
      norm_sub_le _ _
    _ ≤ m + n := add_le_add
      (PVM.norm_spectralTruncation_le f m t)
      (PVM.norm_spectralTruncation_le f n t)
theorem PVM.spectralTruncation_error_measurable (f : ℝ → ℂ)
    (hf : Measurable f) (n : ℕ) :
    Measurable (fun t => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal)) := by
  exact ((hf.sub (PVM.spectralTruncation_measurable f hf n)).nnnorm.pow_const 2).coe_nnreal_ennreal
theorem PVM.spectralTruncation_error_le (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal) ≤
      ↑(‖f t‖₊ ^ 2) := by
  by_cases h : ‖f t‖ ≤ n
  · rw [PVM.spectralTruncation, if_pos h, sub_self, nnnorm_zero,
      zero_pow (by omega)]
    exact bot_le
  · rw [PVM.spectralTruncation, if_neg h, sub_zero]
theorem PVM.spectralTruncation_error_tendsto_zero (f : ℝ → ℂ) (t : ℝ) :
    Filter.Tendsto
      (fun n => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, if_pos, sub_self, nnnorm_zero,
    zero_pow (by omega), ENNReal.coe_zero]
  exact hN.trans (Nat.cast_le.2 hn)
theorem PVM.lintegral_truncation_error_tendsto_zero (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f) :
    Filter.Tendsto
      (fun n => ∫⁻ t,
        (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop (nhds 0) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := E_pvm.scalarMeasure (x : E))
    (F := fun n t => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0)
    (fun t => (↑(‖f t‖₊ ^ 2) : ENNReal))
    (fun n => PVM.spectralTruncation_error_measurable f hf n)
    (fun n => ae_of_all _ fun t => PVM.spectralTruncation_error_le f n t)
    x.property.ne
    (ae_of_all _ fun t => PVM.spectralTruncation_error_tendsto_zero f t)
  simpa only [lintegral_zero] using h
theorem PVM.spectralTruncation_sub_le_error (f : ℝ → ℂ) {n m : ℕ}
    (hnm : n ≤ m) (t : ℝ) :
    (↑(‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal) ≤
      ↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) := by
  unfold PVM.spectralTruncation
  by_cases hn : ‖f t‖ ≤ n
  · have hm : ‖f t‖ ≤ m := hn.trans (Nat.cast_le.2 hnm)
    rw [if_pos hn, if_pos hm]
  · by_cases hm : ‖f t‖ ≤ m
    · rw [if_neg hn, if_pos hm]
    · rw [if_neg hn, if_neg hm, sub_self, nnnorm_zero, zero_pow (by omega)]
      exact bot_le
theorem PVM.ofReal_norm_sq_truncatedIntegral_sub (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E) (n m : ℕ) :
    ENNReal.ofReal
        (‖E_pvm.truncatedIntegral f hf m x -
          E_pvm.truncatedIntegral f hf n x‖ ^ 2) =
      ∫⁻ t,
        ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
          ∂(E_pvm.scalarMeasure x) := by
  let gm := PVM.spectralTruncation f m
  let gn := PVM.spectralTruncation f n
  have hgm : Measurable gm := PVM.spectralTruncation_measurable f hf m
  have hgn : Measurable gn := PVM.spectralTruncation_measurable f hf n
  let hbddm : ∃ C, ∀ t, ‖gm t‖ ≤ C :=
    ⟨m, PVM.norm_spectralTruncation_le f m⟩
  let hbddn : ∃ C, ∀ t, ‖gn t‖ ≤ C :=
    ⟨n, PVM.norm_spectralTruncation_le f n⟩
  let hbddsub : ∃ C, ∀ t, ‖(gm - gn) t‖ ≤ C :=
    ⟨m + n, PVM.norm_spectralTruncation_sub_le f n m⟩
  have hid := E_pvm.ofReal_norm_sq_integral
    (gm - gn) (hgm.sub hgn) hbddsub x
  rw [E_pvm.integral_sub gm gn hgm hgn hbddm hbddn hbddsub] at hid
  simpa only [PVM.truncatedIntegral, gm, gn, Pi.sub_apply, sub_apply] using hid
theorem PVM.cauchySeq_truncatedIntegral_of_l2 (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f)
    (hL2 : ∀ {n m : ℕ}, n ≤ m →
      ENNReal.ofReal
          (‖E_pvm.truncatedIntegral f hf m (x : E) -
            E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2) =
        ∫⁻ t,
          ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E))) :
    CauchySeq (fun n => E_pvm.truncatedIntegral f hf n (x : E)) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  have herr := E_pvm.lintegral_truncation_error_tendsto_zero f hf x
  have hthreshold :
      0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1
    (herr.eventually (gt_mem_nhds hthreshold)))
  refine ⟨N, ?_⟩
  have hordered : ∀ {n m : ℕ}, N ≤ n → n ≤ m →
      dist (E_pvm.truncatedIntegral f hf m (x : E))
        (E_pvm.truncatedIntegral f hf n (x : E)) < ε := by
    intro n m hNn hnm
    rw [dist_eq_norm]
    have hlintegral :
        (∫⁻ t,
          ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E))) ≤
          ∫⁻ t, ‖f t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E)) :=
      lintegral_mono (fun t => PVM.spectralTruncation_sub_le_error f hnm t)
    have hofReal :
        ENNReal.ofReal
            (‖E_pvm.truncatedIntegral f hf m (x : E) -
              E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2) <
          ENNReal.ofReal (ε ^ 2) :=
      (hL2 hnm).trans_lt (hlintegral.trans_lt (hN n hNn))
    have hsquare :
        ‖E_pvm.truncatedIntegral f hf m (x : E) -
          E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2 < ε ^ 2 :=
      (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare
  intro m hm n hn
  rcases le_total n m with hnm | hmn
  · exact hordered hn hnm
  · rw [dist_comm]
    exact hordered hm hmn
theorem PVM.cauchySeq_truncatedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f) :
    CauchySeq (fun n => E_pvm.truncatedIntegral f hf n (x : E)) := by
  apply E_pvm.cauchySeq_truncatedIntegral_of_l2 f hf x
  intro n m _hnm
  exact E_pvm.ofReal_norm_sq_truncatedIntegral_sub f hf (x : E) n m
noncomputable def PVM.unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) : E →ₗ.[ℂ] E :=
  { domain := E_pvm.squareIntegrableDomain f
    toFun :=
      { toFun := fun x => Filter.limUnder Filter.atTop
          (fun n => E_pvm.truncatedIntegral f hf n (x : E))
        map_add' := by
          intro x y
          have hxy := (E_pvm.cauchySeq_truncatedIntegral f hf (x + y)).tendsto_limUnder
          have hx := (E_pvm.cauchySeq_truncatedIntegral f hf x).tendsto_limUnder
          have hy := (E_pvm.cauchySeq_truncatedIntegral f hf y).tendsto_limUnder
          apply tendsto_nhds_unique hxy
          have hfun :
              (fun n => E_pvm.truncatedIntegral f hf n ((x + y : _) : E)) =
                fun n => E_pvm.truncatedIntegral f hf n (x : E) +
                  E_pvm.truncatedIntegral f hf n (y : E) := by
            funext n
            change E_pvm.truncatedIntegral f hf n ((x : E) + (y : E)) = _
            exact map_add _ _ _
          rw [hfun]
          exact hx.add hy
        map_smul' := by
          intro c x
          have hcx := (E_pvm.cauchySeq_truncatedIntegral f hf (c • x)).tendsto_limUnder
          have hx := (E_pvm.cauchySeq_truncatedIntegral f hf x).tendsto_limUnder
          apply tendsto_nhds_unique hcx
          have hfun :
              (fun n => E_pvm.truncatedIntegral f hf n ((c • x : _) : E)) =
                fun n => c • E_pvm.truncatedIntegral f hf n (x : E) := by
            funext n
            change E_pvm.truncatedIntegral f hf n (c • (x : E)) = _
            exact map_smul _ _ _
          rw [hfun]
          exact hx.const_smul c } }
theorem PVM.mem_domain_unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E) :
    x ∈ (E_pvm.unboundedIntegral f hf).domain ↔
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤ :=
  Iff.rfl
noncomputable def complexIndicator (S : Set ℝ) (r : ℝ) : ℂ :=
  S.indicator (fun _ => (1 : ℂ)) r
theorem complexIndicator_measurable {S : Set ℝ}
    (hS : MeasurableSet S) : Measurable (complexIndicator S) := by
  exact measurable_const.indicator hS
theorem complexIndicator_bounded (S : Set ℝ) :
    ∃ C, ∀ r, ‖complexIndicator S r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  by_cases hr : r ∈ S
  · rw [complexIndicator, Set.indicator_of_mem hr, norm_one]
  · rw [complexIndicator, Set.indicator_of_notMem hr, norm_zero]
    exact zero_le_one
theorem complexIndicator_mul_bounded
    (S : Set ℝ) (f : ℝ → ℂ) {C : ℝ} (hf : ∀ r, ‖f r‖ ≤ C) :
    ∃ D, ∀ r, ‖complexIndicator S r * f r‖ ≤ D := by
  refine ⟨C, fun r => ?_⟩
  by_cases hr : r ∈ S
  · rw [complexIndicator, Set.indicator_of_mem hr, one_mul]
    exact hf r
  · rw [complexIndicator, Set.indicator_of_notMem hr, zero_mul, norm_zero]
    exact (norm_nonneg (f 0)).trans (hf 0)
theorem PVM.integral_complexIndicator (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E_pvm.integral (complexIndicator S) (complexIndicator_measurable hS)
      (complexIndicator_bounded S) = E_pvm.proj S := by
  let s : SimpleFunc ℝ ℂ :=
    SimpleFunc.piecewise S hS (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)
  have hsfun : ∀ r, s r = complexIndicator S r := by
    intro r
    dsimp only [s]
    by_cases hr : r ∈ S
    · rw [SimpleFunc.piecewise_apply, if_pos hr,
        SimpleFunc.const_apply, complexIndicator, Set.indicator_of_mem hr]
    · rw [SimpleFunc.piecewise_apply, if_neg hr,
        SimpleFunc.const_apply, complexIndicator, Set.indicator_of_notMem hr]
  have hU : TendstoUniformly (fun _n : ℕ => fun r => s r)
      (complexIndicator S) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    apply Filter.Eventually.of_forall
    intro n r
    rw [hsfun r, dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (complexIndicator S) (complexIndicator_measurable hS)
      (complexIndicator_bounded S) (fun _n => s) hU
  have hsint : E_pvm.simpleIntegral s = E_pvm.proj S := by
    simpa only [one_smul] using E_pvm.simpleIntegral_piecewise_const S hS 1
  have hlim' : Filter.Tendsto (fun _n : ℕ => E_pvm.proj S)
      Filter.atTop
      (nhds (E_pvm.integral (complexIndicator S)
        (complexIndicator_measurable hS) (complexIndicator_bounded S))) := by
    convert hlim using 1
    funext n
    exact hsint.symm
  exact tendsto_nhds_unique hlim' tendsto_const_nhds
theorem PVM.proj_mul_integral (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C) :
    E_pvm.proj S * E_pvm.integral f hf hbdd =
      E_pvm.integral (fun r => complexIndicator S r * f r)
        ((complexIndicator_measurable hS).mul hf)
        (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd)) := by
  rw [← E_pvm.integral_complexIndicator S hS]
  symm
  exact E_pvm.integral_mul (complexIndicator S) f
    (complexIndicator_measurable hS) hf (complexIndicator_bounded S) hbdd
    (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd))
theorem PVM.scalarMeasure_integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (x : E) :
    E_pvm.scalarMeasure (E_pvm.integral f hf hbdd x) =
      (E_pvm.scalarMeasure x).withDensity
        (fun r => ((↑(‖f r‖₊ ^ 2) : ENNReal))) := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply _ S hS,
    E_pvm.scalarContent_eq_norm_sq _ S hS]
  rw [show E_pvm.proj S (E_pvm.integral f hf hbdd x) =
      E_pvm.integral (fun r => complexIndicator S r * f r)
        ((complexIndicator_measurable hS).mul hf)
        (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd)) x by
    have happ := congrArg (fun T : E →L[ℂ] E => T x)
      (E_pvm.proj_mul_integral S hS f hf hbdd)
    simpa only [mul_apply_eq_comp] using happ]
  rw [E_pvm.ofReal_norm_sq_integral]
  rw [withDensity_apply _ hS]
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ S
  · rw [Set.indicator_of_mem hr, complexIndicator,
      Set.indicator_of_mem hr, one_mul, ENNReal.coe_pow]
  · rw [Set.indicator_of_notMem hr, complexIndicator,
      Set.indicator_of_notMem hr, zero_mul, nnnorm_zero]
    norm_num
theorem PVM.integral_mem_domain_unboundedIntegral
    (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (hprodBdd : ∃ C, ∀ r : ℝ, ‖g r * f r‖ ≤ C) (x : E) :
    E_pvm.integral f hf hbdd x ∈
      (E_pvm.unboundedIntegral g hg).domain := by
  rw [E_pvm.mem_domain_unboundedIntegral]
  rw [E_pvm.scalarMeasure_integral f hf hbdd x]
  let density : ℝ → ENNReal := fun r => (↑(‖f r‖₊ ^ 2) : ENNReal)
  have hdensity : Measurable density :=
    ((hf.nnnorm.pow_const 2).coe_nnreal_ennreal)
  have hgSq : Measurable (fun r : ℝ =>
      (↑(‖g r‖₊ ^ 2) : ENNReal)) :=
    ((hg.nnnorm.pow_const 2).coe_nnreal_ennreal)
  change (∫⁻ t : ℝ, (↑(‖g t‖₊ ^ 2) : ENNReal)
    ∂(E_pvm.scalarMeasure x).withDensity density) < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hgSq]
  have hfun : (fun r : ℝ => density r * (↑(‖g r‖₊ ^ 2) : ENNReal)) =
      (fun r : ℝ => (↑(‖g r * f r‖₊ ^ 2) : ENNReal)) := by
    funext r
    unfold density
    rw [← ENNReal.coe_mul, nnnorm_mul, mul_pow, mul_comm]
  change (∫⁻ r : ℝ, density r * (↑(‖g r‖₊ ^ 2) : ENNReal)
    ∂E_pvm.scalarMeasure x) < ⊤
  rw [hfun]
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (fun r => g r * f r) (hg.mul hf) hprodBdd x
  have hL2' : ENNReal.ofReal
      (‖E_pvm.integral (fun r => g r * f r) (hg.mul hf) hprodBdd x‖ ^ 2) =
      ∫⁻ r : ℝ, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
        ∂E_pvm.scalarMeasure x := by
    simpa only [ENNReal.coe_pow] using hL2
  rw [← hL2']
  exact ENNReal.ofReal_lt_top
noncomputable def boundedTruncation
    (g : ℝ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  if ‖g r‖ ≤ n then g r else 0
theorem boundedTruncation_measurable
    (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    Measurable (boundedTruncation g n) := by
  unfold boundedTruncation
  exact Measurable.ite (measurableSet_le hg.norm measurable_const) hg measurable_const
theorem norm_boundedTruncation_le
    (g : ℝ → ℂ) (n : ℕ) (r : ℝ) :
    ‖boundedTruncation g n r‖ ≤ n := by
  by_cases hr : ‖g r‖ ≤ n
  · rw [boundedTruncation, if_pos hr]
    exact hr
  · rw [boundedTruncation, if_neg hr, norm_zero]
    exact Nat.cast_nonneg n
theorem boundedTruncation_mul_bounded
    (g f : ℝ → ℂ) (n : ℕ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C) :
    ∃ C, ∀ r, ‖(boundedTruncation g n * f) r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨n * C, fun r => ?_⟩
  change ‖boundedTruncation g n r * f r‖ ≤ (n : ℝ) * C
  rw [norm_mul]
  exact mul_le_mul (norm_boundedTruncation_le g n r) (hC r)
    (norm_nonneg (f r)) (Nat.cast_nonneg n)
open Filter


