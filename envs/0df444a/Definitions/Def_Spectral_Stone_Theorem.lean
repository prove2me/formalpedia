-- Prove2me | Definitions.Def_Spectral_Stone_Theorem
-- name    : Spectral_Stone_Theorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:07:12.168579+00:00
-- url     : https://prove2.me/theorems/4a22e9f8-2d37-544f-b477-fb5744dd3042
-- title:
--   Theorem
-- statement:
--   Definitions and structural lemmas for Theorem, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Theorem.lean

import Definitions.Def_Spectral_Stone_SelfAdjoint
import Definitions.Def_Spectral_Spectral_Existence
import Theorems.Thm_PVM_integral_mul
import Theorems.Thm_PVM_integral_sub
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
import Theorems.Thm_spectral_theorem_existence
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


set_option autoImplicit false
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def stonePhase (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))
theorem stonePhase_measurable (t : ℝ) : Measurable (stonePhase t) := by
  unfold stonePhase
  fun_prop
theorem stonePhase_norm (t r : ℝ) : ‖stonePhase t r‖ = 1 := by
  rw [stonePhase, mul_assoc, ← Complex.ofReal_mul]
  exact Complex.norm_exp_I_mul_ofReal (t * r)
theorem stonePhase_zero (r : ℝ) : stonePhase 0 r = 1 := by
  rw [stonePhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
theorem stonePhase_add (s t r : ℝ) :
    stonePhase (s + t) r = stonePhase s r * stonePhase t r := by
  rw [stonePhase, stonePhase, stonePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem stonePhase_bounded (t : ℝ) : ∀ r, ‖stonePhase t r‖ ≤ 1 :=
  fun r => (stonePhase_norm t r).le
theorem PVM.integral_congr_local (E_pvm : PVM E) {f g : ℝ → ℂ}
    (hfg : f = g) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C) (hbddg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    E_pvm.integral f hf hbddf = E_pvm.integral g hg hbddg := by
  subst g
  rfl
theorem PVM.integral_one_local (E_pvm : PVM E) :
    E_pvm.integral (fun _ : ℝ => (1 : ℂ)) measurable_const
      ⟨1, fun _ => by rw [norm_one]⟩ = 1 := by
  have hUniform : TendstoUniformly
      (fun (_n : ℕ) (t : ℝ) => (1 : SimpleFunc ℝ ℂ) t)
      (fun _t : ℝ => (1 : ℂ)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [] with n
    intro t
    change dist (1 : ℂ) 1 < ε
    rw [dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (fun _ : ℝ => (1 : ℂ)) measurable_const
    ⟨1, fun _ => by rw [norm_one]⟩ (fun _n => (1 : SimpleFunc ℝ ℂ)) hUniform
  have hone : Tendsto (fun _n : ℕ => (1 : E →L[ℂ] E)) atTop (nhds 1) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique hlim
  simpa only [E_pvm.simpleIntegral_one] using hone
noncomputable def spectralEvolution (E_pvm : PVM E) (t : ℝ) : E →L[ℂ] E :=
  E_pvm.integral (stonePhase t) (stonePhase_measurable t) ⟨1, stonePhase_bounded t⟩
theorem spectralEvolution_zero (E_pvm : PVM E) :
    spectralEvolution E_pvm 0 = 1 := by
  change E_pvm.integral (stonePhase 0) (stonePhase_measurable 0)
    ⟨1, stonePhase_bounded 0⟩ = 1
  have hfun : stonePhase 0 = fun _ : ℝ => (1 : ℂ) := by
    funext r
    exact stonePhase_zero r
  calc
    E_pvm.integral (stonePhase 0) (stonePhase_measurable 0)
        ⟨1, stonePhase_bounded 0⟩ =
      E_pvm.integral (fun _ : ℝ => (1 : ℂ)) measurable_const
        ⟨1, fun _ => by rw [norm_one]⟩ :=
      E_pvm.integral_congr_local hfun _ _ _ _
    _ = 1 := E_pvm.integral_one_local
theorem spectralEvolution_add (E_pvm : PVM E) (s t : ℝ) :
    spectralEvolution E_pvm (s + t) =
      spectralEvolution E_pvm s * spectralEvolution E_pvm t := by
  have hfun : stonePhase (s + t) = stonePhase s * stonePhase t := by
    funext r
    exact stonePhase_add s t r
  have hbddMul : ∀ r, ‖(stonePhase s * stonePhase t) r‖ ≤ 1 := by
    intro r
    change ‖stonePhase s r * stonePhase t r‖ ≤ 1
    rw [norm_mul, stonePhase_norm, stonePhase_norm, one_mul]
  change E_pvm.integral (stonePhase (s + t)) (stonePhase_measurable (s + t))
      ⟨1, stonePhase_bounded (s + t)⟩ =
    E_pvm.integral (stonePhase s) (stonePhase_measurable s) ⟨1, stonePhase_bounded s⟩ *
      E_pvm.integral (stonePhase t) (stonePhase_measurable t) ⟨1, stonePhase_bounded t⟩
  calc
    E_pvm.integral (stonePhase (s + t)) (stonePhase_measurable (s + t))
        ⟨1, stonePhase_bounded (s + t)⟩ =
      E_pvm.integral (stonePhase s * stonePhase t)
        ((stonePhase_measurable s).mul (stonePhase_measurable t)) ⟨1, hbddMul⟩ :=
      E_pvm.integral_congr_local hfun _ _ _ _
    _ = E_pvm.integral (stonePhase s) (stonePhase_measurable s)
          ⟨1, stonePhase_bounded s⟩ *
        E_pvm.integral (stonePhase t) (stonePhase_measurable t)
          ⟨1, stonePhase_bounded t⟩ :=
      E_pvm.integral_mul (stonePhase s) (stonePhase t)
        (stonePhase_measurable s) (stonePhase_measurable t)
        ⟨1, stonePhase_bounded s⟩ ⟨1, stonePhase_bounded t⟩ ⟨1, hbddMul⟩
theorem spectralEvolution_norm (E_pvm : PVM E) (t : ℝ) (x : E) :
    ‖spectralEvolution E_pvm t x‖ = ‖x‖ := by
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (stonePhase t) (stonePhase_measurable t) ⟨1, stonePhase_bounded t⟩ x
  change ENNReal.ofReal (‖spectralEvolution E_pvm t x‖ ^ 2) =
    (∫⁻ r, ‖stonePhase t r‖₊ ^ 2 ∂(E_pvm.scalarMeasure x)) at hL2
  have hright :
      (∫⁻ r, ‖stonePhase t r‖₊ ^ 2 ∂(E_pvm.scalarMeasure x)) =
        ENNReal.ofReal (‖x‖ ^ 2) := by
    change (∫⁻ r, ‖stonePhase t r‖ₑ ^ 2 ∂(E_pvm.scalarMeasure x)) = _
    have henorm (r : ℝ) : ‖stonePhase t r‖ₑ = 1 := by
      rw [enorm_eq_nnnorm]
      exact congrArg (fun z : NNReal => (z : ENNReal))
        (Subtype.ext (stonePhase_norm t r))
    simp_rw [henorm, one_pow]
    rw [lintegral_one, E_pvm.scalarMeasure_univ x]
  rw [hright] at hL2
  have hsquare : ‖spectralEvolution E_pvm t x‖ ^ 2 = ‖x‖ ^ 2 := by
    exact (ENNReal.ofReal_eq_ofReal_iff
      (sq_nonneg ‖spectralEvolution E_pvm t x‖) (sq_nonneg ‖x‖)).mp hL2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare
theorem spectralEvolution_surjective (E_pvm : PVM E) (t : ℝ) :
    Function.Surjective (spectralEvolution E_pvm t) := by
  intro y
  refine ⟨spectralEvolution E_pvm (-t) y, ?_⟩
  have hmul : spectralEvolution E_pvm t * spectralEvolution E_pvm (-t) = 1 := by
    rw [← spectralEvolution_add, add_neg_cancel, spectralEvolution_zero]
  change (spectralEvolution E_pvm t * spectralEvolution E_pvm (-t)) y = y
  rw [hmul, one_apply_eq_self]
theorem spectralEvolution_unitary (E_pvm : PVM E) (t : ℝ) :
    spectralEvolution E_pvm t ∈ unitary (E →L[ℂ] E) := by
  let f : E →ₗᵢ[ℂ] E := LinearIsometry.mk (spectralEvolution E_pvm t).toLinearMap
    (spectralEvolution_norm E_pvm t)
  let e : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective f
    (spectralEvolution_surjective E_pvm t)
  let u : unitary (E →L[ℂ] E) := Unitary.linearIsometryEquiv.symm e
  have hueq : (u : E →L[ℂ] E) = spectralEvolution E_pvm t := by
    ext x
    change e x = spectralEvolution E_pvm t x
    change f x = spectralEvolution E_pvm t x
    rfl
  rw [← hueq]
  exact u.property
theorem stonePhase_continuous_left (r : ℝ) :
    Continuous (fun t : ℝ => stonePhase t r) := by
  unfold stonePhase
  fun_prop
theorem stonePhase_sub_bounded (s t : ℝ) :
    ∀ r, ‖stonePhase t r - stonePhase s r‖ ≤ 2 := by
  intro r
  calc
    ‖stonePhase t r - stonePhase s r‖ ≤
        ‖stonePhase t r‖ + ‖stonePhase s r‖ := norm_sub_le _ _
    _ = 2 := by rw [stonePhase_norm, stonePhase_norm]; norm_num
theorem spectralEvolution_sub (E_pvm : PVM E) (t s : ℝ) :
    spectralEvolution E_pvm t - spectralEvolution E_pvm s =
      E_pvm.integral (stonePhase t - stonePhase s)
        ((stonePhase_measurable t).sub (stonePhase_measurable s))
        ⟨2, stonePhase_sub_bounded s t⟩ := by
  change E_pvm.integral (stonePhase t) (stonePhase_measurable t)
      ⟨1, stonePhase_bounded t⟩ -
    E_pvm.integral (stonePhase s) (stonePhase_measurable s)
      ⟨1, stonePhase_bounded s⟩ = _
  exact (E_pvm.integral_sub (stonePhase t) (stonePhase s)
    (stonePhase_measurable t) (stonePhase_measurable s)
    ⟨1, stonePhase_bounded t⟩ ⟨1, stonePhase_bounded s⟩
    ⟨2, stonePhase_sub_bounded s t⟩).symm
theorem phaseDifference_lintegral_tendsto_zero
    (E_pvm : PVM E) (x : E) (s : ℝ) :
    Tendsto
      (fun t : ℝ => ∫⁻ r,
        (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure x))
      (nhds s) (nhds 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := E_pvm.scalarMeasure x)
    (l := nhds s)
    (F := fun t r => (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0) (fun _ => (4 : ENNReal))
    (Filter.Eventually.of_forall fun t =>
      ((((stonePhase_measurable t).sub
        (stonePhase_measurable s)).nnnorm.pow_const 2).coe_nnreal_ennreal))
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun r => by
      change ‖stonePhase t r - stonePhase s r‖ₑ ^ 2 ≤ (4 : ENNReal)
      calc
        ‖stonePhase t r - stonePhase s r‖ₑ ^ 2 =
            ENNReal.ofReal (‖stonePhase t r - stonePhase s r‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal (2 ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
            (stonePhase_sub_bounded s t r))
        _ = 4 := by norm_num)
    (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (by norm_num)
        (E_pvm.scalarMeasure_lt_top x Set.univ).ne)
    (ae_of_all _ fun r => by
      have hcont : Continuous (fun t : ℝ =>
          (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal)) := by
        have hdiff : Continuous
            (fun t : ℝ => stonePhase t r - stonePhase s r) :=
          (stonePhase_continuous_left r).sub continuous_const
        have hnnorm : Continuous
            (fun t : ℝ => ‖stonePhase t r - stonePhase s r‖₊) := hdiff.nnnorm
        exact ENNReal.continuous_coe.comp (hnnorm.pow 2)
      have htend : Tendsto
          (fun t : ℝ => (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal))
          (nhds s)
          (nhds (↑(‖stonePhase s r - stonePhase s r‖₊ ^ 2) : ENNReal)) :=
        hcont.continuousAt
      simpa only [sub_self, nnnorm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.coe_zero]
        using htend)
  simpa only [lintegral_zero] using h
theorem spectralEvolution_stronglyContinuous (E_pvm : PVM E) (x : E) :
    Continuous (fun t => spectralEvolution E_pvm t x) := by
  rw [continuous_iff_continuousAt]
  intro s
  change Tendsto (fun t => spectralEvolution E_pvm t x) (nhds s)
    (nhds (spectralEvolution E_pvm s x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hIntegral := phaseDifference_lintegral_tendsto_zero E_pvm x s
  have hthreshold : 0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  filter_upwards [hIntegral.eventually (gt_mem_nhds hthreshold)] with t ht
  rw [dist_eq_norm]
  have hop := spectralEvolution_sub E_pvm t s
  have happ := congrArg (fun T : E →L[ℂ] E => T x) hop
  change spectralEvolution E_pvm t x - spectralEvolution E_pvm s x =
    E_pvm.integral (stonePhase t - stonePhase s)
      ((stonePhase_measurable t).sub (stonePhase_measurable s))
      ⟨2, stonePhase_sub_bounded s t⟩ x at happ
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (stonePhase t - stonePhase s)
    ((stonePhase_measurable t).sub (stonePhase_measurable s))
    ⟨2, stonePhase_sub_bounded s t⟩ x
  have hofReal :
      ENNReal.ofReal
          (‖spectralEvolution E_pvm t x - spectralEvolution E_pvm s x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
    rw [happ, hL2]
    exact ht
  have hsquare :
      ‖spectralEvolution E_pvm t x - spectralEvolution E_pvm s x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare
noncomputable def spectralUnitaryGroup (E_pvm : PVM E) :
    StrongContUnitary E where
  toFun := spectralEvolution E_pvm
  isUnitary := spectralEvolution_unitary E_pvm
  zero := spectralEvolution_zero E_pvm
  add := spectralEvolution_add E_pvm
  stronglyContinuous := spectralEvolution_stronglyContinuous E_pvm
noncomputable def stoneQuotient (t r : ℝ) : ℂ :=
  (Complex.I * (t : ℂ))⁻¹ * (stonePhase t r - stonePhase 0 r)
theorem stoneQuotient_measurable (t : ℝ) : Measurable (stoneQuotient t) := by
  unfold stoneQuotient
  exact measurable_const.mul
    ((stonePhase_measurable t).sub (stonePhase_measurable 0))
theorem stoneQuotient_bounded (t : ℝ) :
    ∀ r, ‖stoneQuotient t r‖ ≤ ‖(Complex.I * (t : ℂ))⁻¹‖ * 2 := by
  intro r
  rw [stoneQuotient, norm_mul]
  exact mul_le_mul_of_nonneg_left (stonePhase_sub_bounded 0 t r) (norm_nonneg _)
noncomputable def quotientTime (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)
noncomputable def PVM.phaseUnitaryGroup (E_pvm : PVM E) : StrongContUnitary E :=
  spectralUnitaryGroup E_pvm
noncomputable def selfAdjoint_generates_unitary_group
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    StrongContUnitary E :=
  (Classical.choose (spectral_theorem_existence A hA)).phaseUnitaryGroup


