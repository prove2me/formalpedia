-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFinitePerturbationCleanV6
-- name    : MarkovProcess_V3HRepair_FeynmanKacFinitePerturbationCleanV6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:48:19.959586+00:00
-- url     : https://prove2.me/theorems/51cfe30a-fb26-44e7-a695-481eabb564fe
-- title:
--   Verified MarkovProcess source repair: FeynmanKacFinitePerturbationCleanV6
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FeynmanKacFinitePerturbationCleanV6 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacFinitePerturbationCleanV6 source SHA-256 07fc785b396dc9b3555c92c583aacb9f472149a62dfafdb59878dfdfcce81049. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FellerConditionalCleanV5
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousProcessEvalMeasurableCleanV8
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacSemigroupCleanV4
import Definitions.Def_MarkovProcess_V3HRepair_OneSubExpAdditiveFunctionalCleanV1

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [SecondCountableTopology alpha] in
/-- The accumulated potential is monotone in time for a nonnegative potential. -/
theorem feynmanKacAdditiveFunctional_mono {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q s omega ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [← add_tsub_cancel_of_le hst,
    feynmanKacAdditiveFunctional_add hq hq0 hqC]
  exact le_add_of_nonneg_right
    (feynmanKacAdditiveFunctional_nonneg hq0 (t - s) (ContinuousPath.shift s omega))

omit [SecondCountableTopology alpha] in
/-- The increment of the accumulated potential is the accumulated potential of the shifted
path. -/
theorem feynmanKacAdditiveFunctional_sub {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega - feynmanKacAdditiveFunctional q s omega =
      feynmanKacAdditiveFunctional q (t - s) (ContinuousPath.shift s omega) := by
  have hadd := feynmanKacAdditiveFunctional_add hq hq0 hqC s (t - s) omega
  rw [add_tsub_cancel_of_le hst] at hadd
  linarith only [hadd]

/-- Finite-time perturbation formula for the Feynman--Kac operators on bounded real
observables. -/
theorem IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y *
        IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
        ∂(P (Real.toNNReal s) x) := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let H : ℝ × ContinuousPath alpha → ℝ := fun p ↦
    q (p.2 (Real.toNNReal p.1)) *
      Real.exp (-(feynmanKacAdditiveFunctional q t p.2 -
        feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) * f (p.2 t)
  have hevalJoint : Measurable fun p : ℝ × ContinuousPath alpha ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAs : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAt : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q t p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.comp measurable_snd
  have hH : StronglyMeasurable H := by
    exact (((hq.comp hevalJoint).mul ((hAt.sub hAs).neg.exp)).mul
      ((hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).comp
        measurable_snd)).stronglyMeasurable
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hHbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ))
      (omega : ContinuousPath alpha) : ‖H (s, omega)‖ ≤ C * D := by
    have hsNN : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hAdiff : 0 ≤ feynmanKacAdditiveFunctional q t omega -
        feynmanKacAdditiveFunctional q (Real.toNNReal s) omega :=
      sub_nonneg.mpr (feynmanKacAdditiveFunctional_mono hq hq0 hqC hsNN omega)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 _),
      abs_of_pos (Real.exp_pos _)]
    calc
      q (omega (Real.toNNReal s)) * Real.exp (-_) * |f (omega t)| ≤
          C * 1 * D := by
        exact mul_le_mul
          (mul_le_mul (hqC _)
            ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr hAdiff))
            (Real.exp_pos _).le hC) (hfD _) (abs_nonneg _) (mul_nonneg hC zero_le_one)
      _ = C * D := by ring
  have hProdInt : Integrable (Function.uncurry fun (s : ℝ)
      (omega : ContinuousPath alpha) ↦ H (s, omega))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod mu) := by
    refine Integrable.of_bound hH.aestronglyMeasurable (C * D) ?_
    change ∀ᵐ p : ℝ × ContinuousPath alpha
      ∂((volume.restrict (Ioc (0 : ℝ) t)).prod mu), ‖H p‖ ≤ C * D
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hH.norm.measurable measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ hHbound s ⟨hs.1.le, hs.2⟩ omega
  have hInner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      ∫ omega, H (s, omega) ∂mu =
        ∫ y, q y * IsConservative.feynmanKac P hP q
          (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let W : ContinuousPath alpha → ℝ := fun omega ↦ q (omega u)
    let F : ContinuousPath alpha → ℝ := fun eta ↦
      Real.exp (-feynmanKacAdditiveFunctional q r eta) * f (eta r)
    have hu : u ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) u] W :=
      (hq.comp (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := alpha) u)).stronglyMeasurable
    have hF : StronglyMeasurable F := by
      exact (((stronglyMeasurable_feynmanKacAdditiveFunctional hq r).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) r))).stronglyMeasurable
    have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
      intro eta
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 r eta))) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hfD _)
    have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift u omega)) mu :=
      Integrable.of_bound
        (((hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u))
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ hFbound _)
    have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift u omega)) mu := by
      refine Integrable.of_bound
        ((((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)).mul
          (hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u)))
          ).aestronglyMeasurable) (C * D) ?_
      exact Eventually.of_forall fun omega ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
        exact mul_le_mul (hqC _) (hFbound _) (norm_nonneg _) hC
    have hcond := hFeller.continuousProcess_condExp_shift P hP hK x u F hF D hFbound
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
    have hfactor : (fun omega ↦ H (s, omega)) =
        fun omega ↦ W omega * F (ContinuousPath.shift u omega) := by
      funext omega
      dsimp only [H, W, F, u, r]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hu,
        feynmanKacAdditiveFunctional_sub hq hq0 hqC hu]
      ring
    rw [hfactor]
    calc
      (∫ omega, W omega * F (ContinuousPath.shift u omega) ∂mu) =
          ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift u eta)|
            ContinuousPath.canonicalFiltration (alpha := alpha) u] omega ∂mu := by
              rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)]
      _ = ∫ omega, W omega *
            (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega u)) ∂mu := by
              refine integral_congr_ae (hpull.trans ?_)
              exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
      _ = ∫ omega, q (omega u) * IsConservative.feynmanKac P hP q r f (omega u) ∂mu := by
            rfl
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q r f y ∂(P u x) := by
            simpa only [mu] using!
              (hFeller.integral_eval_continuousProcess_of_measurable P hP hK u x
                (hq.mul (IsConservative.measurable_feynmanKac P hP hq r hf)))
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q
            (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by rfl
  have hPath : (∫ omega, f (omega t) ∂mu) -
      IsConservative.feynmanKac P hP q t f x =
        ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := by
    have hPlain : Integrable (fun omega : ContinuousPath alpha ↦ f (omega t)) mu :=
      Integrable.of_bound
        (((hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t)).stronglyMeasurable
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
            rw [Real.norm_eq_abs]
            exact hfD _)
    have hWeighted : Integrable (fun omega : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) mu :=
      have hmeasWeighted : StronglyMeasurable fun omega : ContinuousPath alpha ↦
          Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) := by
        have hmeas : Measurable fun omega : ContinuousPath alpha ↦
            Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) :=
          ((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
            (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))
        exact hmeas.stronglyMeasurable
      Integrable.of_bound hmeasWeighted.aestronglyMeasurable D (Eventually.of_forall fun omega ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_right
            ((Real.exp_le_one_iff).mpr
              (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)).trans
            (by simpa only [one_mul] using hfD _))
    change (∫ omega, f (omega t) ∂mu) -
      (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) ∂mu) = _
    rw [← integral_sub hPlain hWeighted]
    refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
    change f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
      ∫ s in (0 : ℝ)..t, H (s, omega)
    have halg : f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
        (1 - Real.exp (-feynmanKacAdditiveFunctional q t omega)) * f (omega t) := by ring
    rw [halg, one_sub_exp_neg_feynmanKacAdditiveFunctional hq hq0 hqC,
      ← intervalIntegral.integral_mul_const]
  have hEval := hFeller.integral_eval_continuousProcess_of_measurable P hP hK t x hf
  calc
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
        (∫ omega, f (omega t) ∂mu) - IsConservative.feynmanKac P hP q t f x := by
          rw [hEval]
    _ = ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := hPath
    _ =
        ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu := by
          calc
            (∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu) =
                ∫ omega, (∫ s in Ioc (0 : ℝ) t, H (s, omega)) ∂mu := by
                  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
                  exact intervalIntegral.integral_of_le t.coe_nonneg
            _ = ∫ s in Ioc (0 : ℝ) t, ∫ omega, H (s, omega) ∂mu :=
              (integral_integral_swap hProdInt).symm
            _ = ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu :=
              (intervalIntegral.integral_of_le t.coe_nonneg).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ y, q y *
          IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            rw [uIcc_of_le t.coe_nonneg] at hs
            exact hInner s hs


end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le


