-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
-- name    : LeanPool_SteinerSpanners_Dvoretzky
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:45.647667+00:00
-- url     : https://prove2.me/theorems/45d5b54f-cfa8-4e7a-a102-c80b1e2dc809
-- title:
--   Dvoretzky
-- statement:
--   Definitions and structural lemmas for Dvoretzky, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Dvoretzky.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Dvoretzky
section Helpers
open scoped NNReal Real
open MeasureTheory ProbabilityTheory
noncomputable section
lemma pi_gaussianReal_map_sum_mul {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x : ι → ℝ => ∑ i : ι, a i * x i) =
      gaussianReal 0 (NNReal.mk (∑ i : ι, (a i) ^ 2) (Finset.sum_nonneg (fun _ _ => sq_nonneg
          _))) := by
  let γ_ι : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have : IsProbabilityMeasure γ_ι := inferInstance
  have hmeas : Measurable (fun x : ι → ℝ => ∑ i : ι, a i * x i) := by fun_prop
  have : IsProbabilityMeasure (γ_ι.map (fun x : ι → ℝ => ∑ i : ι, a i * x i)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop), charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_mk]
  have h_integrand : ∀ x : ι → ℝ,
      Complex.exp (↑t * ↑(∑ i : ι, a i * x i) * Complex.I) =
      ∏ i : ι, Complex.exp (↑(t * a i) * ↑(x i) * Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [h_integrand]
  rw [integral_fintype_prod_eq_prod (f := fun i (y : ℝ) => Complex.exp (↑(t * a i) * ↑y *
      Complex.I))]
  have h_each : ∀ i : ι,
      (∫ y : ℝ, Complex.exp (↑(t * a i) * ↑y * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (- ((a i) ^ 2 * t ^ 2 / 2 : ℝ)) := by
    intro i
    have hcf := charFun_gaussianReal (μ := 0) (v := 1) (t * a i)
    rw [charFun_apply_real] at hcf
    simpa [mul_pow, mul_comm] using hcf
  simp_rw [h_each, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
def stdGaussian (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
lemma stdGaussian_map_dual (d : ℕ) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    (stdGaussian d).map L =
      gaussianReal 0 (NNReal.mk (∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  unfold stdGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (L ∘ e : (Fin d → ℝ) → ℝ) =
      fun x => ∑ k : Fin d, L (EuclideanSpace.single k 1) * x k := by
    ext x
    simp only [Function.comp_apply]
    have hx : e x = ∑ k : Fin d, x k • EuclideanSpace.single k (1 : ℝ) := by
      ext k
      simp [e, Pi.single_apply]
    rw [hx, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hfun]
  exact pi_gaussianReal_map_sum_mul _
instance instIsGaussianStdGaussian (d : ℕ) : IsGaussian (stdGaussian d) :=
  isGaussian_of_map_eq_gaussianReal (fun L => ⟨0, _, stdGaussian_map_dual d L⟩)
def matMeasure (d d₂ : ℕ) : Measure (Fin d → Fin d₂ → ℝ) :=
  Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin d₂ => gaussianReal 0 1))
instance instIsProbMatMeasure (d d₂ : ℕ) : IsProbabilityMeasure (matMeasure d d₂) := by
  unfold matMeasure
  infer_instance
def coordCLM {d : ℕ} (k : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
def smoothLpSum (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k : Fin d, ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2)
def smoothLp (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (smoothLpSum p ε z) ^ (1 / p)
def smoothLpDeriv (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ k : Fin d,
    ((smoothLpSum p ε z) ^ (1 / p - 1) * z.ofLp k *
      ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • coordCLM k
end
end Helpers
end HighDimSteinerSpanners.Proofs.Dvoretzky


