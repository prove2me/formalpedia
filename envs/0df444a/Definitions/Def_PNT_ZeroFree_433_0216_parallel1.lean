-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0216_parallel1
-- name    : PNT_ZeroFree_433_0216_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:25:17.89766+00:00
-- url     : https://prove2.me/theorems/5ff1f140-71f0-4655-aa44-8c231edd65d1
-- title:
--   Zero-free region foundations: Eisenstein.WhittakerContinuation [0216_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.WhittakerContinuation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/WhittakerContinuation.lean#L388-L584

import Definitions.Def_PNT_ZeroFree_433_0216_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/WhittakerContinuation.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal


lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))

lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]

lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


def cuspWeightedWhittakerHeightFactor (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))


end CubicEisenstein

end

end OAI

end


