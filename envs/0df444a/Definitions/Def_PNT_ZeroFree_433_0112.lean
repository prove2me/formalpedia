-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0112
-- name    : PNT_ZeroFree_433_0112
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:25:22.955335+00:00
-- url     : https://prove2.me/theorems/01b48b32-6f52-46e5-9904-97eceb4289a8
-- title:
--   Zero-free region foundations: Eisenstein.CuspIntegration [0112]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean#L77-L759

import Definitions.Def_PNT_ZeroFree_433_0111

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean#L77-L759
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration
section
namespace OAI

noncomputable section

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def spatialTriple (x y v : ℝ) : SpatialCoordinates := ![x,y,v]
@[simp] lemma spatialTriple_zero (x y v : ℝ) : spatialTriple x y v 0=x := rfl
@[simp] lemma spatialTriple_one (x y v : ℝ) : spatialTriple x y v 1=y := rfl
@[simp] lemma spatialTriple_two (x y v : ℝ) : spatialTriple x y v 2=v := rfl

def cuspCylinderMeasure (a b : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.restrict (Set.Icc a b)).prod
    ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod
      (volume.restrict (Set.Icc 0 3)))

def cuspBoxIntegral (a b : ℝ) (f : SpatialCoordinates → ℂ) : ℂ :=
  ∫q, f (spatialTriple q.2.2 q.2.1 q.1) ∂cuspCylinderMeasure a b

lemma continuous_spatialTriple {X : Type*} [TopologicalSpace X]
    {x y v : X → ℝ} (hx : Continuous x) (hy : Continuous y) (hv : Continuous v) :
    Continuous (fun p => spatialTriple (x p) (y p) (v p)) := by
  rw [continuous_pi_iff]
  intro j
  fin_cases j <;> assumption

lemma continuous_cuspBox_integrand (f : SpatialCoordinates → ℂ) (hf : Continuous f) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1)) :=
  hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))

lemma integrable_cuspBox (f : SpatialCoordinates → ℂ) (hf : Continuous f) (a b : ℝ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have h : IntegrableOn (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (Set.Icc a b ×ˢ (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3)) volume :=
    (continuous_cuspBox_integrand f hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  simpa only [cuspCylinderMeasure,Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using h

lemma cuspBoxIntegral_add (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p+g p)=cuspBoxIntegral a b f+cuspBoxIntegral a b g :=
  integral_add (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_sub (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p-g p)=cuspBoxIntegral a b f-cuspBoxIntegral a b g :=
  integral_sub (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (a b : ℝ) :
    cuspBoxIntegral a b (fun p => c*f p)=c*cuspBoxIntegral a b f := integral_const_mul _ _

lemma cuspBoxIntegral_eq_iterated (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod _ (integrable_cuspBox f hf a b)]
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    have hc : Continuous (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v)) :=
      hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) continuous_const)
    have hi : IntegrableOn (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hi' : Integrable (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
      simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
    exact integral_prod _ hi')

lemma cuspBoxIntegral_eq_vertical (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, ∫v in a..b, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod_symm _ (integrable_cuspBox f hf a b)]
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => f (spatialTriple q.1.2 q.1.1 q.2)) :=
    hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))
  have hcI : Continuous (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v)) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hi : IntegrableOn (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
    hcI.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
  rw [integral_prod _ hi']
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]

lemma rectangle_interval_swap (f : ℝ→ℝ→ℂ) (hf : Continuous f.uncurry) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f x y)=
      ∫x in (0:ℝ)..3, ∫y in (0:ℝ)..(3*Real.sqrt 3), f x y := by
  apply intervalIntegral_intervalIntegral_swap
  have hc : Continuous (Function.uncurry (fun y x => f x y)) := hf.comp continuous_swap
  exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

def greenSecondField (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondTerm (axisSlice (upperEisensteinField s) p j)
    (axisSlice (upperEisensteinField t) p j) (p j)
def greenWronskianField (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskian (axisSlice (upperEisensteinField s) p 2)
    (axisSlice (upperEisensteinField t) p 2) (p 2)
def greenAxisDensity (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondField s t j p/(p 2:ℂ)
def greenVerticalDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenAxisDensity s t 2 p-greenWronskianField s t p/(p 2:ℂ)^2
def greenBoundaryFlux (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskianField s t p/(p 2:ℂ)

def clampHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : SpatialCoordinates :=
  spatialTriple (p 0) (p 1) (max deltaLoss (p 2))
lemma clampHeight_continuous (deltaLoss : ℝ) : Continuous (clampHeight deltaLoss) :=
  continuous_spatialTriple (continuous_apply 0) (continuous_apply 1)
    (continuous_const.max (continuous_apply 2))
lemma clampHeight_eq (deltaLoss : ℝ) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) : clampHeight deltaLoss p=p := by
  ext j
  fin_cases j <;> simp [clampHeight,spatialTriple,max_eq_right hp]

def extendAboveHeight (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  f (clampHeight deltaLoss p)
lemma extendAboveHeight_continuous (deltaLoss : ℝ) (hδ : 0<deltaLoss) (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) : Continuous (extendAboveHeight deltaLoss f) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (hf (clampHeight deltaLoss p) (lt_of_lt_of_le hδ (le_max_left _ _))).comp
    (clampHeight_continuous deltaLoss).continuousAt
lemma extendAboveHeight_eq (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (hp : deltaLoss≤p 2) : extendAboveHeight deltaLoss f p=f p := by
  rw [extendAboveHeight,clampHeight_eq deltaLoss p hp]

lemma greenSecondField_update (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) (x : ℝ) :
    greenSecondField s t j (Function.update p j x)=
      greenSecondTerm (axisSlice (upperEisensteinField s) p j)
        (axisSlice (upperEisensteinField t) p j) x := by
  simp only [greenSecondField,axisSlice_update,Function.update_self]
lemma greenWronskianField_update (s t : ℂ) (p : SpatialCoordinates) (x : ℝ) :
    greenWronskianField s t (Function.update p 2 x)=
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) x := by
  simp only [greenWronskianField,axisSlice_update,Function.update_self]

lemma greenFields_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∀j,ContinuousAt (greenAxisDensity s t j) p) ∧
    ContinuousAt (greenVerticalDensity s t) p ∧ ContinuousAt (greenBoundaryFlux s t) p := by
  have hS := actual_spatial_continuousAt s hs p hv
  have hT := actual_spatial_continuousAt t ht p hv
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  have hn : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hG (j : Fin 3) : ContinuousAt (greenSecondField s t j) p := by
    unfold greenSecondField greenSecondTerm
    simp only [axisSlice_self]
    exact (((hS.2 j).2.mul hT.1.star).sub (hS.1.mul (hT.2 j).2.star))
  have hW : ContinuousAt (greenWronskianField s t) p := by
    unfold greenWronskianField greenWronskian
    simp only [axisSlice_self]
    exact (((hS.2 2).1.mul hT.1.star).sub (hS.1.mul (hT.2 2).1.star))
  exact ⟨fun j => (hG j).div hV hn,((hG 2).div hV hn).sub (hW.div (hV.pow 2) (pow_ne_zero 2 hn)),
    hW.div hV hn⟩

lemma actual_green_fields_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    greenAxisDensity s t 0 p+greenAxisDensity s t 1 p+greenVerticalDensity s t p=
      (s*(s-2)-star (t*(t-2)))*upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3 := by
  have h := actual_eisenstein_green_density s t hs ht p hv
  simp only [Fin.sum_univ_three,add_div] at h
  calc
    _ = _ := by
      unfold greenVerticalDensity greenAxisDensity greenSecondField greenWronskianField
      ring
    _ = _ := h

lemma spatialTriple_update_zero (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple 0 y v) 0 x := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_one (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x 0 v) 1 y := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_two (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x y 0) 2 v := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]

lemma actual_green_axis_zero_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (y v : ℝ) (hv : 0<v) :
    (∫x in (0:ℝ)..3, greenAxisDensity s t 0 (spatialTriple x y v))=0 := by
  have hf : (fun x => greenAxisDensity s t 0 (spatialTriple x y v))=
      (fun x => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple 0 y v) 0)
        (axisSlice (upperEisensteinField t) (spatialTriple 0 y v) 0) x/(v:ℂ)) := by
    funext x
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_zero,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_real_period_zero s t hs ht (spatialTriple 0 y v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_axis_one_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x v : ℝ) (hv : 0<v) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), greenAxisDensity s t 1 (spatialTriple x y v))=0 := by
  have hf : (fun y => greenAxisDensity s t 1 (spatialTriple x y v))=
      (fun y => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x 0 v) 1)
        (axisSlice (upperEisensteinField t) (spatialTriple x 0 v) 1) y/(v:ℂ)) := by
    funext y
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_one,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_imag_period_zero s t hs ht (spatialTriple x 0 v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_vertical_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x y a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b, greenVerticalDensity s t (spatialTriple x y v))=
      greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have hG (v : ℝ) : greenSecondField s t 2 (spatialTriple x y v)=
      greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenSecondField_update]
  have hW (v : ℝ) : greenWronskianField s t (spatialTriple x y v)=
      greenWronskian (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenWronskianField_update]
  simp only [greenVerticalDensity,greenAxisDensity,greenBoundaryFlux,spatialTriple_two,hG,hW]
  exact actual_eisenstein_vertical_green s t hs ht (spatialTriple x y 0) a b ha hb

lemma cuspCylinder_ae_height (a b : ℝ) :
    ∀ᵐq ∂cuspCylinderMeasure a b, q.1∈Set.Icc a b :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)

lemma cuspBoxIntegral_congr (a b : ℝ) (f g : SpatialCoordinates → ℂ)
    (heq : ∀p, p 2∈Set.Icc a b→f p=g p) :
    cuspBoxIntegral a b f=cuspBoxIntegral a b g := by
  apply integral_congr_ae
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact heq (spatialTriple q.2.2 q.2.1 q.1) hq

lemma cuspBoxIntegral_extendAboveHeight (a b : ℝ) (f : SpatialCoordinates → ℂ) :
    cuspBoxIntegral a b (extendAboveHeight a f)=cuspBoxIntegral a b f :=
  cuspBoxIntegral_congr a b _ _ (fun p hp => extendAboveHeight_eq a f p hp.1)

lemma integrable_cuspBox_of_positive_continuity (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have hi := integrable_cuspBox (extendAboveHeight a f) (extendAboveHeight_continuous a ha f hf) a b
  apply hi.congr
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact extendAboveHeight_eq a f _ hq.1

lemma cuspBox_green_axis_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 0))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 0)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 0 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    simp_rw [hext,actual_green_axis_zero_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_axis_one (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 1))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 1)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 1 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    rw [rectangle_interval_swap (fun x y => f (spatialTriple x y v))
      (hf.comp (continuous_spatialTriple continuous_fst continuous_snd continuous_const))]
    simp_rw [hext,actual_green_axis_one_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_vertical (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenVerticalDensity s t))=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f := extendAboveHeight a (greenVerticalDensity s t)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  rw [cuspBoxIntegral_eq_vertical _ hf a b hab]
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  calc
    _ = ∫v in a..b, greenVerticalDensity s t (spatialTriple x y v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact extendAboveHeight_eq a _ _ (by simpa only [min_eq_left hab,spatialTriple_two] using hv.1)
    _ = _ := actual_green_vertical_integral s t hs ht x y a b ha (lt_of_lt_of_le ha hab)

def eisensteinHermitianDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3

lemma integrable_eisensteinHermitianDensity (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => eisensteinHermitianDensity s t (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  apply integrable_cuspBox_of_positive_continuity _ _ a b ha
  intro p hp
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f₀ := extendAboveHeight a (greenAxisDensity s t 0)
  let f₁ := extendAboveHeight a (greenAxisDensity s t 1)
  let f₂ := extendAboveHeight a (greenVerticalDensity s t)
  have h₀ : Continuous f₀ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  have h₁ : Continuous f₁ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  have h₂ : Continuous f₂ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  have hD : cuspBoxIntegral a b (fun p => f₀ p+f₁ p+f₂ p)=
      (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t) := by
    rw [← cuspBoxIntegral_const_mul]
    apply cuspBoxIntegral_congr
    intro p hp
    change extendAboveHeight a (greenAxisDensity s t 0) p+
      extendAboveHeight a (greenAxisDensity s t 1) p+
      extendAboveHeight a (greenVerticalDensity s t) p=_
    rw [extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,
      actual_green_fields_density s t hs ht p (lt_of_lt_of_le ha hp.1)]
    unfold eisensteinHermitianDensity
    ring
  rw [← hD,cuspBoxIntegral_add (fun p => f₀ p+f₁ p) f₂ (h₀.add h₁) h₂,
    cuspBoxIntegral_add f₀ f₁ h₀ h₁]
  rw [cuspBox_green_axis_zero s t hs ht a b ha hab,cuspBox_green_axis_one s t hs ht a b ha hab,
    cuspBox_green_vertical s t hs ht a b ha hab]
  simp only [zero_add]

lemma cuspBoxIntegral_eq_iterated_positive (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  rw [← cuspBoxIntegral_extendAboveHeight a b f,
    cuspBoxIntegral_eq_iterated _ (extendAboveHeight_continuous a ha f hf) a b hab]
  apply intervalIntegral.integral_congr
  intro v hv
  have hav : a≤v := by simpa only [min_eq_left hab] using hv.1
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  exact extendAboveHeight_eq a f _ hav

lemma eisensteinHermitianDensity_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContinuousAt (eisensteinHermitianDensity s t) p := by
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green_iterated (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*
      (∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        upperEisensteinField s (spatialTriple x y v)*star (upperEisensteinField t (spatialTriple x y v))/(v:ℂ)^3)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have h := actual_eisenstein_cylinder_green s t hs ht a b ha hab
  rw [cuspBoxIntegral_eq_iterated_positive _
    (eisensteinHermitianDensity_continuousAt s t hs ht) a b ha hab] at h
  exact h

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

theorem primePool_singleton_eq_primeSupport (G : Ideal O) :
    primePool {G} = primeSupport G := by
  simp [primePool, primeSupport]

theorem primePool_subset_sum_eq_divisors (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primePool {G})).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products, primePool_singleton_eq_primeSupport]
  exact (squarefree_divisor_sum_eq_support G hG f).symm

theorem middleTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primePool_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2 =
        X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]

theorem principalTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primePool {G}, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primePool_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primePool_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]

end

open ActualEisensteinCubic

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  rw [Finset.sum_coe_sort S (fun a => ∑ b : T, f a b.val)]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem original_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    rw [middleTruncation_eq_ideal_frequencies _ hsq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, originalPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
      else 0 else 0
  have he : originalTruncatedMiddle W rows left right a b M Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold originalTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact original_truncated_pair_expansion W K rows left right a b M Y Z lengthScale hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d.val i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold originalProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.original_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.original_product_divisor_middle deltaLoss hδ ε hε K B N M U hB hN hM hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M P h :=
      originalTruncatedMiddle_le_product_divisors W K rows left right a b M Y Z lengthScale
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, originalProductDivisorMiddleAt W K rows left right a b M P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => originalProductDivisorMiddleAt_nonneg W K rows left right a b M P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

end

end OAI

end


