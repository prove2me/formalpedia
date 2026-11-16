-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CompactFourier
-- name    : liuyao_ca_fd889115_k1_Distributions_CompactFourier
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T19:22:41.075214+00:00
-- url     : https://prove2.me/theorems/8747a647-23c4-4173-9e7f-40343232f868
-- title:
--   Computable analysis · CompactFourier · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/CompactFourier.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FourierQuadratureRationalProof
import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CubeAverage
import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature

set_option autoImplicit true

/-! Fourier integration for compact smooth tests at rational frequencies. -/

open ComputableAnalysis
open ComputableAnalysis.ComputableCoefficient
open ComputableAnalysis.RealApproximationOrder

namespace ComputableDistributions
namespace CompactFourier

set_option maxRecDepth 4096

open ComputableAnalysis.FourierQuadrature

export ComputableAnalysis.FourierQuadrature (boxPoint boxPoint_on_unitCube)

private def component {d : Nat} (φ : TestFunction d) (ξ : QPoint d) (cosine : Bool) : Value :=
  FourierQuadrature.component φ.support φ.toJointLipschitzSampler ξ cosine

/-- Fourier transform at a rational frequency with phase
`exp(-2π i x⋅ξ)`. The real and imaginary parts use iterated integration
over the test's rational support box. -/
def transform {d : Nat} (φ : TestFunction d) (ξ : QPoint d) : ComplexActionValue :=
  let values := FourierQuadrature.transform φ.support φ.toJointLipschitzSampler ξ
  ⟨values.1.real.preferred, values.2.real.preferred, values.1.real.valid, values.2.real.valid⟩

/-- The ordinary integral of a real test, evaluated one coordinate at a time. -/
def testIntegral {d : Nat} (φ : TestFunction d) : RealCompute :=
  (FourierQuadrature.integral φ.support φ.toJointLipschitzSampler).real.preferred

theorem transform_at_zero {d : Nat} (φ : TestFunction d) :
    ((transform φ (origin d)).re).Equiv (testIntegral φ) ∧
      ((transform φ (origin d)).im).Equiv (RealCompute.ofRat 0) :=
  FourierQuadrature.component_at_zero φ.support φ.toJointLipschitzSampler

/-- Equivalent test evaluations give the same transform on a common box. -/
theorem transform_congr {d : Nat} {φ ψ : TestFunction d} (ξ : QPoint d)
    (hbox : φ.support = ψ.support) (he : ∀ x, (φ.value x).Equiv (ψ.value x)) :
    (transform φ ξ).Equiv (transform ψ ξ) := by
  have h (cosine : Bool) : Same (component φ ξ cosine) (component ψ ξ cosine) := by
    unfold component
    rw [← hbox]
    exact FourierQuadrature.component_congr φ.support ξ cosine
      φ.toJointLipschitzSampler ψ.toJointLipschitzSampler (fun x _ => he x)
  exact ⟨h true, h false⟩

/-- Transform a complex test by complex linear extension of the real test transform. -/
def transformComplex {d : Nat} (φ : ComplexTestFunction d) (ξ : QPoint d) : ComplexActionValue :=
  let a := transform φ.re ξ
  let b := transform φ.im ξ
  ⟨RealCompute.sub a.re b.im, RealCompute.add a.im b.re,
    RealCompute.sub_valid a.re_valid b.im_valid, RealCompute.add_valid a.im_valid b.re_valid⟩

theorem transformComplex_congr {d : Nat} {φ ψ : ComplexTestFunction d} (ξ : QPoint d)
    (hboxRe : φ.re.support = ψ.re.support) (hboxIm : φ.im.support = ψ.im.support)
    (heRe : ∀ x, (φ.re.value x).Equiv (ψ.re.value x))
    (heIm : ∀ x, (φ.im.value x).Equiv (ψ.im.value x)) :
    (transformComplex φ ξ).Equiv (transformComplex ψ ξ) := by
  have hr := transform_congr ξ hboxRe heRe
  have hi := transform_congr ξ hboxIm heIm
  exact ⟨RealCompute.sub_equiv (transform φ.re ξ).re_valid (transform ψ.re ξ).re_valid
    (transform φ.im ξ).im_valid (transform ψ.im ξ).im_valid hr.1 hi.2,
    RealCompute.add_equiv (transform φ.re ξ).im_valid (transform ψ.re ξ).im_valid
    (transform φ.im ξ).re_valid (transform ψ.im ξ).re_valid hr.2 hi.1⟩

/-- Contributor target: the transform is unchanged by replacing the
support box or any other certificates, as long as the test values agree. -/
def SupportIndependenceTarget : Prop :=
  ∀ d (φ ψ : TestFunction d) (ξ : QPoint d),
    (∀ x, (φ.value x).Equiv (ψ.value x)) →
    (transform φ ξ).Equiv (transform ψ ξ)

/-- Contributor target: the iterated computation agrees with tagged
quadrature directly on the test's support box. -/
def TaggedQuadratureAgreementTarget : Prop :=
  ∀ d (φ : TestFunction d) (ξ : QPoint d) (cosine : Bool),
    HasBoxIntegral φ.support
      (fun x => RealCompute.mul (φ.value x) (GeometricTrig.sample cosine (phase ξ x)))
      (component φ ξ cosine).real.preferred

/-- Contributor target: spatial differentiation acts by multiplication by
the frequency symbol, with this file's Fourier phase convention. -/
def DifferentiationTarget : Prop :=
  ∀ d (φ : TestFunction d) (ξ : QPoint d) (i : Fin d),
    let F := transform φ ξ
    let DF := transform (φ.coordinatePartial i) ξ
    DF.re.Equiv (RealCompute.scaleRat (-2 * ξ i) (RealCompute.mul GeometricTrig.pi F.im)) ∧
    DF.im.Equiv (RealCompute.scaleRat (2 * ξ i) (RealCompute.mul GeometricTrig.pi F.re))


namespace Line

open FTCRealCalculus LipschitzQuadrature

/-- Samples of the (j)-th ordinary derivative on the rational line. -/
def derivativeSampler (φ : TestFunction 1) (j : Nat) : JointLipschitzSampler 1 where
  value x := parameter (φ.derivative (fun _ => j) x) (φ.derivative_valid (fun _ => j) x)
  bound := φ.derivativeLipschitz (fun _ => j)
  nonnegative := φ.derivativeLipschitz_nonneg _
  control := φ.derivative_control _

/-- The represented derivative value at a rational input. -/
abbrev sample (φ : TestFunction 1) (j : Nat) (t : Rat) : Value :=
  (derivativeSampler φ j).value (fun _ => t)

/-- The first three derivatives have uniform secant convergence on bounded
windows. The Lipschitz estimate for the third derivative is already part of
the test data. The older bracket law at individual rational points provides
pointwise information. -/
def HasUniformDerivatives (φ : TestFunction 1) : Prop :=
  ∀ j : Nat, j < 3 → ∀ n : Nat,
    UniformFirstOrder (sample φ j) (sample φ (j+1))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)

/-- A symmetric window radius with a positive margin outside the support. -/
def supportRadius (φ : TestFunction 1) : Rat :=
  1 + qabs (φ.support.lower 0) + qabs (φ.support.upper 0)

private theorem supportRadius_ge_one (φ : TestFunction 1) : 1 ≤ supportRadius φ := by
  have hl := qabs_nonneg (φ.support.lower 0)
  have hu := qabs_nonneg (φ.support.upper 0)
  unfold supportRadius
  grind only

private theorem sample_vanishes (φ : TestFunction 1) (j : Nat) (t : Rat)
    (ht : supportRadius φ ≤ qabs t) : Same (sample φ j t) (Value.rational 0) := by
  apply φ.derivative_vanishes_off_support
  intro h
  obtain ⟨hl, hu⟩ := h (0 : Fin 1)
  change φ.support.lower 0 ≤ t at hl
  change t ≤ φ.support.upper 0 at hu
  have h₁ := neg_qabs_le_self (φ.support.lower 0)
  have h₂ := self_le_qabs (φ.support.upper 0)
  have hn₁ := qabs_nonneg (φ.support.lower 0)
  have hn₂ := qabs_nonneg (φ.support.upper 0)
  let B := qabs (φ.support.lower 0) + qabs (φ.support.upper 0)
  have hb : qabs t ≤ B := qabs_le_of_neg_le_le (by dsimp only [B]; grind only)
    (by dsimp only [B]; grind only)
  unfold supportRadius at ht
  dsimp only [B] at hb
  grind only

private theorem derivative_bound (φ : TestFunction 1) (j : Nat) (t : Rat) :
    Small (sample φ j t) ((derivativeSampler φ j).bound * (2*supportRadius φ+1)) := by
  let R := supportRadius φ
  let f := derivativeSampler φ j
  have hR := supportRadius_ge_one φ
  have bound0 : 0 ≤ f.bound*(2*R+1) := Rat.mul_nonneg f.nonnegative (by grind only)
  by_cases h : R ≤ qabs t
  · have hz : Small (Value.rational 0) 0 := by
      simpa only [show qabs (0 : Rat) = 0 by decide +kernel] using rational_small 0
    exact (hz.congr (sample_vanishes φ j t h).symm).mono bound0
  have href : R ≤ qabs (R+1) := by have := self_le_qabs (R+1); grind only
  have ht₁ := neg_qabs_le_self t
  have ht₂ := self_le_qabs t
  have H := f.control (fun _ => t) (fun _ => R+1) (2*R+1)
    (by grind only) (fun _ => ⟨by grind only, by grind only⟩)
  refine H.congr (((Same.refl (sample φ j t)).sub (sample_vanishes φ j (R+1) href)).trans ?_)
  apply arithmetic_identity
  intro s
  simp only [sub, Value.rational, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]

/-- Each derivative has a whole-line decay certificate from its support and
Lipschitz bound. -/
def derivativeDecay (φ : TestFunction 1) (j : Nat) : LineDecay (derivativeSampler φ j) :=
  LineDecay.of_support _ (supportRadius φ)
    (Rat.mul_nonneg (derivativeSampler φ j).nonnegative (by
      have := supportRadius_ge_one φ; grind only))
    (supportRadius_ge_one φ) (derivative_bound φ j)
    (fun t ht => sample_vanishes φ j t (Rat.le_of_lt ht))

private def windowDerivativeData (φ : TestFunction 1) (j n : Nat) :
    Data (sample φ j) (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat) where
  ordered := by have := Rat.natCast_nonneg (a := n+1); grind only
  constant := (derivativeSampler φ j).bound
  nonnegative := (derivativeSampler φ j).nonnegative
  lipschitz u v _ huv _ :=
    (derivativeSampler φ j).control (fun _ => v) (fun _ => u) (v-u) (by grind only)
      (fun _ => ⟨by grind only, by grind only⟩)

/-- The derivative bounds for Melrose's proof follow from the FTC on the
fixed dyadic windows. -/
def derivatives (φ : TestFunction 1) (h : HasUniformDerivatives φ) :
    LineDerivatives (derivativeSampler φ 0) where
  first := derivativeSampler φ 1
  second := derivativeSampler φ 2
  third := derivativeSampler φ 3
  firstDecay := derivativeDecay φ 1
  secondDecay := derivativeDecay φ 2
  thirdDecay := derivativeDecay φ 3
  firstStep n := (windowDerivativeData φ 1 n).stepOfUniformFirstOrder (h 0 (by decide) n)
  secondStep n := (windowDerivativeData φ 2 n).stepOfUniformFirstOrder (h 1 (by decide) n)
  thirdStep n := (windowDerivativeData φ 3 n).stepOfUniformFirstOrder (h 2 (by decide) n)

private def clip (R t : Rat) : Rat := max (-R) (min R t)

private theorem clip_bounds {R : Rat} (hR : 0 ≤ R) (t : Rat) : -R ≤ clip R t ∧ clip R t ≤ R := by
  unfold clip
  rw [Rat.max_def, Rat.min_def]
  split <;> split <;> grind only

private theorem clip_eq {R t : Rat} (ht : qabs t ≤ R) : clip R t = t := by
  have h₁ := neg_qabs_le_self t
  have h₂ := self_le_qabs t
  unfold clip
  rw [Rat.max_def, Rat.min_def]
  split <;> split <;> grind only

private theorem clip_control {R u v δ : Rat}
    (h : u ≤ v+δ ∧ v ≤ u+δ) : qabs (clip R u-clip R v) ≤ δ := by
  apply qabs_le_of_neg_le_le
  all_goals
    unfold clip
    rw [Rat.max_def, Rat.min_def, Rat.max_def, Rat.min_def]
    split <;> split <;> split <;> (try split) <;> grind only

/-- The moment sampler clips the coordinate before multiplying. The support
identity makes its value exactly (tphi(t)) on the entire rational line. -/
def momentSampler (φ : TestFunction 1) : JointLipschitzSampler 1 where
  value x := scale (clip (supportRadius φ) (x 0)) ((derivativeSampler φ 0).value x)
  bound := supportRadius φ * (derivativeSampler φ 0).bound + (derivativeDecay φ 0).bound
  nonnegative := Rat.add_nonneg
    (Rat.mul_nonneg (by have := supportRadius_ge_one φ; grind only)
      (derivativeSampler φ 0).nonnegative) (derivativeDecay φ 0).nonnegative
  control := by
    intro u v δ hδ h
    let R := supportRadius φ
    let f := derivativeSampler φ 0
    let D := derivativeDecay φ 0
    let p := clip R (u 0)
    let q := clip R (v 0)
    have hR : 0 ≤ R := by have := supportRadius_ge_one φ; grind only
    have hp := clip_bounds hR (u 0)
    have hF := f.control u v δ hδ h
    have hV : Small (f.value v) D.bound := by
      have e : (fun _ : Fin 1 => v 0) = v := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        rw [hi]
      simpa only [e] using D.bounded (v 0)
    have hL := (scale_small hF p).mono (Rat.mul_le_mul_of_nonneg_right
      (qabs_le_of_neg_le_le hp.1 hp.2) (Rat.mul_nonneg f.nonnegative hδ))
    have hM := (scale_small hV (p-q)).mono
      (Rat.mul_le_mul_of_nonneg_right (clip_control (h 0)) D.nonnegative)
    have H := hL.add hM
    have e : R*(f.bound*δ)+δ*D.bound = (R*f.bound+D.bound)*δ := by grind only
    rw [e] at H
    apply H.congr
    apply arithmetic_identity
    intro s
    change p*((f.value u).sample s-(f.value v).sample s)+(p-q)*(f.value v).sample s =
      p*(f.value u).sample s-q*(f.value v).sample s
    grind only

theorem moment_identity (φ : TestFunction 1) (t : Rat) :
    Same ((momentSampler φ).value (fun _ => t)) (scale t (sample φ 0 t)) := by
  change Same (scale (clip (supportRadius φ) t) (sample φ 0 t)) _
  by_cases ht : qabs t ≤ supportRadius φ
  · rw [clip_eq ht]
    exact Same.refl _
  · have hz := sample_vanishes φ 0 t (by grind only)
    refine (hz.scale _).trans (Same.trans ?_ (hz.scale t).symm)
    apply arithmetic_identity
    intro s
    simp only [scale, Value.rational, Rat.mul_zero]

def momentDecay (φ : TestFunction 1) : LineDecay (momentSampler φ) :=
  LineDecay.of_support (supportRadius φ * (derivativeDecay φ 0).bound) (supportRadius φ)
    (Rat.mul_nonneg (by have := supportRadius_ge_one φ; grind only) (derivativeDecay φ 0).nonnegative)
    (supportRadius_ge_one φ)
    (fun t => by
      let p := clip (supportRadius φ) t
      have hp := clip_bounds (show 0 ≤ supportRadius φ by
        have := supportRadius_ge_one φ; grind only) t
      exact (scale_small ((derivativeDecay φ 0).bounded t) p).mono
        (Rat.mul_le_mul_of_nonneg_right (qabs_le_of_neg_le_le hp.1 hp.2)
          (derivativeDecay φ 0).nonnegative))
    (fun t ht => by
      refine (moment_identity φ t).trans (((sample_vanishes φ 0 t (Rat.le_of_lt ht)).scale t).trans ?_)
      apply arithmetic_identity
      intro s
      simp only [scale, Value.rational, Rat.mul_zero])

/-- Forward transform using the fixed dyadic whole-line quadrature. -/
def dyadicTransformAt (φ : TestFunction 1) (cosine : Bool) (x : RealCompute) (hx : x.Valid) : RealCompute :=
  lineTransformAt (derivativeDecay φ 0) cosine x hx

theorem dyadicTransformAt_valid (φ : TestFunction 1) (cosine : Bool) (x : RealCompute) (hx : x.Valid) :
    (dyadicTransformAt φ cosine x hx).Valid :=
  lineTransformAt_valid (derivativeDecay φ 0) cosine x hx

/-- At a rational frequency the dyadic forward transform is already the
compact integral as soon as a window covers the padded support. -/
theorem dyadicTransformAt_eq_window (φ : TestFunction 1) (cosine : Bool) (q : Rat) (n : Nat)
    (hn : supportRadius φ ≤ ((n+1 : Nat) : Rat)) :
    (dyadicTransformAt φ cosine (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).Equiv
      (lineCompactComponent (derivativeDecay φ 0) (fun _ => q) cosine n).real.preferred := by
  let D := derivativeDecay φ 0
  let F := parameter (dyadicTransformAt φ cosine (RealCompute.ofRat q) (RealCompute.ofRat_valid q))
    (dyadicTransformAt_valid φ cosine _ _)
  have hF : Same F (lineValue D cosine q) := lineTransformAt_rational D cosine q
  have hI : Same (lineValue D cosine q) (expandingComponent (derivativeSampler φ 0) (fun _ => q) cosine n) :=
    lineTransform_of_support D _ cosine (supportRadius φ) n hn (sample_vanishes φ 0)
  exact (hF.trans hI).trans (lineCompactComponent_agrees D _ cosine n)

/-- The reconstruction supplied by Melrose's theorem for the dyadic
transform of a compactly supported smooth line test. -/
def dyadicInverseAt (φ : TestFunction 1) (h : HasUniformDerivatives φ)
    (x : RealCompute) (hx : x.Valid) : RealCompute :=
  (inverseLineAt (derivativeDecay φ 0) (derivatives φ h) (momentDecay φ) (moment_identity φ) x hx).real.preferred

theorem dyadicInverseAt_eq (φ : TestFunction 1) (h : HasUniformDerivatives φ)
    (x : RealCompute) (hx : x.Valid) :
    (dyadicInverseAt φ h x hx).Equiv (lineSamplerAt φ.toJointLipschitzSampler x hx) :=
  inverseLineAt_eq (derivativeDecay φ 0) (derivatives φ h) (momentDecay φ) (moment_identity φ) x hx

theorem dyadicInverseAt_congr (φ : TestFunction 1) (h : HasUniformDerivatives φ)
    {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    (dyadicInverseAt φ h x hx).Equiv (dyadicInverseAt φ h y hy) :=
  inverseLineAt_congr (derivativeDecay φ 0) (derivatives φ h) (momentDecay φ) (moment_identity φ) hx hy hxy

end Line

end CompactFourier
end ComputableDistributions


