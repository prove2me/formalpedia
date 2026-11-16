-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ElementaryRational
-- name    : liuyao_ca_fd889115_k1_Analysis_ElementaryRational
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:06:47.992201+00:00
-- url     : https://prove2.me/theorems/739375a2-18c9-4376-abcc-6cbee9e4520e
-- title:
--   Computable analysis · ElementaryRational · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ElementaryRational.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FunctionSampling
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialLift
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexLogarithmApproximation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricPiRotation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions

set_option autoImplicit true

/-! Elementary sampling interfaces. Inputs are rational numbers or rational
complex numbers; represented constants are coefficients, not the function's
input domain. The normalized trigonometric samplers compute finite Taylor
prefixes at rational approximations to the fixed geometric pi coefficient.
Radian and chart representations retain their distinct coordinate names. -/
namespace ComputableAnalysis.ElementaryRational
open ComplexCompute ComplexExponentialApproximation ComplexExponentialLift

def exponentialValue (z : QComplex) : ComplexCompute := exponentialRawAt z (QComplex.normBound z)

theorem exponentialValue_valid (z : QComplex) : (exponentialValue z).Valid :=
  exponentialRawAt_valid (QComplex.normBound_nonneg z) Rat.le_refl

def exponential : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (exponentialValue z).compute

theorem exponential_valid : exponential.Valid := fun z _ => exponentialValue_valid z

def exponentialReal : PartialRealFunRaw := exponential.realPartOnRealAxis
theorem exponentialReal_valid : exponentialReal.Valid :=
  FunctionRaw.realPartOnRealAxis_valid exponential exponential_valid

private theorem abs_between {lo hi x : Rat} (hl : lo ≤ x) (hh : x ≤ hi) :
    qabs x ≤ qabs lo + qabs hi := by
  unfold qabs
  split <;> split <;> split <;> grind

private def inputBudget (z : ComplexCompute) : Rat :=
  qabs (z.compute 0).lo.re + qabs (z.compute 0).hi.re +
    (qabs (z.compute 0).lo.im + qabs (z.compute 0).hi.im)

/-- An internal finite bound from the initial box; this is not an additional
public argument or a choice of a completed complex number. -/
private def boundedInput (z : ComplexCompute) (hz : z.Valid) : BoundedInput (inputBudget z) where
  raw := z
  valid := hz
  radius_nonneg := Rat.add_nonneg (Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _))
    (Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _))
  center_normBound n := by
    have hc := QBox.center_mem (ComplexCompute.valid_ordered hz n)
    have hn := ComplexCompute.valid_nestedIn hz (Nat.zero_le n)
    have hr := abs_between (Rat.le_trans hn.1.1 hc.1.1) (Rat.le_trans hc.2.1 hn.2.1)
    have hi := abs_between (Rat.le_trans hn.1.2 hc.1.2) (Rat.le_trans hc.2.2 hn.2.2)
    exact rat_add_le_add hr hi

def pi : RealCompute := RealCompute.scaleRat 2 GeometricPiRotation.halfPi
theorem pi_valid : pi.Valid := RealCompute.scaleRat_valid GeometricPiRotation.halfPi_valid

def piAngle (r : Rat) : RealCompute := RealCompute.scaleRat r pi
theorem piAngle_valid (r : Rat) : (piAngle r).Valid := RealCompute.scaleRat_valid pi_valid

/-- The rational parameter is a multiple of pi. Every stage is finite rational
Taylor computation, including approximation of the fixed pi coefficient. -/
def piRotationInput (r : Rat) : BoundedInput (inputBudget (imaginaryAxis (piAngle r))) :=
  boundedInput (imaginaryAxis (piAngle r)) (imaginaryAxis_valid (piAngle_valid r))

def piRotationValue (r : Rat) : ComplexCompute := BoundedInput.exponential (piRotationInput r)

theorem piRotationValue_valid (r : Rat) : (piRotationValue r).Valid :=
  BoundedInput.exponential_valid _

def sinPi : PartialRealFunRaw where
  definedAt _ := True
  compute r _ := (piRotationValue r).imagPart.compute

def cosPi : PartialRealFunRaw where
  definedAt _ := True
  compute r _ := (piRotationValue r).realPart.compute

theorem sinPi_valid : sinPi.Valid := fun r _ => imagPart_valid (piRotationValue_valid r)
theorem cosPi_valid : cosPi.Valid := fun r _ => realPart_valid (piRotationValue_valid r)

def imaginaryUnit : QComplex := ⟨0,1⟩

def sineRadianValue (z : QComplex) : ComplexCompute :=
  mul (ofQComplex ⟨0,-(1/2)⟩)
    (sub (exponentialValue (QComplex.mul imaginaryUnit z))
      (exponentialValue (QComplex.neg (QComplex.mul imaginaryUnit z))))

def cosineRadianValue (z : QComplex) : ComplexCompute :=
  scaleRat (1/2) (add (exponentialValue (QComplex.mul imaginaryUnit z))
    (exponentialValue (QComplex.neg (QComplex.mul imaginaryUnit z))))

theorem sineRadianValue_valid (z : QComplex) : (sineRadianValue z).Valid :=
  mul_valid (ofQComplex_valid _) (sub_valid (exponentialValue_valid _) (exponentialValue_valid _))
theorem cosineRadianValue_valid (z : QComplex) : (cosineRadianValue z).Valid :=
  scaleRat_valid_of_nonneg (by decide +kernel) (add_valid (exponentialValue_valid _) (exponentialValue_valid _))

def sineRadian : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (sineRadianValue z).compute
def cosineRadian : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (cosineRadianValue z).compute
theorem sineRadian_valid : sineRadian.Valid := fun z _ => sineRadianValue_valid z
theorem cosineRadian_valid : cosineRadian.Valid := fun z _ => cosineRadianValue_valid z

/-- Real-axis rotation presentations, using the same certified exponential
Taylor sampler on rational imaginary-axis points. -/
def sineRadianRotation : PartialRealFunRaw where
  definedAt _ := True
  compute x _ := (exponentialValue ⟨0,x⟩).imagPart.compute
def cosineRadianRotation : PartialRealFunRaw where
  definedAt _ := True
  compute x _ := (exponentialValue ⟨0,x⟩).realPart.compute
theorem sineRadianRotation_valid : sineRadianRotation.Valid :=
  fun x _ => imagPart_valid (exponentialValue_valid ⟨0,x⟩)
theorem cosineRadianRotation_valid : cosineRadianRotation.Valid :=
  fun x _ => realPart_valid (exponentialValue_valid ⟨0,x⟩)

def sinhValue (z : QComplex) : ComplexCompute :=
  scaleRat (1/2) (sub (exponentialValue z) (exponentialValue (QComplex.neg z)))
def coshValue (z : QComplex) : ComplexCompute :=
  scaleRat (1/2) (add (exponentialValue z) (exponentialValue (QComplex.neg z)))
theorem sinhValue_valid (z : QComplex) : (sinhValue z).Valid :=
  scaleRat_valid_of_nonneg (by decide +kernel) (sub_valid (exponentialValue_valid _) (exponentialValue_valid _))
theorem coshValue_valid (z : QComplex) : (coshValue z).Valid :=
  scaleRat_valid_of_nonneg (by decide +kernel) (add_valid (exponentialValue_valid _) (exponentialValue_valid _))
def sinh : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (sinhValue z).compute
def cosh : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (coshValue z).compute
theorem sinh_valid : sinh.Valid := fun z _ => sinhValue_valid z
theorem cosh_valid : cosh.Valid := fun z _ => coshValue_valid z

abbrev logOnePlus : FunctionRaw := ComplexLogarithmApproximation.logOnePlus
abbrev localLog : FunctionRaw := ComplexLogarithmApproximation.localLog
theorem logOnePlus_valid : logOnePlus.Valid := ComplexLogarithmApproximation.logOnePlus_valid
theorem localLog_valid : localLog.Valid := ComplexLogarithmApproximation.localLog_valid

/-- A proved comparison between genuinely different input coordinates. -/
theorem logarithm_shift_agrees :
    logOnePlus.AgreeAlong localLog id (fun w => QComplex.add QComplex.one w) := by
  intro w hw hz
  have he : QComplex.sub (QComplex.add QComplex.one w) QComplex.one = w := by
    cases w
    simp only [QComplex.sub,QComplex.add,QComplex.neg,QComplex.one]
    congr 1 <;> grind
  change (ComplexLogarithmApproximation.logOnePlusRawAt w).Equiv
    (ComplexLogarithmApproximation.logOnePlusRawAt
      (QComplex.sub (QComplex.add QComplex.one w) QComplex.one))
  rw [he]
  exact equiv_refl _ (ComplexLogarithmApproximation.logOnePlusRawAt_valid hw)

abbrev squareRoot : PartialRealFunRaw := ComputableAnalysis.sqrtPartialRaw
theorem squareRoot_valid : squareRoot.Valid := by
  intro x hx
  exact ComputableAnalysis.sqrtRaw_valid x hx

def exponentialFunction : ComplexFunction := ComplexFunction.ofRaw exponential exponential_valid
def sinPiFunction : PartialRealFunction := PartialRealFunction.ofRaw sinPi sinPi_valid
def cosPiFunction : PartialRealFunction := PartialRealFunction.ofRaw cosPi cosPi_valid
def sineRadianFunction : ComplexFunction := ComplexFunction.ofRaw sineRadian sineRadian_valid
def cosineRadianFunction : ComplexFunction := ComplexFunction.ofRaw cosineRadian cosineRadian_valid
def sinhFunction : ComplexFunction := ComplexFunction.ofRaw sinh sinh_valid
def coshFunction : ComplexFunction := ComplexFunction.ofRaw cosh cosh_valid
def localLogFunction : ComplexFunction := ComplexFunction.ofRaw localLog localLog_valid
def squareRootFunction : PartialRealFunction := PartialRealFunction.ofRaw squareRoot squareRoot_valid

/-- The constructed geometric unit branch; other arctangent presentations
keep their own rational domains and can join by a proved overlap comparison. -/
def arctangentUnit : PartialRealFunRaw where
  definedAt x := 0 ≤ x ∧ x ≤ 1
  compute x _ := (ArctanGeometry.arctanGeom x).compute

theorem arctangentUnit_valid : arctangentUnit.Valid :=
  fun _ hx => ArctanGeometry.arctanGeom_valid_on_unit hx.1 hx.2

def arctangentUnitFunction : PartialRealFunction :=
  PartialRealFunction.ofRaw arctangentUnit arctangentUnit_valid

/-- Preserve the existing supplied inverse-branch construction, with rational
inputs. This does not claim to construct the missing branch evidence. -/
def arcsineOfBranch (branch : Elementary.ArcsinFromMonotoneSin) : PartialRealFunction :=
  PartialRealFunction.ofRaw (Elementary.arcsinAsPartial branch.toRaw) branch.toRaw_spec

/-- Explicit slope-coordinate sampling; these names do not identify the
stereographic parameter with a radian or normalized angle. -/
def circleSine : PartialRealFunRaw where
  definedAt _ := True
  compute t _ := (RealCompute.ofRat (RationalCircle.Trigonometry.sin t)).compute
def circleCosine : PartialRealFunRaw where
  definedAt _ := True
  compute t _ := (RealCompute.ofRat (RationalCircle.Trigonometry.cos t)).compute
theorem circleSine_valid : circleSine.Valid := fun _t _ => RealCompute.ofRat_valid _
theorem circleCosine_valid : circleCosine.Valid := fun _t _ => RealCompute.ofRat_valid _

end ComputableAnalysis.ElementaryRational


