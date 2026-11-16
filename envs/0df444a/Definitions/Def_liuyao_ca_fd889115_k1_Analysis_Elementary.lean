-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Elementary
-- name    : liuyao_ca_fd889115_k1_Analysis_Elementary
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:39.149296+00:00
-- url     : https://prove2.me/theorems/55a75100-de4b-4c62-bfa3-a0fa4ba35181
-- title:
--   Computable analysis · Elementary · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Elementary.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Pi
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Extension

set_option autoImplicit true

/-!
# Elementary function branch conventions

Some inverse functions are not canonical until a branch is chosen.  We make
that choice explicit in the function definition rather than hiding it in a
global convention.
-/

namespace ComputableAnalysis

def inClosedInterval (a b x : Rat) : Prop := a <= x /\ x <= b
def allRationals (_x : Rat) : Prop := True
def positiveRationals (x : Rat) : Prop := 0 < x

/-- Data recording a named inverse-function branch.  The actual algorithms and
proofs can be built by hand for each branch. -/
structure InverseBranchConvention where
  forwardName : String
  inverseName : String
  inputDomain : Rat -> Prop
  branchDomain : Rat -> Prop

namespace InverseBranchConvention

/-- The conventional real arcsine branch:
input `[-1,1]`, output branch `[-pi/2, pi/2]`.

The output branch is represented by rational angles only here; once `pi/2` is a
certified `RealCompute.Certified`, this convention should be upgraded to a computable-real
interval condition.
-/
def arcsin : InverseBranchConvention where
  forwardName := "sin"
  inverseName := "arcsin"
  inputDomain := fun y => inClosedInterval (-1) 1 y
  branchDomain := fun _theta => True

/-- The conventional real arctangent branch:
all real inputs, output branch `(-pi/2, pi/2)`.

As above, the exact branch bound should be upgraded after `pi/2` is a certified
computable real.
-/
def arctan : InverseBranchConvention where
  forwardName := "tan"
  inverseName := "arctan"
  inputDomain := allRationals
  branchDomain := fun _theta => True

/-- The conventional real logarithm branch:
input positive rationals, output all real values. -/
def log : InverseBranchConvention where
  forwardName := "exp"
  inverseName := "log"
  inputDomain := positiveRationals
  branchDomain := allRationals

end InverseBranchConvention

namespace Elementary

def arcsinDomain (x : Rat) : Prop := inClosedInterval (-1) 1 x
def arctanDomain (_x : Rat) : Prop := True
def logDomain (x : Rat) : Prop := positiveRationals x

/-- Partial arcsine target on rational inputs.  No value is supplied outside
`[-1,1]`. -/
structure ArcsinRaw where
  compute : (x : Rat) -> arcsinDomain x -> Nat -> QInterval

/-- Partial arctangent target on rational inputs.  This one is total, but we
still record the branch convention separately. -/
structure ArctanRaw where
  compute : (x : Rat) -> arctanDomain x -> Nat -> QInterval

/-- Partial logarithm target on positive rational inputs.  No value is supplied
at `x <= 0`. -/
structure LogRaw where
  compute : (x : Rat) -> logDomain x -> Nat -> QInterval

def arcsinAsPartial (f : ArcsinRaw) : PartialRealFunRaw where
  definedAt := arcsinDomain
  compute := f.compute

def arctanAsPartial (f : ArctanRaw) : PartialRealFunRaw where
  definedAt := arctanDomain
  compute := f.compute

def logAsPartial (f : LogRaw) : PartialRealFunRaw where
  definedAt := logDomain
  compute := f.compute

/-- The proof target for a hand-built arcsine branch. -/
def ArcsinSpec (f : ArcsinRaw) : Prop :=
  forall x h, RealCompute.ValidCompute ((arcsinAsPartial f).compute x h)

/-- The proof target for a hand-built arctangent branch. -/
def ArctanSpec (f : ArctanRaw) : Prop :=
  forall x h, RealCompute.ValidCompute ((arctanAsPartial f).compute x h)

/-- The proof target for a hand-built logarithm branch. -/
def LogSpec (f : LogRaw) : Prop :=
  forall x h, RealCompute.ValidCompute ((logAsPartial f).compute x h)

/-- Legacy validity alias, retained for compatibility. Despite its name,
this declaration asserts only `LogSpec`, not an inverse law. Use the checked
`ExponentialComputations.log_exp` and `exp_log` for global inverse identities. -/
def LogInvertsExp (f : LogRaw) : Prop :=
  LogSpec f

/-- An arcsine branch should invert sine on `[-1,1]`.
The precise equation will be sharpened once sine has a real interval-regular
package over the conventional branch. -/
def ArcsinInvertsSin (f : ArcsinRaw) : Prop :=
  ArcsinSpec f

/-- An arcsine branch built by applying the interval inverse-function
construction to a monotone sine branch. -/
structure ArcsinFromMonotoneSin where
  sineBranch : InvertibleFunctionOnInterval
  inverse : InverseRaw sineBranch
  targetValue : (x : Rat) -> arcsinDomain x -> InRangeRaw sineBranch
  targetValue_equiv :
    forall x h, (targetValue x h).value.Equiv (RealCompute.ofRat x)
  target_domain : Rat -> Prop := arcsinDomain

/-- A logarithm branch built by applying the interval inverse-function
construction to a monotone exponential branch. -/
structure LogFromMonotoneExp where
  expBranch : InvertibleFunctionOnInterval
  inverse : InverseRaw expBranch
  targetValue : (x : Rat) -> logDomain x -> InRangeRaw expBranch
  targetValue_equiv :
    forall x h, (targetValue x h).value.Equiv (RealCompute.ofRat x)
  target_domain : Rat -> Prop := logDomain

/-- Legacy candidate record: interval validity alone does not certify an
integral. The actual global reciprocal computation and its integral evidence
are `ExponentialComputations.integralLog` and `integralLog_hasIntegral`. -/
structure LogFromIntegralInv where
  raw : LogRaw
  spec : LogSpec raw

namespace ArcsinFromMonotoneSin

def toRaw (branch : ArcsinFromMonotoneSin) : ArcsinRaw where
  compute := fun x h n => (branch.inverse.apply (branch.targetValue x h)).compute n

theorem toRaw_spec (branch : ArcsinFromMonotoneSin) :
    ArcsinSpec branch.toRaw := by
  intro x h
  exact branch.inverse.apply_valid (branch.targetValue x h)

/-- Conditional well-definedness of arcsine: once sine has a certified monotone
branch and every rational `y ∈[-1,1]` is certified to be in its range, the
inverse branch is a computable partial function. -/
theorem asin_well_defined (branch : ArcsinFromMonotoneSin) :
    Exists fun asin : ArcsinRaw => ArcsinSpec asin :=
  ⟨branch.toRaw, branch.toRaw_spec⟩
end ArcsinFromMonotoneSin

namespace LogFromMonotoneExp

def toRaw (branch : LogFromMonotoneExp) : LogRaw where
  compute := fun x h n => (branch.inverse.apply (branch.targetValue x h)).compute n

theorem toRaw_spec (branch : LogFromMonotoneExp) :
    LogSpec branch.toRaw := by
  intro x h
  exact branch.inverse.apply_valid (branch.targetValue x h)

theorem log_well_defined (branch : LogFromMonotoneExp) :
    Exists fun log : LogRaw => LogSpec log :=
  ⟨branch.toRaw, branch.toRaw_spec⟩
end LogFromMonotoneExp

/-- Legacy comparison proposition, not a proved agreement theorem. The
constructed global integral agreement is `ExponentialComputations.integralLog_equiv_log`. -/
def LogIntegralAgreesWithInverseExp (fromIntegral : LogFromIntegralInv)
    (fromInverse : LogFromMonotoneExp) : Prop :=
  forall x hx,
    (PartialRealFunRaw.apply
      (logAsPartial fromIntegral.raw)
      (fun y hy => fromIntegral.spec y hy)
      x hx).Equiv
      (PartialRealFunRaw.apply
        (logAsPartial fromInverse.toRaw)
        (fun y hy => fromInverse.toRaw_spec y hy)
        x hx)

def ArcsinViaInverseFunction : Prop :=
  Nonempty ArcsinFromMonotoneSin

def LogViaInverseFunction : Prop :=
  Nonempty LogFromMonotoneExp

namespace Arctan

/-- Named partial-function representation of arctangent.

Different arctangent algorithms naturally carry different domains.  For
example, the power series is used on `|x| <= 1`, while the geometric
sector-area construction is total on rational slopes. -/
structure FunctionRepresentation where
  name : String
  raw : PartialRealFunRaw

def Equivalent (f g : FunctionRepresentation) : Prop :=
  f.raw.AgreeOnOverlap g.raw

def EquivalentAllStages (f g : FunctionRepresentation) : Prop :=
  f.raw.AgreeOnOverlapAllStages g.raw

theorem equivalent_of_allStages {f g : FunctionRepresentation} :
    EquivalentAllStages f g -> Equivalent f g :=
  PartialRealFunRaw.agreeOnOverlap_of_allStages

def powerSeriesDomain (x : Rat) : Prop :=
  qabs x <= 1

/-- Arctangent by the alternating power series
`x - x^3/3 + x^5/5 - ...`, restricted to `|x| <= 1`. -/
def powerSeriesFunctionRaw : PartialRealFunRaw where
  definedAt := powerSeriesDomain
  compute := fun x _ => (arctan x).compute

theorem powerSeriesFunctionRaw_compute_eq_arctan
    (x : Rat) (h : powerSeriesDomain x) (n : Nat) :
    powerSeriesFunctionRaw.compute x h n = (arctan x).compute n := rfl

def powerSeries : FunctionRepresentation where
  name := "arctan.series"
  raw := powerSeriesFunctionRaw

def PowerSeriesSpec : Prop :=
  forall x h, RealCompute.ValidCompute (powerSeriesFunctionRaw.compute x h)

end Arctan

end Elementary

end ComputableAnalysis


