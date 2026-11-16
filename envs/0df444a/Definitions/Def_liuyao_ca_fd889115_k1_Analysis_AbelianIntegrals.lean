-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AbelianIntegrals
-- name    : liuyao_ca_fd889115_k1_Analysis_AbelianIntegrals
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:40.54361+00:00
-- url     : https://prove2.me/theorems/3f561ba0-4c08-4a42-a0d4-f7b015ea6017
-- title:
--   Computable analysis · AbelianIntegrals · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/AbelianIntegrals.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions

set_option autoImplicit true

/-!
# Abelian integrals

This file keeps abelian integrals close to their computational meaning:
evaluate an algebraic differential on rational sample points and add a
Riemann sum with explicit choices for subdivision and evaluation precision.
-/

namespace ComputableAnalysis

namespace AbelianIntegral

/-- A straight line piece in rational complex coordinates. -/
structure SegmentRaw where
  start : QComplex
  stop : QComplex
deriving Repr

/-- A circular arc piece.

The arc is recorded geometrically.  Its evaluator should later be a rational
Riemann-sum algorithm for a chosen rational parametrization of the arc, not an
appeal to imported trigonometry. -/
structure CircleArcRaw where
  center : QComplex
  radius : Rat
  start : QComplex
  stop : QComplex
  counterclockwise : Bool
deriving Repr

/-- The only path pieces we plan to support for abelian integrals: straight
segments and circular arcs. -/
inductive PathPieceRaw where
  | segment (s : SegmentRaw)
  | circular (c : CircleArcRaw)
deriving Repr

/-- A piecewise straight/circular path. -/
structure PathRaw where
  pieces : List PathPieceRaw

namespace PathRaw

def constant (_z : QComplex) : PathRaw where
  pieces := []

def segment (a b : QComplex) : PathRaw where
  pieces := [PathPieceRaw.segment { start := a, stop := b }]

def circular (center : QComplex) (radius : Rat) (start stop : QComplex)
    (counterclockwise : Bool) : PathRaw where
  pieces := [PathPieceRaw.circular {
    center := center
    radius := radius
    start := start
    stop := stop
    counterclockwise := counterclockwise
  }]

def append (p q : PathRaw) : PathRaw where
  pieces := p.pieces ++ q.pieces

end PathRaw

namespace Segment

def point (a b : QComplex) (t : Rat) : QComplex :=
  QComplex.add a (QComplex.scaleRat t (QComplex.sub b a))

def step (a b : QComplex) (n : Nat) : QComplex :=
  QComplex.scaleRat (1 / (n : Rat)) (QComplex.sub b a)

def leftParameter (n : Nat) (k : Nat) : Rat :=
  (k : Rat) * (1 / (n : Rat))

def leftPoint (a b : QComplex) (n : Nat) (k : Nat) : QComplex :=
  point a b (leftParameter n k)

end Segment

def unitInterval (t : Rat) : Prop := 0 <= t /\ t <= 1

/-- A rational parametrization of a path piece on the unit interval.

The derivative is also interval-valued, because circular arcs will usually be
computed by rational approximations rather than by exact trigonometric values. -/
structure ParametrizationRaw where
  point : (t : Rat) -> unitInterval t -> QComplex
  derivative : (t : Rat) -> unitInterval t -> Nat -> QBox

namespace ParametrizationRaw

def segment (a b : QComplex) : ParametrizationRaw where
  point := fun t _ => Segment.point a b t
  derivative := fun _ _ _ => QBox.point (QComplex.sub b a)

end ParametrizationRaw

/-- A rational differential on an algebraic branch:

`omega = numerator(z, w) / denominator(z, w) dz`

Division is not made total.  Concrete evaluators must carry whatever
denominator-separation certificate their domain needs. -/
structure DifferentialRaw where
  branch : AlgebraicFunction.Raw
  numerator : BiPoly.Coeffs
  denominator : BiPoly.Coeffs

namespace DifferentialRaw

def denominatorAt (omega : DifferentialRaw) (z w : QComplex) : QComplex :=
  BiPoly.eval omega.denominator z w

def numeratorAt (omega : DifferentialRaw) (z w : QComplex) : QComplex :=
  BiPoly.eval omega.numerator z w

def DenominatorSeparatedAt (omega : DifferentialRaw) (z : QComplex)
    (hz : omega.branch.domain z) : Prop :=
  exists n : Nat,
    let Z := QBox.point z
    let W := omega.branch.branch.compute z hz n
    let D := BiPoly.evalBox omega.denominator Z W
    D.hi.re < 0 \/ 0 < D.lo.re \/ D.hi.im < 0 \/ 0 < D.lo.im

def AdmissibleAt (omega : DifferentialRaw) (z : QComplex) : Prop :=
  omega.branch.domain z /\
    forall hz : omega.branch.domain z, DenominatorSeparatedAt omega z hz

end DifferentialRaw

/-- A raw interval algorithm for evaluating a differential at rational complex
inputs. -/
structure DifferentialEvalRaw where
  differential : DifferentialRaw
  domain : QComplex -> Prop
  compute : (z : QComplex) -> domain z -> Nat -> QBox

namespace DifferentialEvalRaw

def Valid (omega : DifferentialEvalRaw) : Prop :=
  forall z hz, ComplexCompute.Valid { compute := omega.compute z hz }

end DifferentialEvalRaw

/-- Constructive continuity for a complex interval evaluator.

This is the epsilon-delta statement in algorithmic form: given the requested
output precision `eps`, `modulus eps` is an input precision.  If two rational
complex inputs are closer than that amount, then their output boxes at scale
`eps` overlap. -/
structure ConstructiveContinuous where
  function : DifferentialEvalRaw
  modulus : Nat -> Nat
  close_outputs :
    forall z w (hz : function.domain z) (hw : function.domain w) eps,
      QComplex.coordDist z w <= (1 / ((modulus eps : Nat) : Rat)) ->
        QBox.Overlaps (function.compute z hz eps) (function.compute w hw eps)

namespace ConstructiveContinuous

def ValidEvaluator (cont : ConstructiveContinuous) : Prop :=
  cont.function.Valid

end ConstructiveContinuous

/-- The left Riemann sum for a differential along a single segment.

The domain proof is supplied for each subdivision index `k < n`, so undefined
sample points cannot be silently evaluated. -/
def riemannSegmentSum (omega : DifferentialEvalRaw) (a b : QComplex) (n : Nat)
    (hDomain : forall k : Fin n, omega.domain (Segment.leftPoint a b n k.val))
    (evalPrecision : Nat) : QBox :=
  let dz := Segment.step a b n
  (List.finRange n).foldl
    (fun acc k =>
      let z := Segment.leftPoint a b n k.val
      let hz := hDomain k
      QBox.add acc (QBox.mul (omega.compute z hz evalPrecision) (QBox.point dz)))
    QBox.zero

def intervalLeftParameter (n : Nat) (k : Nat) : Rat :=
  (k : Rat) * (1 / (n : Rat))

/-- Effective choices needed to compute an integral to a requested precision:
how many subintervals to use, and how accurately to evaluate the differential
on each subinterval. -/
structure RiemannPlan where
  subdivisions : Nat
  evalPrecision : Nat

/-- Pull back a complex differential along a rational parametrization of a path
piece.  At a rational parameter `t`, this computes
`omega(gamma(t)) * gamma'(t)` as a complex box. -/
def pullbackCompute (omega : DifferentialEvalRaw) (gamma : ParametrizationRaw)
    (hDomain : forall t h, omega.domain (gamma.point t h))
    (t : Rat) (ht : unitInterval t) (eps : Nat) : QBox :=
  let z := gamma.point t ht
  QBox.mul (omega.compute z (hDomain t ht) eps) (gamma.derivative t ht eps)

/-- The left Riemann sum of the pulled-back differential over `[0,1]`. -/
def pulledbackRiemannSum (omega : DifferentialEvalRaw) (gamma : ParametrizationRaw)
    (hDomain : forall t h, omega.domain (gamma.point t h))
    (n : Nat)
    (hUnit : forall k : Fin n, unitInterval (intervalLeftParameter n k.val))
    (evalPrecision : Nat) : QBox :=
  let dt := QBox.point (QComplex.ofRat (1 / (n : Rat)))
  (List.finRange n).foldl
    (fun acc k =>
      let t := intervalLeftParameter n k.val
      let ht := hUnit k
      QBox.add acc (QBox.mul (pullbackCompute omega gamma hDomain t ht evalPrecision) dt))
    QBox.zero

/-- Agreement target: integrating over a parametrized path piece agrees with
integrating the pulled-back differential over the real interval `[0,1]`.

This is intentionally stated as equality of the finite interval sums at a
given plan.  Convergence/nesting is handled separately by
`RiemannSumCertificate`. -/
def PullbackAgreementAt (omega : DifferentialEvalRaw) (gamma : ParametrizationRaw)
    (pathSum : Nat -> QBox)
    (hDomain : forall t h, omega.domain (gamma.point t h))
    (plan : Nat -> RiemannPlan)
    (hUnit : forall eps, forall k : Fin (plan eps).subdivisions,
      unitInterval (intervalLeftParameter (plan eps).subdivisions k.val)) : Prop :=
  forall eps,
    let p := plan eps
    QBox.Overlaps (pathSum eps)
      (pulledbackRiemannSum omega gamma hDomain p.subdivisions (hUnit eps) p.evalPrecision)

/-- A constructive segment integral.  Given the requested output precision, it
chooses a Riemann plan and computes the corresponding interval sum. -/
structure SegmentIntegralCandidate where
  differential : DifferentialEvalRaw
  start : QComplex
  stop : QComplex
  plan : Nat -> RiemannPlan
  domain :
    (eps : Nat) ->
    forall k : Fin (plan eps).subdivisions,
      differential.domain (Segment.leftPoint start stop (plan eps).subdivisions k.val)

namespace SegmentIntegralCandidate

def fromSegment (omega : DifferentialEvalRaw) (s : SegmentRaw)
    (plan : Nat -> RiemannPlan)
    (domain :
      (eps : Nat) ->
      forall k : Fin (plan eps).subdivisions,
        omega.domain (Segment.leftPoint s.start s.stop (plan eps).subdivisions k.val)) :
    SegmentIntegralCandidate where
  differential := omega
  start := s.start
  stop := s.stop
  plan := plan
  domain := domain

def compute (I : SegmentIntegralCandidate) (eps : Nat) : QBox :=
  let p := I.plan eps
  riemannSegmentSum I.differential I.start I.stop p.subdivisions (I.domain eps) p.evalPrecision

def Valid (I : SegmentIntegralCandidate) : Prop :=
  ComplexCompute.Valid { compute := I.compute }

def toComplexCompute (I : SegmentIntegralCandidate) : ComplexCompute where
  compute := I.compute

theorem toComplexCompute_valid (I : SegmentIntegralCandidate) (h : I.Valid) :
    ComplexCompute.Valid I.toComplexCompute :=
  h

end SegmentIntegralCandidate

/-- The concrete certificate that a constructive Riemann-sum algorithm really
produces a computable complex number: ordered boxes, nesting, and coordinate
widths that shrink to zero. -/
structure RiemannSumCertificate (I : SegmentIntegralCandidate) where
  ordered :
    forall eps, (I.compute eps).Ordered
  nested :
    forall eps delta, eps <= delta -> QBox.NestedIn (I.compute delta) (I.compute eps)
  widths_shrink : ComplexCompute.WidthsShrinkToZero I.compute

namespace RiemannSumCertificate

theorem valid {I : SegmentIntegralCandidate} (cert : RiemannSumCertificate I) : I.Valid :=
  ⟨fun eps => (QBox.ordered_iff_width_height_nonneg (I.compute eps)).1 (cert.ordered eps),
    fun eps delta h =>
      let hnest := cert.nested eps delta h
      ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩,
    cert.widths_shrink⟩

def complexCompute {I : SegmentIntegralCandidate} (_cert : RiemannSumCertificate I) : ComplexCompute :=
  I.toComplexCompute

theorem complexCompute_valid {I : SegmentIntegralCandidate} (cert : RiemannSumCertificate I) :
    ComplexCompute.Valid (complexCompute cert) :=
  SegmentIntegralCandidate.toComplexCompute_valid I cert.valid

end RiemannSumCertificate

/-- Effective existence of Riemann sums.

For a constructively continuous differential evaluator, suitable effective
Riemann plans should come with a `RiemannSumCertificate`, hence produce a
`ComplexCompute`.  The estimates that construct this certificate are the main work
still to prove. -/
def HasEffectiveRiemannSum (I : SegmentIntegralCandidate)
    (cont : ConstructiveContinuous) : Prop :=
  cont.function = I.differential -> Nonempty (RiemannSumCertificate I)

/-- A numerical candidate for an Abelian integral. The surrounding branch,
differential, base point, and path labels do not prove that the value integrates
the differential. Supply pullback semantics and `Integral.HasComplexIntegral`
before using the candidate as a mathematical integral. -/
structure Candidate where
  differential : DifferentialEvalRaw
  basePoint : QComplex
  pathsTo : QComplex -> PathRaw
  value : FunctionRaw

namespace Candidate

def domain (I : Candidate) : QComplex -> Prop := I.value.domain

def evalRaw (I : Candidate) (z : QComplex) (hz : I.domain z) : ComplexCompute :=
  I.value.evalRaw z hz

def Valid (I : Candidate) : Prop :=
  forall z hz, ComplexCompute.Valid (I.evalRaw z hz)

def AgreeOnCommonDomain (I J : Candidate) : Prop :=
  FunctionRaw.AgreeOnCommonDomain I.value J.value

end Candidate

/-- A named representation of an inverse to an abelian integral. -/
structure InverseRepresentation where
  integral : Candidate
  inverse : FunctionRaw
  branchDomain : QComplex -> Prop

namespace InverseRepresentation

def AgreesWithFunction (inv : InverseRepresentation) (f : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain inv.inverse f

end InverseRepresentation

end AbelianIntegral

end ComputableAnalysis


