-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTC
-- name    : liuyao_ca_fd889115_k1_Analysis_FTC
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:30.453077+00:00
-- url     : https://prove2.me/theorems/bcbc3689-1489-45ff-88b3-e76a8cec1c25
-- title:
--   Computable analysis · FTC · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FTC.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Effective fundamental theorem of calculus

This file contains numerical comparison and stabilization lemmas for existing
FTC algorithms. The mathematical law for an arbitrary supplied integral is
`Integral.HasIntegral.ftc` in `IntegralFTC`. Numerical validity and an
endpoint comparison alone do not establish `Integral.HasIntegral`.
-/

namespace ComputableAnalysis

namespace FTC

theorem one_div_den_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    1 / (((q.den + 1 : Nat) : Rat)) <= q := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos q.den)
  have hnumpos : 0 < q.num := rat_num_pos_of_pos hq
  have hnumgeInt : (1 : Int) <= q.num := by omega
  have hnumge : (1 : Rat) <= (q.num : Rat) := by
    exact_mod_cast hnumgeInt
  have hqd :
      q * d = (q.num : Rat) + q := by
    dsimp [d]
    have hden := rat_den_mul_self q
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hqd_ge_one : 1 <= q * d := by
    rw [hqd]
    grind [Rat.le_of_lt hq]
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= q * d := hqd_ge_one
  · exact hdpos

theorem one_div_nat_antitone {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (hnm : n <= m) :
    (1 / (m : Rat)) <= 1 / (n : Rat) := by
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * (m : Rat))
  · calc
      (1 / (m : Rat)) * ((n : Rat) * (m : Rat)) = (n : Rat) := by
        have hmne : (m : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (m : Rat) := by
        exact_mod_cast hnm
      _ = (1 / (n : Rat)) * ((n : Rat) * (m : Rat)) := by
        have hnne : (n : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hn) ((Rat.natCast_pos).2 hm)

def requestedPrecision (n : Nat) : QPos :=
  if hn : n = 0 then
    { val := 1, property := by decide +kernel }
  else
    { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

theorem requestedPrecision_positive (n : Nat) :
    0 < (requestedPrecision n).val := by
  by_cases hn : n = 0
  · simp [requestedPrecision, hn]
    decide +kernel
  · simp [requestedPrecision, hn]
    exact one_div_nat_pos (Nat.pos_of_ne_zero hn)

theorem requestedPrecision_le_one (n : Nat) :
    (requestedPrecision n).val <= 1 := by
  by_cases hn : n = 0
  · simp [requestedPrecision, hn]
  · rw [requestedPrecision, dif_neg hn]
    change 1 / (n : Rat) <= 1
    have h := one_div_nat_antitone (n := 1) (m := n)
      (by decide +kernel) (Nat.pos_of_ne_zero hn)
      (Nat.one_le_iff_ne_zero.mpr hn)
    calc
      1 / (n : Rat) <= 1 / (1 : Rat) := h
      _ = 1 := by decide +kernel

theorem requestedPrecision_antitone {n m : Nat} (hnm : n <= m) :
    (requestedPrecision m).val <= (requestedPrecision n).val := by
  by_cases hn : n = 0
  · simp [requestedPrecision, hn]
    exact requestedPrecision_le_one m
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmpos : 0 < m := Nat.lt_of_lt_of_le hnpos hnm
    have h := one_div_nat_antitone hnpos hmpos hnm
    simpa [requestedPrecision, hn, Nat.ne_of_gt hmpos] using h

def riemannComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    riemannLeftInterval dF a b
      (h.chooseN eps)
      (h.chooseEvalPrecision eps)

def endpointComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    endpointDifferenceInterval F a b (h.chooseEvalPrecision eps)

def riemannRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealCompute where
  compute := riemannComputeOfEffectiveFTC h

def endpointRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealCompute where
  compute := endpointComputeOfEffectiveFTC h

/-- Agreement between a scheduled endpoint-difference algorithm and the
canonical endpoint-difference raw real.

An `EffectiveFTC` chooses an endpoint evaluation precision as part of its
finite schedule.  To turn the scheduled FTC bridge into the canonical
endpoint formula `F(b)-F(a)`, we separately prove that the scheduled endpoint
raw real is a valid representative of the canonical endpoint-difference
algorithm. -/
structure EndpointScheduleAgreement
    (F : RealFunRaw) (a b : Rat) (scheduledEndpoint : RealCompute) where
  endpoint_valid :
    RealCompute.ValidCompute (endpointDifferenceCompute F a b)
  scheduled_valid : scheduledEndpoint.Valid
  equivalent :
    scheduledEndpoint.Equiv
      (endpointDifferenceRaw F a b endpoint_valid)

namespace EndpointScheduleAgreement

theorem endpoint_raw_valid
    {F : RealFunRaw} {a b : Rat} {scheduledEndpoint : RealCompute}
    (h : EndpointScheduleAgreement F a b scheduledEndpoint) :
    (endpointDifferenceRaw F a b h.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealCompute.Valid] using h.endpoint_valid

end EndpointScheduleAgreement

/-- Build endpoint-schedule agreement for an `EffectiveFTC` when its endpoint
precision choices are a cofinal monotone stage schedule for the canonical
endpoint-difference raw real. -/
theorem endpointScheduleAgreement_of_effectiveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (requestedPrecision n) = sigma.stage n) :
    EndpointScheduleAgreement F a b (endpointRawOfEffectiveFTC h) := by
  let endpoint : RealCompute := endpointDifferenceRaw F a b hendpoint
  have hendpointValid : endpoint.Valid := by
    simpa [endpoint, endpointDifferenceRaw, RealCompute.Valid] using hendpoint
  refine
    { endpoint_valid := hendpoint
      scheduled_valid := ?_
      equivalent := ?_ }
  · have hsched := RealCompute.schedule_valid endpoint hendpointValid sigma
    have hcompute :
        endpointComputeOfEffectiveFTC h =
          fun n => endpointDifferenceCompute F a b (sigma.stage n) := by
      funext n
      simp [endpointComputeOfEffectiveFTC, endpointDifferenceCompute, hsigma]
    simpa [endpointRawOfEffectiveFTC, RealCompute.Valid, RealCompute.schedule,
      endpoint, endpointDifferenceRaw, endpointDifferenceCompute,
      hcompute] using hsched
  · intro n
    have hall := RealCompute.allStagesOverlap_refl endpoint hendpointValid
      (sigma.stage n) n
    have hover := (RealCompute.compareAt_overlap_iff endpoint endpoint
      (sigma.stage n) n).1 hall
    apply (RealCompute.compareAt_overlap_iff
      (endpointRawOfEffectiveFTC h)
      (endpointDifferenceRaw F a b hendpoint) n n).2
    simpa [endpointRawOfEffectiveFTC, endpointComputeOfEffectiveFTC,
      endpoint, endpointDifferenceRaw, endpointDifferenceCompute,
      endpointDifferenceInterval, hsigma] using hover

/-- Static-dyadic endpoint-schedule agreement is the same endpoint schedule
agreement after forgetting to `EffectiveFTC`. -/
theorem endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (requestedPrecision n) = sigma.stage n) :
    EndpointScheduleAgreement F a b
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) :=
  endpointScheduleAgreement_of_effectiveFTC_stageSchedule
    h.toEffectiveFTC hendpoint sigma hsigma

/-- Build endpoint-schedule agreement for a derivative-bound FTC certificate
when its endpoint precision choices are a cofinal monotone stage schedule for
the canonical endpoint-difference raw real. -/
theorem endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) = sigma.stage n) :
    EndpointScheduleAgreement F a b h.endpointRaw := by
  let endpoint : RealCompute := endpointDifferenceRaw F a b hendpoint
  have hendpointValid : endpoint.Valid := by
    simpa [endpoint, endpointDifferenceRaw, RealCompute.Valid] using hendpoint
  refine
    { endpoint_valid := hendpoint
      scheduled_valid := ?_
      equivalent := ?_ }
  · have hsched := RealCompute.schedule_valid endpoint hendpointValid sigma
    have hcompute :
        h.endpointCompute =
          fun n => endpointDifferenceCompute F a b (sigma.stage n) := by
      funext n
      simp [DerivativeBoundFTC.endpointCompute,
        DerivativeBoundFTC.endpointInterval, endpointDifferenceCompute, hsigma]
    simpa [DerivativeBoundFTC.endpointRaw, RealCompute.Valid, RealCompute.schedule,
      endpoint, endpointDifferenceRaw, endpointDifferenceCompute,
      hcompute] using hsched
  · intro n
    have hall := RealCompute.allStagesOverlap_refl endpoint hendpointValid
      (sigma.stage n) n
    have hover := (RealCompute.compareAt_overlap_iff endpoint endpoint
      (sigma.stage n) n).1 hall
    apply (RealCompute.compareAt_overlap_iff
      h.endpointRaw
      (endpointDifferenceRaw F a b hendpoint) n n).2
    simpa [DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      DerivativeBoundFTC.endpointInterval, endpoint, endpointDifferenceRaw,
      endpointDifferenceCompute, endpointDifferenceInterval, hsigma] using hover

/-- Candidate-derivative endpoint-schedule agreement, by conversion to the
derivative-bound FTC certificate. -/
theorem endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Curvature endpoint-schedule agreement, by conversion to the
derivative-bound FTC certificate. -/
theorem endpointScheduleAgreement_of_curvatureFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Convex endpoint-schedule agreement, by conversion to the derivative-bound
FTC certificate. -/
theorem endpointScheduleAgreement_of_convexFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

/-- Concave endpoint-schedule agreement, by conversion to the derivative-bound
FTC certificate. -/
theorem endpointScheduleAgreement_of_concaveFTC_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision (precisionAtStage n) =
          sigma.stage n) :
    EndpointScheduleAgreement F a b h.toDerivativeBoundFTC.endpointRaw :=
  endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
    h.toDerivativeBoundFTC hendpoint sigma hsigma

def integralPlanOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> Integral.Plan :=
  fun n =>
    let eps := requestedPrecision n
    { subdivisions := h.chooseN eps,
      evalPrecision := h.chooseEvalPrecision eps }

def integralPlanOfStaticDyadicEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) : Nat -> Integral.Plan :=
  fun n =>
    let eps := requestedPrecision n
    { subdivisions := Integral.staticDyadicSubdivisions (h.chooseStage eps),
      evalPrecision := h.chooseEvalPrecision eps }

theorem integralPlanOfStaticDyadicEffectiveFTC_eq_toEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    integralPlanOfStaticDyadicEffectiveFTC h =
      integralPlanOfEffectiveFTC h.toEffectiveFTC := by
  funext n
  simp [integralPlanOfStaticDyadicEffectiveFTC, integralPlanOfEffectiveFTC,
    StaticDyadicEffectiveFTC.toEffectiveFTC]

theorem riemannComputeOfEffectiveFTC_eq_integralPlan
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) (n : Nat) :
    riemannComputeOfEffectiveFTC h n =
      riemannLeftInterval dF a b
        ((integralPlanOfEffectiveFTC h n).subdivisions)
        ((integralPlanOfEffectiveFTC h n).evalPrecision) := by
  simp [riemannComputeOfEffectiveFTC, integralPlanOfEffectiveFTC]

theorem integral_compute_eq_riemannComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h) :
    (Integral.sampleValue dF a b c).compute =
      riemannComputeOfEffectiveFTC h := by
  funext n
  simp [Integral.sampleValue, Integral.Certificate.realCompute,
    Integral.Raw.toRealCompute, Integral.Raw.compute, Integral.algorithm,
    riemannComputeOfEffectiveFTC, integralPlanOfEffectiveFTC, hplan]

theorem integral_valid_of_construction
    {f : RealFunRaw} {a b : Rat}
    (c : Integral.SampleConstruction f a b) :
    (Integral.sampleValue f a b c).Valid := by
  have hv := c.certificate.valid
  change RealCompute.ValidCompute (Integral.algorithm f a b c.plan).compute at hv
  exact hv

/-- General effective FTC, in computable-real form.

An `EffectiveFTC` certificate already says that, for every rational precision,
some finite Riemann sum for `dF` is close to the endpoint difference
`F(b)-F(a)`.  This theorem packages that certificate as equivalence of two
raw real algorithms: the scheduled Riemann sums and the scheduled endpoint
differences overlap at every requested stage. -/
theorem effectiveFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) :
    (riemannRawOfEffectiveFTC h).Equiv (endpointRawOfEffectiveFTC h) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hgood := h.good (requestedPrecision n)
  exact (RealCompute.compareAt_overlap_iff
    (riemannRawOfEffectiveFTC h) (endpointRawOfEffectiveFTC h) n n).2 hgood.1

/-! A scheduled FTC need not produce nested boxes at its public stage index.
The following adapter makes the finite Riemann computation into a valid raw
real by prefix-stabilizing it against the canonical endpoint difference. -/

theorem effectiveFTC_riemannRaw_equiv_endpointDifference_of_endpointAgreement
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (hriemann : (riemannRawOfEffectiveFTC h).Valid)
    (agreement : EndpointScheduleAgreement F a b
      (endpointRawOfEffectiveFTC h)) :
    (riemannRawOfEffectiveFTC h).Equiv
      (endpointDifferenceRaw F a b agreement.endpoint_valid) := by
  exact RealCompute.equiv_trans hriemann agreement.scheduled_valid
    (by simpa [endpointDifferenceRaw, RealCompute.Valid] using agreement.endpoint_valid)
    (effectiveFTC_equiv_endpoint h) agreement.equivalent

def effectiveFTCStabilizedRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (radius : Nat -> Rat) : RealCompute :=
  RealCompute.prefixStabilize (riemannRawOfEffectiveFTC h) radius

theorem effectiveFTCStabilizedRaw_valid
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (hriemann : (riemannRawOfEffectiveFTC h).Valid)
    (agreement : EndpointScheduleAgreement F a b
      (endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hwidth : RealCompute.WidthsShrinkToZero
      (riemannRawOfEffectiveFTC h).compute)
    (hradius : forall n,
      ((endpointDifferenceRaw F a b agreement.endpoint_valid).compute n).width
        <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    (effectiveFTCStabilizedRaw h radius).Valid := by
  unfold effectiveFTCStabilizedRaw
  apply RealCompute.prefixStabilize_valid
    (candidate := riemannRawOfEffectiveFTC h)
    (anchor := endpointDifferenceRaw F a b agreement.endpoint_valid)
    (radius := radius)
  · exact hwidth
  · simpa [endpointDifferenceRaw, RealCompute.Valid] using agreement.endpoint_valid
  · exact effectiveFTC_riemannRaw_equiv_endpointDifference_of_endpointAgreement
      h hriemann agreement
  · exact hradius
  · exact hradius_shrinks

theorem effectiveFTCStabilizedRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (hriemann : (riemannRawOfEffectiveFTC h).Valid)
    (agreement : EndpointScheduleAgreement F a b
      (endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hradius : forall n,
      ((endpointDifferenceRaw F a b agreement.endpoint_valid).compute n).width
        <= radius n) :
    (effectiveFTCStabilizedRaw h radius).Equiv
      (endpointDifferenceRaw F a b agreement.endpoint_valid) := by
  unfold effectiveFTCStabilizedRaw
  apply RealCompute.prefixStabilize_equiv_anchor
    (candidate := riemannRawOfEffectiveFTC h)
    (anchor := endpointDifferenceRaw F a b agreement.endpoint_valid)
    (radius := radius)
  · simpa [endpointDifferenceRaw, RealCompute.Valid] using agreement.endpoint_valid
  · exact effectiveFTC_riemannRaw_equiv_endpointDifference_of_endpointAgreement
      h hriemann agreement
  · exact hradius

/-- FTC bridge for a chosen integral construction.

If the integral construction uses exactly the Riemann-sum plan supplied by an
`EffectiveFTC` certificate, then the constructed integral is equivalent to the
scheduled endpoint-difference raw algorithm from that certificate.  This is the
main reusable form for later equivalence proofs: the analytic work is isolated
in the `EffectiveFTC` certificate, while the integral side only has to expose
the same finite-stage schedule. -/
theorem effectiveFTC_integral_equiv_scheduledEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h) :
    (Integral.sampleValue dF a b c).Equiv (endpointRawOfEffectiveFTC h) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hgood := h.good (requestedPrecision n)
  apply (RealCompute.compareAt_overlap_iff
    (Integral.sampleValue dF a b c) (endpointRawOfEffectiveFTC h) n n).2
  rw [integral_compute_eq_riemannComputeOfEffectiveFTC h c hplan]
  exact hgood.1

/-- Static-dyadic effective FTC, in computable-real form. -/
theorem staticDyadicEffectiveFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    (riemannRawOfEffectiveFTC h.toEffectiveFTC).Equiv
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) :=
  effectiveFTC_equiv_endpoint h.toEffectiveFTC

/-- FTC bridge for a construction using the static dyadic schedule. -/
theorem staticDyadicEffectiveFTC_integral_equiv_scheduledEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h) :
    (Integral.sampleValue dF a b c).Equiv
      (endpointRawOfEffectiveFTC h.toEffectiveFTC) := by
  apply effectiveFTC_integral_equiv_scheduledEndpoint h.toEffectiveFTC c
  rw [← integralPlanOfStaticDyadicEffectiveFTC_eq_toEffectiveFTC h]
  exact hplan

/-- Transport the scheduled FTC bridge to the canonical endpoint-difference
algorithm when that endpoint schedule has separately been proved equivalent to
the canonical endpoint computation.

This theorem is intentionally split from `effectiveFTC_integral_equiv_scheduledEndpoint`:
cofinality or monotonicity of the endpoint precision schedule is representation
specific, so later files can prove it in the form most convenient for the
function `F`. -/
theorem effectiveFTC_definiteIntegralEqualsEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (hplan : c.plan = integralPlanOfEffectiveFTC h)
    (hscheduledEndpoint : (endpointRawOfEffectiveFTC h).Valid)
    (hendpoint_equiv :
      (endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw F a b hendpoint)) :
    CandidateEqualsEndpointDifference F dF a b c hendpoint := by
  exact RealCompute.equiv_trans
    (integral_valid_of_construction c)
    hscheduledEndpoint
    hendpoint
    (effectiveFTC_integral_equiv_scheduledEndpoint h c hplan)
    hendpoint_equiv

/-- Definite-integral FTC bridge using the packaged endpoint-schedule
agreement. -/
theorem effectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hplan : c.plan = integralPlanOfEffectiveFTC h)
    (endpoint :
      EndpointScheduleAgreement F a b (endpointRawOfEffectiveFTC h)) :
    CandidateEqualsEndpointDifference
      F dF a b c endpoint.endpoint_valid :=
  effectiveFTC_definiteIntegralEqualsEndpoint
    h c endpoint.endpoint_valid hplan
    endpoint.scheduled_valid endpoint.equivalent

/--
Transport the effective FTC certificate directly from an explicit endpoint
stage schedule to the canonical endpoint-difference computation.

The schedule equality is a finite implementation certificate: at each
requested stage it identifies the precision selected by `h` with the stage
used by `sigma`.  This composes that transport with the existing Riemann-plan
bridge, so callers need not manually unpack an `EndpointScheduleAgreement`.
-/
theorem effectiveFTC_definiteIntegralEqualsEndpoint_of_stageSchedule
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (hplan : c.plan = integralPlanOfEffectiveFTC h)
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (requestedPrecision n) = sigma.stage n) :
    CandidateEqualsEndpointDifference F dF a b c hendpoint := by
  exact effectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    h c hplan
    (endpointScheduleAgreement_of_effectiveFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Static-dyadic specialization of the definite-integral FTC bridge. -/
theorem staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h)
    (hscheduledEndpoint : (endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint_equiv :
      (endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw F a b hendpoint)) :
    CandidateEqualsEndpointDifference F dF a b c hendpoint := by
  exact RealCompute.equiv_trans
    (integral_valid_of_construction c)
    hscheduledEndpoint
    hendpoint
    (staticDyadicEffectiveFTC_integral_equiv_scheduledEndpoint h c hplan)
    hendpoint_equiv

/-- Static-dyadic specialization using the packaged endpoint-schedule
agreement. -/
theorem staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b)
    (c : Integral.SampleConstruction dF a b)
    (hplan : c.plan = integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint :
      EndpointScheduleAgreement F a b
        (endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    CandidateEqualsEndpointDifference
      F dF a b c endpoint.endpoint_valid :=
  staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
    h c endpoint.endpoint_valid hplan
    endpoint.scheduled_valid endpoint.equivalent

/-!
## Finite partition endpoint transport

These declarations expose the finite telescoping step at the FTC layer.  A
caller supplies one rational interval box for each cell; the boxes are folded
in `Nat` order and the result is shown to contain the endpoint box for the
whole partition.  The adjacent-interval theorem concatenates two such finite
folds.  No limiting partition, completed real, or completeness principle is
used.
-/

/-- Fold one supplied rational interval box for every cell of a finite
partition.  The zero interval makes the computation total outside the finite
`List.range` that is actually traversed. -/
def finitePartitionEndpointStageSum
    {a b : Rat} (P : RationalPartition a b)
    (cellBox : (k : Nat) -> k < P.pieces -> QInterval) : QInterval :=
  (List.range P.pieces).foldl
    (fun acc k => QInterval.addInterval acc
      (if hk : k < P.pieces then cellBox k hk else { lo := 0, hi := 0 }))
    { lo := 0, hi := 0 }

/-- A finite cellwise endpoint enclosure telescopes to the endpoint enclosure
of the entire rational partition.  `cell_contains` is the only
function-specific obligation; the assembly itself is a reusable finite
certificate. -/
theorem finitePartitionEndpointStageSum_contains
    {F : RealFunRaw} {a b : Rat}
    (P : RationalPartition a b) (prec : Nat)
    (hF : F.Valid)
    (hdomain : forall i, i <= P.pieces -> F.domain (P.point i))
    (cellBox : (k : Nat) -> k < P.pieces -> QInterval)
    (cell_contains : forall k (hk : k < P.pieces),
      (cellBox k hk).ContainsInterval
        (endpointDifferenceInterval F (P.point k) (P.point (k + 1)) prec)) :
    (finitePartitionEndpointStageSum P cellBox).ContainsInterval
      (endpointDifferenceInterval F a b prec) := by
  have hsum : (finitePartitionEndpointStageSum P cellBox).ContainsInterval
      (P.endpointDifferenceSum F prec) := by
    unfold finitePartitionEndpointStageSum
    apply RationalPartition.addInterval_fold_contains (List.range P.pieces)
      (fun k => if hk : k < P.pieces then cellBox k hk else { lo := 0, hi := 0 })
      (P.endpointDifferenceTerm F prec)
      (QInterval.containsInterval_refl _)
    intro k
    unfold RationalPartition.endpointDifferenceTerm
    split
    · exact cell_contains k _
    · exact QInterval.containsInterval_refl _
  exact hsum.trans (by
    simpa [P.left_endpoint, P.right_endpoint] using
      (RationalPartition.endpointDifferenceSum_contains P F prec hF hdomain))

/-- Concatenate two finite partition folds over adjacent rational intervals.
The added boxes first telescope on `[a,b]` and `[b,c]`, then the shared
endpoint box is handled by the finite adjacent-difference certificate. -/
theorem finitePartitionEndpointStageSum_adjacent_contains
    {F : RealFunRaw} {a b c : Rat}
    (left : RationalPartition a b) (right : RationalPartition b c)
    (prec : Nat) (hF : F.Valid)
    (hleft_domain : forall i, i <= left.pieces -> F.domain (left.point i))
    (hright_domain : forall i, i <= right.pieces -> F.domain (right.point i))
    (leftBox : (k : Nat) -> k < left.pieces -> QInterval)
    (rightBox : (k : Nat) -> k < right.pieces -> QInterval)
    (hleft : forall k (hk : k < left.pieces),
      (leftBox k hk).ContainsInterval
        (endpointDifferenceInterval F (left.point k) (left.point (k + 1)) prec))
    (hright : forall k (hk : k < right.pieces),
      (rightBox k hk).ContainsInterval
        (endpointDifferenceInterval F (right.point k) (right.point (k + 1)) prec)) :
    (QInterval.addInterval
      (finitePartitionEndpointStageSum left leftBox)
      (finitePartitionEndpointStageSum right rightBox)).ContainsInterval
        (endpointDifferenceInterval F a c prec) := by
  have hleft_sum := finitePartitionEndpointStageSum_contains left prec hF
    hleft_domain leftBox hleft
  have hright_sum := finitePartitionEndpointStageSum_contains right prec hF
    hright_domain rightBox hright
  have hleft' : (finitePartitionEndpointStageSum left leftBox).ContainsInterval
      (endpointDifferenceInterval F a b prec) := by
    simpa [left.left_endpoint, left.right_endpoint] using hleft_sum
  have hright' : (finitePartitionEndpointStageSum right rightBox).ContainsInterval
      (endpointDifferenceInterval F b c prec) := by
    simpa [right.left_endpoint, right.right_endpoint] using hright_sum
  have hadd := QInterval.addInterval_contains hleft' hright'
  have hmiddle : 0 <= (F.compute b prec).width := by
    have hb : F.domain b := by
      simpa [left.right_endpoint] using
        (hleft_domain left.pieces (Nat.le_refl left.pieces))
    exact (hF b hb).1 prec
  exact hadd.trans (endpointDifferenceInterval_adjacent_additive_contains
    (F := F) (a := a) (b := b) (c := c) (prec := prec) hmiddle)

end FTC

end ComputableAnalysis


