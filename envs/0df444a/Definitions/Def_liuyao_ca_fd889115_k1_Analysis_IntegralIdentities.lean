-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralIdentities
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralIdentities
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:15:16.15818+00:00
-- url     : https://prove2.me/theorems/5c09c326-6e49-4a34-b998-f7af3be8375f
-- title:
--   Computable analysis · IntegralIdentities · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralIdentities.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanGeometry
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ElementaryFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralSpecification
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalCircle

set_option autoImplicit true

/-!
# Integral identities for elementary functions

This file records the comparison layer between geometric definitions and
definite-integral representations.  The geometric trigonometric algorithms are
not redefined here; instead, this file states the integral identities they
should satisfy once the derivative and Riemann-sum certificates are supplied.
-/

namespace ComputableAnalysis

namespace FunctionOnInterval

/-- Forget the interval-domain proof argument and expose an interval function
as a `RealFunRaw` with the interval as its domain.  Outside the interval the
compute field is a harmless dummy value; the domain field prevents it from
being used in theorem statements. -/
def toRealFunRaw (F : FunctionOnInterval) : RealFunRaw where
  domain := inDomainInterval F.lower F.upper
  compute := fun x n =>
    if hleft : F.lower <= x then
      if hright : x <= F.upper then
        F.compute x ⟨hleft, hright⟩ n
      else
        { lo := 0, hi := 0 }
    else
      { lo := 0, hi := 0 }

theorem toRealFunRaw_compute_of_mem
    (F : FunctionOnInterval) {x : Rat}
    (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    F.toRealFunRaw.compute x n = F.compute x hx n := by
  rcases hx with ⟨hleft, hright⟩
  simp [toRealFunRaw, hleft, hright]

theorem toRealFunRaw_valid (F : FunctionOnInterval) :
    F.toRealFunRaw.Valid := by
  intro x hx
  have hcompute :
      F.toRealFunRaw.compute x = F.raw.compute x (F.defined_on x hx) := by
    funext n
    rw [toRealFunRaw_compute_of_mem F hx n]
    rfl
  rw [RealFunRaw.applyCompute, hcompute]
  exact F.valid_on x (F.defined_on x hx)

/-! Stage-reindex an interval evaluator when a calculus construction needs a
finer native computation schedule.  The reindexed function is equivalent at
every rational input because `RealCompute.StageSchedule` is cofinal; this keeps
the public equal-dyadic algorithm unchanged up to `RealCompute.Equiv`. -/

def stageSchedule (F : FunctionOnInterval) (sigma : RealCompute.StageSchedule) :
    FunctionOnInterval where
  raw := {
    definedAt := F.raw.definedAt
    compute := fun x hx n => F.raw.compute x hx (sigma.stage n)
  }
  lower := F.lower
  upper := F.upper
  defined_on := F.defined_on
  valid_on := by
    intro x hx
    let hF : F.raw.definedAt x := hx
    change RealCompute.ValidCompute (fun n => F.raw.compute x hF (sigma.stage n))
    exact RealCompute.schedule_valid
      { compute := fun n => F.raw.compute x hF n } (F.valid_on x hF) sigma

theorem stageSchedule_compute_of_mem
    (F : FunctionOnInterval) (sigma : RealCompute.StageSchedule)
    {x : Rat} (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (F.stageSchedule sigma).compute x hx n =
      F.compute x hx (sigma.stage n) := by
  rfl

theorem stageSchedule_point_equiv
    (F : FunctionOnInterval) (sigma : RealCompute.StageSchedule)
    {x : Rat} (hx : inDomainInterval F.lower F.upper x) :
    (RealCompute.schedule sigma
      ({ compute := F.compute x hx } : RealCompute)).Equiv
      ({ compute := F.compute x hx } : RealCompute) := by
  exact RealCompute.equiv_symm
    (RealCompute.schedule_equiv ({ compute := F.compute x hx } : RealCompute)
      (F.valid_on x (F.defined_on x hx)) sigma)

theorem toRealFunRaw_stageSchedule_sample_overlap
    (F : FunctionOnInterval) (sigma : RealCompute.StageSchedule)
    {x : Rat} (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    QInterval.Overlaps
      (F.toRealFunRaw.compute x n)
      ((F.stageSchedule sigma).toRealFunRaw.compute x n) := by
  let R : RealCompute := { compute := F.compute x hx }
  have hR : R.Valid := F.valid_on x (F.defined_on x hx)
  have hover := (RealCompute.compareAt_overlap_iff R R n (sigma.stage n)).1
    (RealCompute.allStagesOverlap_refl R hR n (sigma.stage n))
  rw [toRealFunRaw_compute_of_mem F hx n]
  rw [toRealFunRaw_compute_of_mem (F.stageSchedule sigma) hx n]
  exact hover

theorem integral_equiv_of_stageSchedule
    (F : FunctionOnInterval) (sigma : RealCompute.StageSchedule)
    (hab : F.lower <= F.upper)
    (cf : Integral.SampleConstruction F.toRealFunRaw F.lower F.upper)
    (cg : Integral.SampleConstruction
      (F.stageSchedule sigma).toRealFunRaw F.lower F.upper)
    (hplan : cf.plan = cg.plan) :
    (Integral.sampleValue F.toRealFunRaw F.lower F.upper cf).Equiv
      (Integral.sampleValue (F.stageSchedule sigma).toRealFunRaw
        F.lower F.upper cg) := by
  apply Integral.integral_equiv_of_plan_and_sample_overlaps hab cf cg hplan
  intro n k hk
  have hpieces : 0 < (cf.plan n).subdivisions := by omega
  have hxleft : F.lower <=
      leftPoint F.lower F.upper (cf.plan n).subdivisions k := by
    have hmono := leftPoint_monotone hpieces hab
      (Nat.zero_le k)
    simpa [leftPoint_zero] using hmono
  have hxright :
      leftPoint F.lower F.upper (cf.plan n).subdivisions k <= F.upper := by
    have hmono := leftPoint_monotone hpieces hab
      (Nat.le_of_lt hk)
    calc
      leftPoint F.lower F.upper (cf.plan n).subdivisions k <=
          leftPoint F.lower F.upper (cf.plan n).subdivisions
            (cf.plan n).subdivisions := hmono
      _ = F.upper := leftPoint_endpoint hpieces
  exact toRealFunRaw_stageSchedule_sample_overlap F sigma
    ⟨hxleft, hxright⟩ (cf.plan n).evalPrecision

/-- Domain-aware endpoint telescoping for an interval-certified primitive. -/
theorem endpointDifferenceRaw_adjacent_additive
    (F : FunctionOnInterval) {a b c : Rat}
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c)
    (hc : c <= F.upper)
    (hab_valid :
      RealCompute.ValidCompute (endpointDifferenceCompute F.toRealFunRaw a b))
    (hbc_valid :
      RealCompute.ValidCompute (endpointDifferenceCompute F.toRealFunRaw b c))
    (hac_valid :
      RealCompute.ValidCompute (endpointDifferenceCompute F.toRealFunRaw a c)) :
    ((endpointDifferenceRaw F.toRealFunRaw a b hab_valid) +
      (endpointDifferenceRaw F.toRealFunRaw b c hbc_valid)).Equiv
        (endpointDifferenceRaw F.toRealFunRaw a c hac_valid) :=
  ComputableAnalysis.endpointDifferenceRaw_adjacent_additive
    F.toRealFunRaw_valid
    ⟨ha, Rat.le_trans hab (Rat.le_trans hbc hc)⟩
    ⟨Rat.le_trans ha hab, Rat.le_trans hbc hc⟩
    ⟨Rat.le_trans ha (Rat.le_trans hab hbc), hc⟩
    hab_valid hbc_valid hac_valid

end FunctionOnInterval

/-! Public domain-aware packaging for the generic stabilized FTC evaluator.
The executable integral is the prefix-stabilized Riemann computation; the
endpoint raw appears only in the finite certificate. -/

def effectiveFTCStabilizedCandidateConstructionFor
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (agreement : FTC.EndpointScheduleAgreement primitive.toRealFunRaw
      integrand.lower integrand.upper (FTC.endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hwidth : RealCompute.WidthsShrinkToZero
      (FTC.riemannRawOfEffectiveFTC h).compute)
    (hradius : forall n,
      ((endpointDifferenceRaw primitive.toRealFunRaw integrand.lower
        integrand.upper agreement.endpoint_valid).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    Integral.CandidateConstructionFor integrand where
  compute := (FTC.effectiveFTCStabilizedRaw h radius).compute
  certificate := by
    simpa [RealCompute.Valid] using
      FTC.effectiveFTCStabilizedRaw_valid h hriemann agreement radius hwidth
        hradius hradius_shrinks

def effectiveFTCStabilizedCandidateValueFor
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (agreement : FTC.EndpointScheduleAgreement primitive.toRealFunRaw
      integrand.lower integrand.upper (FTC.endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hwidth : RealCompute.WidthsShrinkToZero
      (FTC.riemannRawOfEffectiveFTC h).compute)
    (hradius : forall n,
      ((endpointDifferenceRaw primitive.toRealFunRaw integrand.lower
        integrand.upper agreement.endpoint_valid).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) : RealCompute :=
  Integral.candidateValueFor integrand
    (effectiveFTCStabilizedCandidateConstructionFor h agreement radius hriemann hwidth
      hradius hradius_shrinks)

theorem effectiveFTCStabilizedCandidateValueFor_valid
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (agreement : FTC.EndpointScheduleAgreement primitive.toRealFunRaw
      integrand.lower integrand.upper (FTC.endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hwidth : RealCompute.WidthsShrinkToZero
      (FTC.riemannRawOfEffectiveFTC h).compute)
    (hradius : forall n,
      ((endpointDifferenceRaw primitive.toRealFunRaw integrand.lower
        integrand.upper agreement.endpoint_valid).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    (effectiveFTCStabilizedCandidateValueFor h agreement radius hriemann hwidth
      hradius hradius_shrinks).Valid := by
  exact Integral.candidateValueFor_valid integrand
    (effectiveFTCStabilizedCandidateConstructionFor h agreement radius hriemann hwidth
      hradius hradius_shrinks)

theorem effectiveFTCStabilizedCandidateValueFor_equiv_endpointDifference
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (agreement : FTC.EndpointScheduleAgreement primitive.toRealFunRaw
      integrand.lower integrand.upper (FTC.endpointRawOfEffectiveFTC h))
    (radius : Nat -> Rat)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hwidth : RealCompute.WidthsShrinkToZero
      (FTC.riemannRawOfEffectiveFTC h).compute)
    (hradius : forall n,
      ((endpointDifferenceRaw primitive.toRealFunRaw integrand.lower
        integrand.upper agreement.endpoint_valid).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    (effectiveFTCStabilizedCandidateValueFor h agreement radius hriemann hwidth
      hradius hradius_shrinks).Equiv
      (endpointDifferenceRaw primitive.toRealFunRaw integrand.lower
        integrand.upper agreement.endpoint_valid) := by
  change (FTC.effectiveFTCStabilizedRaw h radius).Equiv _
  exact FTC.effectiveFTCStabilizedRaw_equiv_endpointDifference h hriemann
    agreement radius hradius

namespace Integral

/-- A definite-integral identity on raw total functions:
the integral of `integrand` over `[a,b]` equals the endpoint difference of the
primitive. -/
structure CandidateEndpointAgreement
    (integrand primitive : RealFunRaw) (a b : Rat) where
  construction : Integral.SampleConstruction integrand a b
  endpoint_valid :
    RealCompute.ValidCompute (endpointDifferenceCompute primitive a b)
  equivalent :
    CandidateEqualsEndpointDifference
      primitive integrand a b construction endpoint_valid

namespace CandidateEndpointAgreement

theorem integral_valid
    {integrand primitive : RealFunRaw} {a b : Rat}
    (I : CandidateEndpointAgreement integrand primitive a b) :
    (Integral.sampleValue integrand a b I.construction).Valid :=
  FTC.integral_valid_of_construction I.construction

theorem endpoint_formula
    {integrand primitive : RealFunRaw} {a b : Rat}
    (I : CandidateEndpointAgreement integrand primitive a b) :
    CandidateEqualsEndpointDifference
      primitive integrand a b I.construction I.endpoint_valid :=
  I.equivalent

end CandidateEndpointAgreement

/-- The same definite-integral identity, but with both functions already
certified on a finite rational interval. -/
structure CandidateEndpointAgreementOnInterval
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction :
    Integral.SampleConstruction
      integrand.toRealFunRaw integrand.lower integrand.upper
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    CandidateEqualsEndpointDifference
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper construction endpoint_valid

namespace CandidateEndpointAgreementOnInterval

def toCandidateEndpointAgreement
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementOnInterval integrand primitive) :
    CandidateEndpointAgreement
      integrand.toRealFunRaw primitive.toRealFunRaw
      integrand.lower integrand.upper where
  construction := I.construction
  endpoint_valid := I.endpoint_valid
  equivalent := I.equivalent

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementOnInterval integrand primitive) :
    (Integral.sampleValue
      integrand.toRealFunRaw integrand.lower integrand.upper
      I.construction).Valid :=
  I.toCandidateEndpointAgreement.integral_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementOnInterval integrand primitive) :
    CandidateEqualsEndpointDifference
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper I.construction I.endpoint_valid :=
  I.equivalent

end CandidateEndpointAgreementOnInterval

/-- Numerical endpoint agreement for the domain-aware candidate interface.
The raw computation is valid, but its mathematical integral role must be
established separately with `HasIntegral`. This record stores an agreement;
projecting it is not a new FTC proof. -/
structure CandidateEndpointAgreementFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.CandidateConstructionFor integrand
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.candidateValueFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace CandidateEndpointAgreementFor

/-- An endpoint comparison transports a separately established semantic
integral proof. The comparison record by itself does not prove integrability. -/
theorem hasIntegral {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive)
    (hendpoint : HasIntegral integrand (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper I.endpoint_valid)) :
    HasIntegral integrand (candidateValueFor integrand I.construction) :=
  hendpoint.congr I.construction.certificate (RealCompute.equiv_symm I.equivalent)

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive) :
    (Integral.candidateValueFor integrand I.construction).Valid :=
  Integral.candidateValueFor_valid integrand I.construction

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive) :
    (Integral.candidateValueFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealCompute.Valid] using I.endpoint_valid

/-- Replace the integral construction in a domain-aware definite-integral
identity by an equivalent construction. -/
def transportConstruction
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive)
    (construction' : Integral.CandidateConstructionFor integrand)
    (hconstruction :
      (Integral.candidateValueFor integrand construction').Equiv
        (Integral.candidateValueFor integrand I.construction)) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction'
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealCompute.equiv_trans
      (Integral.candidateValueFor_valid integrand construction')
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Two domain-aware definite-integral identities for the same integrand and
primitive have equivalent integral raw reals. -/
theorem integral_equiv_integral
    {integrand primitive : FunctionOnInterval}
    (I J : CandidateEndpointAgreementFor integrand primitive) :
    (Integral.candidateValueFor integrand I.construction).Equiv
      (Integral.candidateValueFor integrand J.construction) := by
  exact RealCompute.equiv_trans
    I.integral_valid
    I.endpoint_raw_valid
    J.integral_valid
    I.equivalent
    (RealCompute.equiv_symm J.equivalent)

/-- Additivity transfers from endpoint differences to integrals once each
piece has a definite-integral identity.

This is the FTC-facing algebra step: after proving
`∫_a^b f = F(b)-F(a)`, `∫_b^c f = F(c)-F(b)`, and
`∫_a^c f = F(c)-F(a)`, the remaining additivity proof is just endpoint
telescoping. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : CandidateEndpointAgreementFor integrandAB primitiveAB)
    (Ibc : CandidateEndpointAgreementFor integrandBC primitiveBC)
    (Iac : CandidateEndpointAgreementFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.candidateValueFor integrandAB Iab.construction) +
      (Integral.candidateValueFor integrandBC Ibc.construction)).Equiv
        (Integral.candidateValueFor integrandAC Iac.construction) := by
  have hsum_integral_valid :
      ((Integral.candidateValueFor integrandAB Iab.construction) +
        (Integral.candidateValueFor integrandBC Ibc.construction)).Valid :=
    RealCompute.add_valid Iab.integral_valid Ibc.integral_valid
  have hsum_endpoint_valid :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Valid :=
    RealCompute.add_valid Iab.endpoint_raw_valid Ibc.endpoint_raw_valid
  have hintegral_to_endpoint :
      ((Integral.candidateValueFor integrandAB Iab.construction) +
        (Integral.candidateValueFor integrandBC Ibc.construction)).Equiv
          ((endpointDifferenceRaw primitiveAB.toRealFunRaw
              integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
            (endpointDifferenceRaw primitiveBC.toRealFunRaw
              integrandBC.lower integrandBC.upper Ibc.endpoint_valid)) :=
    RealCompute.add_equiv
      Iab.integral_valid Iab.endpoint_raw_valid
      Ibc.integral_valid Ibc.endpoint_raw_valid
      Iab.equivalent Ibc.equivalent
  have hintegral_to_ac_endpoint :
      ((Integral.candidateValueFor integrandAB Iab.construction) +
        (Integral.candidateValueFor integrandBC Ibc.construction)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid) :=
    RealCompute.equiv_trans
      hsum_integral_valid hsum_endpoint_valid Iac.endpoint_raw_valid
      hintegral_to_endpoint hendpoint
  exact RealCompute.equiv_trans
    hsum_integral_valid Iac.endpoint_raw_valid Iac.integral_valid
    hintegral_to_ac_endpoint
    (RealCompute.equiv_symm Iac.equivalent)

/-- Linearity-facing orientation of
`integral_add_equiv_of_endpoint_additive`.

If the endpoint difference of `H` is the sum of the endpoint differences of
`F` and `G`, then the integral of `H` is the sum of the integrals of `F` and
`G`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : CandidateEndpointAgreementFor integrandF primitiveF)
    (IG : CandidateEndpointAgreementFor integrandG primitiveG)
    (IH : CandidateEndpointAgreementFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.candidateValueFor integrandH IH.construction).Equiv
      ((Integral.candidateValueFor integrandF IF.construction) +
        (Integral.candidateValueFor integrandG IG.construction)) :=
  RealCompute.equiv_symm
    (integral_add_equiv_of_endpoint_additive
      IF IG IH (RealCompute.equiv_symm hendpoint))

/-- Rational scaling transfers from endpoint differences to
integrals once both sides have definite-integral identities.

This is the scalar analogue of
`integral_add_equiv_of_endpoint_additive`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : CandidateEndpointAgreementFor integrand primitive)
    (J : CandidateEndpointAgreementFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealCompute.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.candidateValueFor scaledIntegrand J.construction).Equiv
      (RealCompute.scaleRat r
        (Integral.candidateValueFor integrand I.construction)) := by
  have hscaled_endpoint_valid :
      (RealCompute.scaleRat r
        (endpointDifferenceRaw primitive.toRealFunRaw
          integrand.lower integrand.upper I.endpoint_valid)).Valid :=
    RealCompute.scaleRat_valid I.endpoint_raw_valid
  have hscaled_integral_valid :
      (RealCompute.scaleRat r
        (Integral.candidateValueFor integrand I.construction)).Valid :=
    RealCompute.scaleRat_valid I.integral_valid
  have hintegral_to_scaled_endpoint :
      (Integral.candidateValueFor scaledIntegrand J.construction).Equiv
        (RealCompute.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid)) :=
    RealCompute.equiv_trans
      J.integral_valid J.endpoint_raw_valid hscaled_endpoint_valid
      J.equivalent hendpoint
  exact RealCompute.equiv_trans
    J.integral_valid hscaled_endpoint_valid hscaled_integral_valid
    hintegral_to_scaled_endpoint
    (RealCompute.equiv_symm
      (RealCompute.scaleRat_equiv I.equivalent))

/-- Order transfers from endpoint differences to integrals once both sides
have definite-integral identities.

This is the order analogue of the endpoint-additivity and endpoint-scaling
transfer theorems: after FTC has identified each integral with a primitive
endpoint difference, it remains only to prove the endpoint differences are
ordered. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : CandidateEndpointAgreementFor integrandF primitiveF)
    (IG : CandidateEndpointAgreementFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.candidateValueFor integrandF IF.construction).Le
      (Integral.candidateValueFor integrandG IG.construction) := by
  have hleft :
      (Integral.candidateValueFor integrandF IF.construction).Le
        (endpointDifferenceRaw primitiveF.toRealFunRaw
          integrandF.lower integrandF.upper IF.endpoint_valid) :=
    RealCompute.le_of_equiv IF.integral_valid IF.endpoint_raw_valid IF.equivalent
  have hright :
      (endpointDifferenceRaw primitiveG.toRealFunRaw
        integrandG.lower integrandG.upper IG.endpoint_valid).Le
        (Integral.candidateValueFor integrandG IG.construction) :=
    RealCompute.le_of_equiv IG.endpoint_raw_valid IG.integral_valid
      (RealCompute.equiv_symm IG.equivalent)
  exact RealCompute.le_trans IG.endpoint_raw_valid
    (RealCompute.le_trans IF.endpoint_raw_valid hleft hendpoint)
    hright

end CandidateEndpointAgreementFor

/-- Data for a constructive integration-by-parts identity on one rational
interval.

`left` and `right` stand for the two integrands `f*g'` and `f'*g`; `product`
is the endpoint product `f*g`.  The substantive field is
`paired_sum_equiv`: it is where a common finite subdivision, its two
Stieltjes computations, and its shrinking corner budget are certified.  The
theorems below perform only representation-safe raw-interval algebra, so they
do not turn a suggested antiderivative or an unproved limiting rule into an
axiom. -/
structure IntegrationByPartsCertificate
    (left right product : FunctionOnInterval) where
  same_lower_left : product.lower = left.lower
  same_upper_left : product.upper = left.upper
  same_lower_right : product.lower = right.lower
  same_upper_right : product.upper = right.upper
  left_construction : Integral.CandidateConstructionFor left
  right_construction : Integral.CandidateConstructionFor right
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute product.toRealFunRaw product.lower product.upper)
  paired_sum_equiv :
    ((Integral.candidateValueFor left left_construction) +
      (Integral.candidateValueFor right right_construction)).Equiv
        (endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
          endpoint_valid)

namespace IntegrationByPartsCertificate

theorem left_integral_valid
    {left right product : FunctionOnInterval}
    (C : IntegrationByPartsCertificate left right product) :
    (Integral.candidateValueFor left C.left_construction).Valid :=
  Integral.candidateValueFor_valid left C.left_construction

theorem right_integral_valid
    {left right product : FunctionOnInterval}
    (C : IntegrationByPartsCertificate left right product) :
    (Integral.candidateValueFor right C.right_construction).Valid :=
  Integral.candidateValueFor_valid right C.right_construction

theorem endpoint_raw_valid
    {left right product : FunctionOnInterval}
    (C : IntegrationByPartsCertificate left right product) :
    (endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
      C.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealCompute.Valid] using C.endpoint_valid

/-- Constructive integration by parts in its usual first orientation.  The
finite paired-subdivision certificate states that the two integral raws add
to the endpoint product; subtracting the second valid raw representative is
then justified by the checked interval cancellation laws. -/
theorem left_integral_equiv_endpoint_sub_right
    {left right product : FunctionOnInterval}
    (C : IntegrationByPartsCertificate left right product) :
    (Integral.candidateValueFor left C.left_construction).Equiv
      ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
        C.endpoint_valid) -
        (Integral.candidateValueFor right C.right_construction)) := by
  have hleft := C.left_integral_valid
  have hright := C.right_integral_valid
  have hendpoint := C.endpoint_raw_valid
  have hsum :
      ((Integral.candidateValueFor left C.left_construction) +
        (Integral.candidateValueFor right C.right_construction)).Valid :=
    RealCompute.add_valid hleft hright
  have hsumSub :
      (((Integral.candidateValueFor left C.left_construction) +
        (Integral.candidateValueFor right C.right_construction)) -
        (Integral.candidateValueFor right C.right_construction)).Valid :=
    RealCompute.sub_valid hsum hright
  have hendpointSub :
      ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
        C.endpoint_valid) -
        (Integral.candidateValueFor right C.right_construction)).Valid :=
    RealCompute.sub_valid hendpoint hright
  have hsubtract :
      (((Integral.candidateValueFor left C.left_construction) +
        (Integral.candidateValueFor right C.right_construction)) -
        (Integral.candidateValueFor right C.right_construction)).Equiv
          ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
            C.endpoint_valid) -
            (Integral.candidateValueFor right C.right_construction)) :=
    RealCompute.sub_equiv hsum hendpoint hright hright C.paired_sum_equiv
      (RealCompute.equiv_refl _ hright)
  exact RealCompute.equiv_trans hleft hsumSub hendpointSub
    (RealCompute.equiv_symm (RealCompute.add_sub_cancel_right_equiv hleft hright))
    hsubtract

/-- The symmetric orientation of constructive integration by parts.  It is
derived from the same paired mesh certificate after an explicit commutation of
the two valid integral raws. -/
theorem right_integral_equiv_endpoint_sub_left
    {left right product : FunctionOnInterval}
    (C : IntegrationByPartsCertificate left right product) :
    (Integral.candidateValueFor right C.right_construction).Equiv
      ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
        C.endpoint_valid) -
        (Integral.candidateValueFor left C.left_construction)) := by
  have hleft := C.left_integral_valid
  have hright := C.right_integral_valid
  have hendpoint := C.endpoint_raw_valid
  have hsum :
      ((Integral.candidateValueFor left C.left_construction) +
        (Integral.candidateValueFor right C.right_construction)).Valid :=
    RealCompute.add_valid hleft hright
  have hsumComm :
      ((Integral.candidateValueFor right C.right_construction) +
        (Integral.candidateValueFor left C.left_construction)).Valid :=
    RealCompute.add_valid hright hleft
  have hsumSub :
      (((Integral.candidateValueFor right C.right_construction) +
        (Integral.candidateValueFor left C.left_construction)) -
        (Integral.candidateValueFor left C.left_construction)).Valid :=
    RealCompute.sub_valid hsumComm hleft
  have hendpointSub :
      ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
        C.endpoint_valid) -
        (Integral.candidateValueFor left C.left_construction)).Valid :=
    RealCompute.sub_valid hendpoint hleft
  have hpairedComm :
      ((Integral.candidateValueFor right C.right_construction) +
        (Integral.candidateValueFor left C.left_construction)).Equiv
          (endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
            C.endpoint_valid) :=
    RealCompute.equiv_trans hsumComm hsum hendpoint
      (RealCompute.add_comm_equiv _ _ hright hleft)
      C.paired_sum_equiv
  have hsubtract :
      (((Integral.candidateValueFor right C.right_construction) +
        (Integral.candidateValueFor left C.left_construction)) -
        (Integral.candidateValueFor left C.left_construction)).Equiv
          ((endpointDifferenceRaw product.toRealFunRaw product.lower product.upper
            C.endpoint_valid) -
            (Integral.candidateValueFor left C.left_construction)) :=
    RealCompute.sub_equiv hsumComm hendpoint hleft hleft hpairedComm
      (RealCompute.equiv_refl _ hleft)
  exact RealCompute.equiv_trans hright hsumSub hendpointSub
    (RealCompute.equiv_symm (RealCompute.add_sub_cancel_right_equiv hright hleft))
    hsubtract

end IntegrationByPartsCertificate

/-- A definite-integral identity whose integral side is explicitly supplied by
a monotone-integral construction. -/
structure MonotoneCandidateEndpointAgreementFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.MonotoneCandidateConstructionFor integrand
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.monotoneCandidateValueFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace MonotoneCandidateEndpointAgreementFor

def toCandidateEndpointAgreementFor
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := I.construction.construction
  endpoint_valid := I.endpoint_valid
  equivalent := by
    simpa [Integral.monotoneCandidateValueFor] using I.equivalent

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive) :
    (Integral.monotoneCandidateValueFor integrand I.construction).Valid :=
  Integral.monotoneCandidateValueFor_valid integrand I.construction

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealCompute.Valid] using I.endpoint_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive) :
    (Integral.monotoneCandidateValueFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

/-- Monotone-facing version of
`CandidateEndpointAgreementFor.integral_add_equiv_of_endpoint_additive`. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : MonotoneCandidateEndpointAgreementFor integrandAB primitiveAB)
    (Ibc : MonotoneCandidateEndpointAgreementFor integrandBC primitiveBC)
    (Iac : MonotoneCandidateEndpointAgreementFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.monotoneCandidateValueFor integrandAB Iab.construction) +
      (Integral.monotoneCandidateValueFor integrandBC Ibc.construction)).Equiv
        (Integral.monotoneCandidateValueFor integrandAC Iac.construction) := by
  simpa [MonotoneCandidateEndpointAgreementFor.toCandidateEndpointAgreementFor,
    Integral.monotoneCandidateValueFor] using
    CandidateEndpointAgreementFor.integral_add_equiv_of_endpoint_additive
      Iab.toCandidateEndpointAgreementFor Ibc.toCandidateEndpointAgreementFor
      Iac.toCandidateEndpointAgreementFor hendpoint

/-- Monotone-facing version of
`CandidateEndpointAgreementFor.integral_equiv_add_of_endpoint_add`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : MonotoneCandidateEndpointAgreementFor integrandF primitiveF)
    (IG : MonotoneCandidateEndpointAgreementFor integrandG primitiveG)
    (IH : MonotoneCandidateEndpointAgreementFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.monotoneCandidateValueFor integrandH IH.construction).Equiv
      ((Integral.monotoneCandidateValueFor integrandF IF.construction) +
        (Integral.monotoneCandidateValueFor integrandG IG.construction)) := by
  simpa [MonotoneCandidateEndpointAgreementFor.toCandidateEndpointAgreementFor,
    Integral.monotoneCandidateValueFor] using
    CandidateEndpointAgreementFor.integral_equiv_add_of_endpoint_add
      IF.toCandidateEndpointAgreementFor IG.toCandidateEndpointAgreementFor
      IH.toCandidateEndpointAgreementFor hendpoint

/-- Monotone-facing version of
`CandidateEndpointAgreementFor.integral_scaleRat_equiv_of_endpoint_scaleRat`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive)
    (J : MonotoneCandidateEndpointAgreementFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealCompute.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.monotoneCandidateValueFor scaledIntegrand J.construction).Equiv
      (RealCompute.scaleRat r
        (Integral.monotoneCandidateValueFor integrand I.construction)) := by
  simpa [MonotoneCandidateEndpointAgreementFor.toCandidateEndpointAgreementFor,
    Integral.monotoneCandidateValueFor] using
    CandidateEndpointAgreementFor.integral_scaleRat_equiv_of_endpoint_scaleRat
      I.toCandidateEndpointAgreementFor J.toCandidateEndpointAgreementFor hendpoint

/-- Monotone-facing version of
`CandidateEndpointAgreementFor.integral_le_of_endpoint_le`. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : MonotoneCandidateEndpointAgreementFor integrandF primitiveF)
    (IG : MonotoneCandidateEndpointAgreementFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.monotoneCandidateValueFor integrandF IF.construction).Le
      (Integral.monotoneCandidateValueFor integrandG IG.construction) := by
  simpa [MonotoneCandidateEndpointAgreementFor.toCandidateEndpointAgreementFor,
    Integral.monotoneCandidateValueFor] using
    CandidateEndpointAgreementFor.integral_le_of_endpoint_le
      IF.toCandidateEndpointAgreementFor IG.toCandidateEndpointAgreementFor hendpoint

end MonotoneCandidateEndpointAgreementFor

/-- A definite-integral identity whose integral side is supplied by the public
general integral interface: a finite sum over monotone pieces. -/
structure GeneralCandidateEndpointAgreementFor
    (integrand primitive : FunctionOnInterval) where
  same_lower : primitive.lower = integrand.lower
  same_upper : primitive.upper = integrand.upper
  construction : Integral.GeneralCandidateConstructionFor integrand
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute
        primitive.toRealFunRaw integrand.lower integrand.upper)
  equivalent :
    (Integral.generalCandidateValueFor integrand construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        endpoint_valid)

namespace GeneralCandidateEndpointAgreementFor

theorem integral_valid
    {integrand primitive : FunctionOnInterval}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive) :
    (Integral.generalCandidateValueFor integrand I.construction).Valid :=
  Integral.generalCandidateValueFor_valid integrand I.construction

theorem endpoint_raw_valid
    {integrand primitive : FunctionOnInterval}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive) :
    (endpointDifferenceRaw
      primitive.toRealFunRaw integrand.lower integrand.upper
      I.endpoint_valid).Valid := by
  simpa [endpointDifferenceRaw, RealCompute.Valid] using I.endpoint_valid

theorem endpoint_formula
    {integrand primitive : FunctionOnInterval}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive) :
    (Integral.generalCandidateValueFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid) :=
  I.equivalent

/-- Forget that the integral was built by the public general construction and
view it through the ordinary domain-aware definite-integral identity
interface. -/
def toCandidateEndpointAgreementFor
    {integrand primitive : FunctionOnInterval}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction :=
    { compute := (Integral.generalCandidateValueFor integrand I.construction).compute
      certificate := by
        simpa [RealCompute.Valid] using I.integral_valid }
  endpoint_valid := I.endpoint_valid
  equivalent := by
    change (Integral.generalCandidateValueFor integrand I.construction).Equiv
      (endpointDifferenceRaw
        primitive.toRealFunRaw integrand.lower integrand.upper
        I.endpoint_valid)
    exact I.equivalent

/-- Replace the public general construction in a general definite-integral
identity by an equivalent general construction. -/
def transportConstruction
    {integrand primitive : FunctionOnInterval}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive)
    (construction' : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction').Equiv
        (Integral.generalCandidateValueFor integrand I.construction)) :
    GeneralCandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction'
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealCompute.equiv_trans
      (Integral.generalCandidateValueFor_valid integrand construction')
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Promote an ordinary domain-aware definite-integral identity to the public
general-integral interface when a general construction computes an equivalent
raw real. -/
def ofCandidateEndpointAgreementFor
    {integrand primitive : FunctionOnInterval}
    (I : CandidateEndpointAgreementFor integrand primitive)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand I.construction)) :
    GeneralCandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction := construction
  endpoint_valid := I.endpoint_valid
  equivalent := by
    exact RealCompute.equiv_trans
      (Integral.generalCandidateValueFor_valid integrand construction)
      I.integral_valid
      I.endpoint_raw_valid
      hconstruction
      I.equivalent

/-- Two general definite-integral identities for the same integrand and
primitive have equivalent general-integral raw reals. -/
theorem integral_equiv_integral
    {integrand primitive : FunctionOnInterval}
    (I J : GeneralCandidateEndpointAgreementFor integrand primitive) :
    (Integral.generalCandidateValueFor integrand I.construction).Equiv
      (Integral.generalCandidateValueFor integrand J.construction) := by
  exact RealCompute.equiv_trans
    I.integral_valid
    I.endpoint_raw_valid
    J.integral_valid
    I.equivalent
    (RealCompute.equiv_symm J.equivalent)

/-- General-integral version of
`CandidateEndpointAgreementFor.integral_add_equiv_of_endpoint_additive`. -/
theorem integral_add_equiv_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : GeneralCandidateEndpointAgreementFor integrandAB primitiveAB)
    (Ibc : GeneralCandidateEndpointAgreementFor integrandBC primitiveBC)
    (Iac : GeneralCandidateEndpointAgreementFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.generalCandidateValueFor integrandAB Iab.construction) +
      (Integral.generalCandidateValueFor integrandBC Ibc.construction)).Equiv
        (Integral.generalCandidateValueFor integrandAC Iac.construction) := by
  have h := CandidateEndpointAgreementFor.integral_add_equiv_of_endpoint_additive
    Iab.toCandidateEndpointAgreementFor Ibc.toCandidateEndpointAgreementFor
    Iac.toCandidateEndpointAgreementFor hendpoint
  change (RealCompute.add
      (Integral.generalCandidateValueFor integrandAB Iab.construction)
      (Integral.generalCandidateValueFor integrandBC Ibc.construction)).Equiv
    (Integral.generalCandidateValueFor integrandAC Iac.construction)
  exact h

/-- General-integral version of
`CandidateEndpointAgreementFor.integral_equiv_add_of_endpoint_add`. -/
theorem integral_equiv_add_of_endpoint_add
    {integrandF primitiveF integrandG primitiveG integrandH primitiveH :
      FunctionOnInterval}
    (IF : GeneralCandidateEndpointAgreementFor integrandF primitiveF)
    (IG : GeneralCandidateEndpointAgreementFor integrandG primitiveG)
    (IH : GeneralCandidateEndpointAgreementFor integrandH primitiveH)
    (hendpoint :
      (endpointDifferenceRaw primitiveH.toRealFunRaw
        integrandH.lower integrandH.upper IH.endpoint_valid).Equiv
          ((endpointDifferenceRaw primitiveF.toRealFunRaw
              integrandF.lower integrandF.upper IF.endpoint_valid) +
            (endpointDifferenceRaw primitiveG.toRealFunRaw
              integrandG.lower integrandG.upper IG.endpoint_valid))) :
    (Integral.generalCandidateValueFor integrandH IH.construction).Equiv
      ((Integral.generalCandidateValueFor integrandF IF.construction) +
        (Integral.generalCandidateValueFor integrandG IG.construction)) := by
  have h := CandidateEndpointAgreementFor.integral_equiv_add_of_endpoint_add
    IF.toCandidateEndpointAgreementFor IG.toCandidateEndpointAgreementFor
    IH.toCandidateEndpointAgreementFor hendpoint
  change (Integral.generalCandidateValueFor integrandH IH.construction).Equiv
    (RealCompute.add
      (Integral.generalCandidateValueFor integrandF IF.construction)
      (Integral.generalCandidateValueFor integrandG IG.construction))
  exact h

/-- General-integral version of
`CandidateEndpointAgreementFor.integral_scaleRat_equiv_of_endpoint_scaleRat`. -/
theorem integral_scaleRat_equiv_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : GeneralCandidateEndpointAgreementFor integrand primitive)
    (J : GeneralCandidateEndpointAgreementFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealCompute.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.generalCandidateValueFor scaledIntegrand J.construction).Equiv
      (RealCompute.scaleRat r
        (Integral.generalCandidateValueFor integrand I.construction)) := by
  have h := CandidateEndpointAgreementFor.integral_scaleRat_equiv_of_endpoint_scaleRat
    I.toCandidateEndpointAgreementFor J.toCandidateEndpointAgreementFor hendpoint
  change (Integral.generalCandidateValueFor scaledIntegrand J.construction).Equiv
    (RealCompute.scaleRat r
      (Integral.generalCandidateValueFor integrand I.construction))
  exact h

/-- General-integral version of
`CandidateEndpointAgreementFor.integral_le_of_endpoint_le`. -/
theorem integral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : GeneralCandidateEndpointAgreementFor integrandF primitiveF)
    (IG : GeneralCandidateEndpointAgreementFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.generalCandidateValueFor integrandF IF.construction).Le
      (Integral.generalCandidateValueFor integrandG IG.construction) := by
  have h := CandidateEndpointAgreementFor.integral_le_of_endpoint_le
    IF.toCandidateEndpointAgreementFor IG.toCandidateEndpointAgreementFor hendpoint
  change (Integral.generalCandidateValueFor integrandF IF.construction).Le
    (Integral.generalCandidateValueFor integrandG IG.construction)
  exact h

/-- Promote a one-piece monotone endpoint identity to the public general
integral interface. -/
noncomputable def ofMonotone
    {integrand primitive : FunctionOnInterval}
    (I : MonotoneCandidateEndpointAgreementFor integrand primitive)
    (hinterval : integrand.lower <= integrand.upper) :
    GeneralCandidateEndpointAgreementFor integrand primitive where
  same_lower := I.same_lower
  same_upper := I.same_upper
  construction :=
    Integral.PiecewiseMonotoneCandidateConstructionFor.ofMonotone
      I.construction hinterval
  endpoint_valid := I.endpoint_valid
  equivalent := by
    have hgeneral :
        (Integral.generalCandidateValueFor integrand
          (Integral.PiecewiseMonotoneCandidateConstructionFor.ofMonotone
            I.construction hinterval)).Equiv
          (Integral.monotoneCandidateValueFor integrand I.construction) :=
      Integral.generalCandidateValueFor_ofMonotone_equiv
        I.construction hinterval
    exact RealCompute.equiv_trans
      (Integral.generalCandidateValueFor_valid integrand
        (Integral.PiecewiseMonotoneCandidateConstructionFor.ofMonotone
          I.construction hinterval))
      I.integral_valid
      I.endpoint_raw_valid
      hgeneral
      I.equivalent

end GeneralCandidateEndpointAgreementFor

def definiteIdentity_of_effectiveFTC
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC primitive integrand a b)
    (c : Integral.SampleConstruction integrand a b)
    (hendpoint :
      RealCompute.ValidCompute (endpointDifferenceCompute primitive a b))
    (hplan : c.plan = FTC.integralPlanOfEffectiveFTC h)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw primitive a b hendpoint)) :
    CandidateEndpointAgreement integrand primitive a b where
  construction := c
  endpoint_valid := hendpoint
  equivalent :=
    FTC.effectiveFTC_definiteIntegralEqualsEndpoint
      h c hendpoint hplan hscheduledEndpoint hendpoint_equiv

def definiteIdentity_of_staticDyadicEffectiveFTC
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC primitive integrand a b)
    (c : Integral.SampleConstruction integrand a b)
    (hendpoint :
      RealCompute.ValidCompute (endpointDifferenceCompute primitive a b))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw primitive a b hendpoint)) :
    CandidateEndpointAgreement integrand primitive a b where
  construction := c
  endpoint_valid := hendpoint
  equivalent :=
    FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint
      h c hendpoint hplan hscheduledEndpoint hendpoint_equiv

def definiteIdentity_of_effectiveFTC_endpointAgreement
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC primitive integrand a b)
    (c : Integral.SampleConstruction integrand a b)
    (hplan : c.plan = FTC.integralPlanOfEffectiveFTC h)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive a b
        (FTC.endpointRawOfEffectiveFTC h)) :
    CandidateEndpointAgreement integrand primitive a b where
  construction := c
  endpoint_valid := endpoint.endpoint_valid
  equivalent :=
    FTC.effectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
      h c hplan endpoint

def definiteIdentity_of_staticDyadicEffectiveFTC_endpointAgreement
    {primitive integrand : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC primitive integrand a b)
    (c : Integral.SampleConstruction integrand a b)
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive a b
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    CandidateEndpointAgreement integrand primitive a b where
  construction := c
  endpoint_valid := endpoint.endpoint_valid
  equivalent :=
    FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
      h c hplan endpoint

/-- Package the scheduled Riemann algorithm from an `EffectiveFTC` certificate
as a domain-aware integral construction. -/
def constructionFor_of_effectiveFTC
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h).Valid) :
    Integral.CandidateConstructionFor integrand where
  compute := FTC.riemannComputeOfEffectiveFTC h
  certificate := by
    simpa [RealCompute.Valid, FTC.riemannRawOfEffectiveFTC] using hvalid

theorem candidateValueFor_effectiveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h).Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_effectiveFTC h hvalid)).compute =
        FTC.riemannComputeOfEffectiveFTC h := rfl

/-- Turn an `EffectiveFTC` certificate into the domain-aware definite-integral
identity interface.

As in the derivative-bound route, validity of the scheduled Riemann and
endpoint algorithms is kept explicit.  The `EffectiveFTC` certificate supplies
the same-stage overlap; the endpoint-equivalence hypothesis identifies the
scheduled endpoint algorithm with the canonical endpoint-difference raw real. -/
def definiteIdentityFor_of_effectiveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := same_lower
  same_upper := same_upper
  construction := constructionFor_of_effectiveFTC h hriemann
  endpoint_valid := hendpoint
  equivalent := by
    have hbridge :
        (Integral.candidateValueFor integrand
          (constructionFor_of_effectiveFTC h hriemann)).Equiv
            (FTC.endpointRawOfEffectiveFTC h) := by
      simpa [Integral.candidateValueFor, constructionFor_of_effectiveFTC,
        FTC.riemannRawOfEffectiveFTC] using
        FTC.effectiveFTC_equiv_endpoint h
    exact RealCompute.equiv_trans
      (Integral.candidateValueFor_valid integrand
        (constructionFor_of_effectiveFTC h hriemann))
      hscheduledEndpoint
      hendpoint
      hbridge
      hendpoint_equiv

/-- Static-dyadic specialization of
`constructionFor_of_effectiveFTC`. -/
def constructionFor_of_staticDyadicEffectiveFTC
    {integrand primitive : FunctionOnInterval}
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid) :
    Integral.CandidateConstructionFor integrand :=
  constructionFor_of_effectiveFTC h.toEffectiveFTC hvalid

theorem candidateValueFor_staticDyadicEffectiveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_staticDyadicEffectiveFTC h hvalid)).compute =
        FTC.riemannComputeOfEffectiveFTC h.toEffectiveFTC := rfl

/-- Domain-aware definite-integral identity produced by a static-dyadic
`EffectiveFTC` certificate. -/
def definiteIdentityFor_of_staticDyadicEffectiveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC
    same_lower same_upper h.toEffectiveFTC
    hriemann hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_effectiveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        (FTC.endpointRawOfEffectiveFTC h)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC
    same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_effectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_effectiveFTC_endpointAgreement
    same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_effectiveFTC_stageSchedule
      h hendpoint sigma hsigma)

def definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_staticDyadicEffectiveFTC
    same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement
    same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Package a stabilized two-stage finite FTC evaluator as a public
domain-aware integral construction.

The evaluator itself is the finite-prefix stabilization of the certificate's
bounded sums.  The endpoint raw appears only in the proof-side hypotheses
which show that the explicit radius schedule is sufficient. -/
def constructionFor_of_twoStageCandidateDerivativeFTC_stabilized
    {primitive integrand : FunctionOnInterval}
    (h : TwoStageCandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hendpoint : RealCompute.ValidCompute
      (endpointDifferenceCompute primitive.toRealFunRaw integrand.lower integrand.upper))
    (radius : Nat -> Rat)
    (hshrink : RealCompute.WidthsShrinkToZero h.boundedIntegralRaw.compute)
    (hradius : forall n,
      ((endpointDifferenceRaw primitive.toRealFunRaw integrand.lower integrand.upper
        hendpoint).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    Integral.CandidateConstructionFor integrand where
  compute := (h.stabilizedRaw hendpoint radius).compute
  certificate := by
    simpa [TwoStageCandidateDerivativeFTC.stabilizedRaw, RealCompute.Valid] using
      h.stabilizedRaw_valid hendpoint radius hshrink hradius hradius_shrinks

/-- Package a derivative-bound FTC cell-sum algorithm as a domain-aware
integral construction.

The derivative-bound certificate supplies the comparison with endpoint
differences.  The validity of the bounded-sum raw algorithm is kept as an
explicit hypothesis because validity in this project includes nestedness and
shrinking, not just same-stage overlap. -/
def constructionFor_of_derivativeBoundFTC
    {integrand primitive : FunctionOnInterval}
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand where
  compute := h.boundedIntegralCompute
  certificate := by
    simpa [RealCompute.Valid, DerivativeBoundFTC.boundedIntegralRaw] using hvalid

theorem candidateValueFor_derivativeBoundFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_derivativeBoundFTC h hvalid)).compute =
        h.boundedIntegralCompute := rfl

/-- Turn a derivative-bound FTC certificate into the domain-aware definite
integral identity interface.

Two representation obligations remain explicit: the derivative-bound integral
algorithm must be a valid `RealCompute`, and the scheduled endpoint algorithm must
be equivalent to the canonical endpoint-difference algorithm.  Those are
formula-specific bookkeeping facts, while the FTC overlap itself is supplied
by `DerivativeBoundFTC.equiv_endpoint`. -/
def definiteIdentityFor_of_derivativeBoundFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := same_lower
  same_upper := same_upper
  construction := constructionFor_of_derivativeBoundFTC h hbounded
  endpoint_valid := hendpoint
  equivalent := by
    have hbridge :
        (Integral.candidateValueFor integrand
          (constructionFor_of_derivativeBoundFTC h hbounded)).Equiv
            h.endpointRaw := by
      simpa [Integral.candidateValueFor, constructionFor_of_derivativeBoundFTC,
        DerivativeBoundFTC.boundedIntegralRaw] using h.equiv_endpoint
    exact RealCompute.equiv_trans
      (Integral.candidateValueFor_valid integrand
        (constructionFor_of_derivativeBoundFTC h hbounded))
      hscheduledEndpoint
      hendpoint
      hbridge
      hendpoint_equiv

def definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper h.endpointRaw) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_derivativeBoundFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) =
        sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule
      h hendpoint sigma hsigma)

/-! The selected-stage FTC interface is the direct form used by evaluators
whose derivative and endpoint boxes are deliberately computed at one common
finite stage.  Keep this bridge separate from the derivative-bound wrapper:
the selected-stage certificate already contains the finite telescope and
should be consumable without an artificial re-packaging step. -/

def constructionFor_of_selectedStageCandidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (h : SelectedStageCandidateDerivativeFTC
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand where
  compute := h.boundedIntegralCompute
  certificate := by
    simpa [RealCompute.Valid, SelectedStageCandidateDerivativeFTC.boundedIntegralRaw] using hvalid

theorem candidateValueFor_selectedStageCandidateDerivativeFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : SelectedStageCandidateDerivativeFTC
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_selectedStageCandidateDerivativeFTC h hvalid)).compute =
        h.boundedIntegralCompute := rfl

def definiteIdentityFor_of_selectedStageCandidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : SelectedStageCandidateDerivativeFTC
      primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive where
  same_lower := same_lower
  same_upper := same_upper
  construction := constructionFor_of_selectedStageCandidateDerivativeFTC h hbounded
  endpoint_valid := hendpoint
  equivalent := by
    have hbridge :
        (Integral.candidateValueFor integrand
          (constructionFor_of_selectedStageCandidateDerivativeFTC h hbounded)).Equiv
            h.endpointRaw := by
      simpa [Integral.candidateValueFor,
        constructionFor_of_selectedStageCandidateDerivativeFTC,
        SelectedStageCandidateDerivativeFTC.boundedIntegralRaw] using h.equiv_endpoint
    exact RealCompute.equiv_trans
      (Integral.candidateValueFor_valid integrand
        (constructionFor_of_selectedStageCandidateDerivativeFTC h hbounded))
      hscheduledEndpoint hendpoint hbridge hendpoint_equiv

/-- Candidate-derivative specialization of
`constructionFor_of_derivativeBoundFTC`. -/
def constructionFor_of_candidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand :=
  constructionFor_of_derivativeBoundFTC h.toDerivativeBoundFTC hvalid

theorem candidateValueFor_candidateDerivativeFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_candidateDerivativeFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

/-- Turn a candidate-derivative FTC certificate into the domain-aware
definite-integral identity interface. -/
def definiteIdentityFor_of_candidateDerivativeFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h.toDerivativeBoundFTC
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_candidateDerivativeFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule
      h hendpoint sigma hsigma)

/-- Convexity-facing specialization of
`definiteIdentityFor_of_derivativeBoundFTC`.

The public convex FTC certificate first turns into a derivative-bound FTC
certificate, then uses the same domain-aware endpoint-identity bridge. -/
def constructionFor_of_curvatureFTC
    {integrand primitive : FunctionOnInterval}
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand :=
  constructionFor_of_derivativeBoundFTC h.toDerivativeBoundFTC hvalid

theorem candidateValueFor_curvatureFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_curvatureFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

/-- Turn a curvature FTC certificate into the domain-aware definite-integral
identity interface.  This covers both convex and concave curvature data. -/
def definiteIdentityFor_of_curvatureFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_derivativeBoundFTC
    same_lower same_upper h.toDerivativeBoundFTC
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_curvatureFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_curvatureFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_curvatureFTC_stageSchedule
      h hendpoint sigma hsigma)

def constructionFor_of_convexFTC
    {integrand primitive : FunctionOnInterval}
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand :=
  constructionFor_of_curvatureFTC h.toCurvatureFTCCertificate hvalid

theorem candidateValueFor_convexFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_convexFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

def definiteIdentityFor_of_convexFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h.toCurvatureFTCCertificate
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_convexFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_convexFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_convexFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_convexFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_convexFTC_stageSchedule
      h hendpoint sigma hsigma)

def constructionFor_of_concaveFTC
    {integrand primitive : FunctionOnInterval}
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    Integral.CandidateConstructionFor integrand :=
  constructionFor_of_curvatureFTC h.toCurvatureFTCCertificate hvalid

theorem candidateValueFor_concaveFTC_compute_eq
    {integrand primitive : FunctionOnInterval}
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hvalid : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid) :
    (Integral.candidateValueFor integrand
      (constructionFor_of_concaveFTC h hvalid)).compute =
        h.toDerivativeBoundFTC.boundedIntegralCompute := rfl

def definiteIdentityFor_of_concaveFTC
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw
          primitive.toRealFunRaw integrand.lower integrand.upper hendpoint)) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_curvatureFTC
    same_lower same_upper h.toCurvatureFTCCertificate
    hbounded hscheduledEndpoint hendpoint hendpoint_equiv

def definiteIdentityFor_of_concaveFTC_endpointAgreement
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw
        integrand.lower integrand.upper
        h.toDerivativeBoundFTC.endpointRaw) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_concaveFTC
    same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent

def definiteIdentityFor_of_concaveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n) :
    CandidateEndpointAgreementFor integrand primitive :=
  definiteIdentityFor_of_concaveFTC_endpointAgreement
    same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_concaveFTC_stageSchedule
      h hendpoint sigma hsigma)

def generalCandidateEndpointAgreementFor_of_effectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : EffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_effectiveFTC h hriemann))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_effectiveFTC_stageSchedule
      same_lower same_upper h hriemann hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_staticDyadicEffectiveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_staticDyadicEffectiveFTC h hriemann))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule
      same_lower same_upper h hriemann hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_derivativeBoundFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : DerivativeBoundFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n, h.chooseEndpointPrecision (precisionAtStage n) =
        sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_derivativeBoundFTC h hbounded))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_derivativeBoundFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_candidateDerivativeFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_candidateDerivativeFTC h hbounded))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_curvatureFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_curvatureFTC h hbounded))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_curvatureFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_convexFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConvexFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_convexFTC h hbounded))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_convexFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

def generalCandidateEndpointAgreementFor_of_concaveFTC_stageSchedule
    {integrand primitive : FunctionOnInterval}
    (same_lower : primitive.lower = integrand.lower)
    (same_upper : primitive.upper = integrand.upper)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw integrand.toRealFunRaw
      integrand.lower integrand.upper)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute
          primitive.toRealFunRaw integrand.lower integrand.upper))
    (sigma : RealCompute.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (construction : Integral.GeneralCandidateConstructionFor integrand)
    (hconstruction :
      (Integral.generalCandidateValueFor integrand construction).Equiv
        (Integral.candidateValueFor integrand
          (constructionFor_of_concaveFTC h hbounded))) :
    GeneralCandidateEndpointAgreementFor integrand primitive :=
  GeneralCandidateEndpointAgreementFor.ofCandidateEndpointAgreementFor
    (definiteIdentityFor_of_concaveFTC_stageSchedule
      same_lower same_upper h hbounded hendpoint sigma hsigma)
    construction hconstruction

theorem endpointDifference_linearPrimitive_compute
    (c a b : Rat) (n : Nat) :
    endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b n =
      { lo := c * b - c * a, hi := c * b - c * a } := by
  unfold endpointDifferenceCompute endpointDifferenceInterval
    Integral.linearPrimitiveFunRaw RealFunRaw.exact
  simp

theorem constantPrimitiveEndpoint_valid (c a b : Rat) :
    RealCompute.ValidCompute
      (endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b) := by
  have hcompute :
      endpointDifferenceCompute (Integral.linearPrimitiveFunRaw c) a b =
        fun _ : Nat => { lo := c * b - c * a, hi := c * b - c * a } := by
    funext n
    exact endpointDifference_linearPrimitive_compute c a b n
  rw [hcompute]
  exact RealCompute.ofRat_valid (c * b - c * a)

/-- The first fully verified definite-integral identity: the one-cell
Riemann-sum integral of the constant function `c` equals the endpoint
difference of the primitive `x ↦ c*x`. -/
theorem constant_integral_equiv_endpoint (c a b : Rat) :
    CandidateEqualsEndpointDifference
      (Integral.linearPrimitiveFunRaw c) (Integral.constantFunRaw c)
      a b (Integral.constantConstruction c a b)
      (constantPrimitiveEndpoint_valid c a b) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  rw [Integral.constantIntegral_compute]
  simp [endpointDifferenceRaw, endpointDifference_linearPrimitive_compute]
  have harea : (b - a) * c = c * b - c * a := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [harea]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

def constantCandidateEndpointAgreement (c a b : Rat) :
    CandidateEndpointAgreement
      (Integral.constantFunRaw c) (Integral.linearPrimitiveFunRaw c) a b where
  construction := Integral.constantConstruction c a b
  endpoint_valid := constantPrimitiveEndpoint_valid c a b
  equivalent := constant_integral_equiv_endpoint c a b

end Integral

namespace IntegralIdentities

/-- The rational kernel `x ↦ 1 / (1 + x^2)` used by the integral
representation of arctangent. -/
def oneOverOnePlusSquareRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ =>
    let y : Rat := 1 / (1 + x * x)
    { lo := y, hi := y }

/-- The kernel `1 / (1 + x^2)` certified on an arbitrary rational interval. -/
def oneOverOnePlusSquareOnInterval (a b : Rat) : FunctionOnInterval where
  raw := oneOverOnePlusSquareRaw
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x hx
    simpa [oneOverOnePlusSquareRaw] using
      RealCompute.ofRat_valid (1 / (1 + x * x))

theorem oneOverOnePlusSquareOnInterval_valid (a b : Rat) :
    (oneOverOnePlusSquareOnInterval a b).toRealFunRaw.Valid :=
  FunctionOnInterval.toRealFunRaw_valid _

theorem oneOverOnePlusSquareOnInterval_toRealFunRaw_point
    (a b x : Rat) (n : Nat) :
    ((oneOverOnePlusSquareOnInterval a b).toRealFunRaw.compute x n).lo =
      ((oneOverOnePlusSquareOnInterval a b).toRealFunRaw.compute x n).hi := by
  by_cases hleft : a <= x
  · by_cases hright : x <= b
    · simp [FunctionOnInterval.toRealFunRaw, FunctionOnInterval.compute,
        oneOverOnePlusSquareOnInterval, oneOverOnePlusSquareRaw,
        hleft, hright]
    · simp [FunctionOnInterval.toRealFunRaw, oneOverOnePlusSquareOnInterval,
        hleft, hright]
  · simp [FunctionOnInterval.toRealFunRaw, oneOverOnePlusSquareOnInterval,
      hleft]

theorem oneOverOnePlusSquareRaw_compute_eq_sectorAreaDensity
    (u : Rat) (h : oneOverOnePlusSquareRaw.definedAt u) (n : Nat) :
    oneOverOnePlusSquareRaw.compute u h n =
      { lo := RationalCircle.Stage.sectorAreaDensity u,
        hi := RationalCircle.Stage.sectorAreaDensity u } := by
  rw [RationalCircle.Stage.sectorAreaDensity_eq_one_over_one_plus_square]
  simp [oneOverOnePlusSquareRaw]

/-- Exact rational difference factorization for the arctangent kernel. -/
private theorem oneOverOnePlusSquare_difference (s t : Rat) :
    (1 / (1 + s * s)) - (1 / (1 + t * t)) =
      ((t - s) * (s + t)) / ((1 + s * s) * (1 + t * t)) := by
  have hspos : 0 < 1 + s * s := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg s
    grind
  have htpos : 0 < 1 + t * t := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg t
    grind
  have hsne : 1 + s * s ≠ 0 := Rat.ne_of_gt hspos
  have htne : 1 + t * t ≠ 0 := Rat.ne_of_gt htpos
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hscancel : (1 + s * s) * (1 + s * s)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hsne
  have htcancel : (1 + t * t) * (1 + t * t)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ htne
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem oneOverOnePlusSquare_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => 1 / (1 + x * x)) 2 := by
  constructor
  · decide +kernel
  · intro s t hs0 hs1 ht0 ht1
    let d : Rat := (1 + s * s) * (1 + t * t)
    have hsone : 1 <= 1 + s * s := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg s
      grind
    have htone : 1 <= 1 + t * t := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg t
      grind
    have hdpos : 0 < d := by
      dsimp [d]
      exact Rat.mul_pos (by grind) (by grind)
    have hdone : 1 <= d := by
      dsimp [d]
      have hs0 : 0 <= 1 + s * s := Rat.le_trans (by decide +kernel) hsone
      calc
        1 = 1 * 1 := by decide +kernel
        _ <= (1 + s * s) * 1 :=
          Rat.mul_le_mul_of_nonneg_right hsone (by decide +kernel)
        _ <= (1 + s * s) * (1 + t * t) :=
          Rat.mul_le_mul_of_nonneg_left htone hs0
    have hdinv0 : 0 <= d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hdpos)
    have hdinv : d⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := d)
      · calc
          d⁻¹ * d = d * d⁻¹ := by rw [Rat.mul_comm]
          _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
          _ <= 1 * d := by simpa using hdone
      · exact hdpos
    have hsum0 : 0 <= s + t := Rat.add_nonneg hs0 ht0
    have hsum : s + t <= 2 := by grind
    have hsumabs : qabs (s + t) = s + t :=
      qabs_eq_self_of_nonneg hsum0
    have hfactor : (s + t) * d⁻¹ <= 2 := by
      calc
        (s + t) * d⁻¹ <= 2 * d⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hsum hdinv0
        _ <= 2 * 1 :=
          Rat.mul_le_mul_of_nonneg_left hdinv (by decide +kernel)
        _ = 2 := by decide +kernel
    rw [oneOverOnePlusSquare_difference]
    change qabs (((t - s) * (s + t)) / d) <= 2 * qabs (t - s)
    rw [Rat.div_def, qabs_mul, qabs_mul, hsumabs,
      qabs_eq_self_of_nonneg hdinv0]
    calc
      qabs (t - s) * (s + t) * d⁻¹ =
          qabs (t - s) * ((s + t) * d⁻¹) := by
            rw [Rat.mul_assoc]
      _ <= qabs (t - s) * 2 :=
        Rat.mul_le_mul_of_nonneg_left hfactor (qabs_nonneg _)
      _ = 2 * qabs (t - s) := by rw [Rat.mul_comm]

/-- The arctangent kernel on `[0, x]`, as a domain-aware function. -/
abbrev arctanKernelInterval (x : Rat) : FunctionOnInterval :=
  oneOverOnePlusSquareOnInterval 0 x

/-- The arctangent kernel on the unit interval, as a domain-aware function. -/
abbrev arctanKernelIntervalAtOne : FunctionOnInterval :=
  arctanKernelInterval 1

/-- The verified midpoint-rectangle construction for
`∫_0^x dt / (1 + t^2)`, for rational `x` in `[0, 1]`. -/
def arctanIntegralRectangleConstruction
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Integral.CandidateConstructionFor (arctanKernelInterval x) where
  compute := ArctanGeometry.arctanIntegralRectangleCompute x
  certificate := by
    have hvalid := ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
    change RealCompute.ValidCompute
      (ArctanGeometry.arctanIntegralRectangleCompute x)
    exact hvalid

/-- The domain-aware integral raw real supplied by the rectangle construction
for the arctangent kernel on `[0, x]`, with `0 <= x <= 1`. -/
def arctanIntegralRectangleFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) : RealCompute :=
  Integral.candidateValueFor (arctanKernelInterval x)
    (arctanIntegralRectangleConstruction x hx0 hx1)

theorem arctanIntegralRectangleFor_valid
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Valid :=
  Integral.candidateValueFor_valid (arctanKernelInterval x)
    (arctanIntegralRectangleConstruction x hx0 hx1)

theorem arctanIntegralRectangleFor_compute_eq
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleFor x hx0 hx1).compute n =
      ArctanGeometry.arctanIntegralRectangleCompute x n := rfl

theorem arctanIntegralRectangleFor_equiv_raw
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (arctanIntegralRectangleFor x hx0 hx1)
    (ArctanGeometry.arctanIntegralRectangleRaw x) n n).2
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered hx0 n
  have hle :
      (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute x n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
  exact ⟨hle, hle⟩

/-- The arctangent kernel is nonincreasing on every interval `[0,x]`. -/
def arctanKernelInterval_monotone (x : Rat) :
    MonotoneOnInterval (arctanKernelInterval x) where
  increasing := False
  monotone_inc := by
    intro h
    cases h
  monotone_dec := by
    intro _hdec p q hp _hq hpq n
    have hkernel :
        ArctanGeometry.integralKernel q <=
          ArctanGeometry.integralKernel p :=
      ArctanGeometry.integralKernel_antitone_nonneg hp.1 hpq
    simpa [arctanKernelInterval, oneOverOnePlusSquareOnInterval,
      FunctionOnInterval.compute, oneOverOnePlusSquareRaw,
      ArctanGeometry.integralKernel] using hkernel

/-- The rectangle construction for `∫_0^x dt/(1+t^2)`, packaged as a
monotone integral for rational `x` in `[0,1]`. -/
def arctanIntegralRectangleMonotoneConstruction
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Integral.MonotoneCandidateConstructionFor (arctanKernelInterval x) where
  monotone := arctanKernelInterval_monotone x
  construction := arctanIntegralRectangleConstruction x hx0 hx1

/-- The monotone-integral packaging of the rectangle arctangent computation
throughout the rational unit branch. -/
def arctanIntegralRectangleMonotoneFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) : RealCompute :=
  Integral.monotoneCandidateValueFor (arctanKernelInterval x)
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1)

theorem arctanIntegralRectangleMonotoneFor_valid
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Valid :=
  Integral.monotoneCandidateValueFor_valid (arctanKernelInterval x)
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1)

theorem arctanIntegralRectangleMonotoneFor_compute_eq
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).compute n =
      (arctanIntegralRectangleFor x hx0 hx1).compute n := by
  change (arctanIntegralRectangleFor x hx0 hx1).compute n =
    (arctanIntegralRectangleFor x hx0 hx1).compute n
  rfl

theorem arctanIntegralRectangleMonotoneFor_equiv_rectangleFor
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Equiv
      (arctanIntegralRectangleFor x hx0 hx1) := by
  change (arctanIntegralRectangleFor x hx0 hx1).Equiv
    (arctanIntegralRectangleFor x hx0 hx1)
  exact RealCompute.equiv_refl (arctanIntegralRectangleFor x hx0 hx1)
    (arctanIntegralRectangleFor_valid x hx0 hx1)

theorem arctanIntegralRectangleFor_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanGeom x) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (arctanIntegralRectangleFor x hx0 hx1)
    (ArctanGeometry.arctanGeom x) n n).2
  have hover := (RealCompute.compareAt_overlap_iff
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (ArctanGeometry.arctanGeom x) n n).1
      (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0 n)
  simpa [arctanIntegralRectangleFor, Integral.candidateValueFor,
    arctanIntegralRectangleConstruction,
    ArctanGeometry.arctanIntegralRectangleRaw] using hover

theorem arctanIntegralRectangleMonotoneFor_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleMonotoneFor x hx0 hx1).Equiv
      (ArctanGeometry.arctanGeom x) := by
  have hleft :
      (arctanIntegralRectangleMonotoneFor x hx0 hx1).Valid :=
    arctanIntegralRectangleMonotoneFor_valid x hx0 hx1
  have hmid :
      (arctanIntegralRectangleFor x hx0 hx1).Valid :=
    arctanIntegralRectangleFor_valid x hx0 hx1
  have hright : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealCompute.equiv_trans
    hleft hmid hright
    (arctanIntegralRectangleMonotoneFor_equiv_rectangleFor x hx0 hx1)
    (arctanIntegralRectangleFor_equiv_arctanGeom x hx0 hx1)

/-- The verified rectangle-integral arctangent as a partial function on the
rational unit branch. -/
def arctanIntegralRectangleFunctionRaw : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx => (arctanIntegralRectangleFor x hx.1 hx.2).compute
  rate := fun x hx => (arctanIntegralRectangleFor x hx.1 hx.2).rate

def arctanIntegralRectangleRepresentation :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.rectangle"
  raw := arctanIntegralRectangleFunctionRaw

theorem arctanIntegralRectangleFunctionRaw_valid :
    forall x h, RealCompute.ValidCompute
      (arctanIntegralRectangleFunctionRaw.compute x h) := by
  intro x hx
  have hvalid := arctanIntegralRectangleFor_valid x hx.1 hx.2
  change RealCompute.ValidCompute
    (arctanIntegralRectangleFor x hx.1 hx.2).compute
  exact hvalid

/-- The rectangle arctangent as a domain-aware function on the unit slope
interval.  This keeps upper-endpoint monotonicity separate from the
nonincreasing property of its integration kernel. -/
def arctanIntegralRectangleOnUnit : FunctionOnInterval where
  raw := arctanIntegralRectangleFunctionRaw
  lower := 0
  upper := 1
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    have hvalid := arctanIntegralRectangleFor_valid x hx.1 hx.2
    change RealCompute.ValidCompute
      (arctanIntegralRectangleFor x hx.1 hx.2).compute
    exact hvalid

/-- The rectangle arctangent evaluated in the tangent-addition chart based at
`x`.  Its input is the ordinary positive increment `h`; restricting it to a
half unit makes every derived chart increment a valid unit-branch input. -/
def arctanIntegralRectangleTangentChartOnHalf
    (x : Rat) (hx0 : 0 <= x) : FunctionOnInterval where
  raw :=
    { definedAt := fun h => 0 <= h /\ h <= (1 : Rat) / 2
      compute := fun h hh =>
        (arctanIntegralRectangleFor (ArctanGeometry.tangentChartIncrement x h)
          (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
            hx0 hh.1 hh.2).1
          (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
            hx0 hh.1 hh.2).2).compute
      rate := fun h hh =>
        (arctanIntegralRectangleFor (ArctanGeometry.tangentChartIncrement x h)
          (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
            hx0 hh.1 hh.2).1
          (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
            hx0 hh.1 hh.2).2).rate }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro _h hh
    exact hh
  valid_on := by
    intro h hh
    exact arctanIntegralRectangleFor_valid
      (ArctanGeometry.tangentChartIncrement x h)
      (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
        hx0 hh.1 hh.2).1
      (ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
        hx0 hh.1 hh.2).2

theorem arctanIntegralRectangleTangentChartOnHalf_compute
    (x : Rat) (hx0 : 0 <= x) (h : Rat)
    (hh : inDomainInterval
      (arctanIntegralRectangleTangentChartOnHalf x hx0).lower
      (arctanIntegralRectangleTangentChartOnHalf x hx0).upper h)
    (n : Nat) :
    (arctanIntegralRectangleTangentChartOnHalf x hx0).compute h hh n =
      ArctanGeometry.arctanIntegralRectangleCompute
        (ArctanGeometry.tangentChartIncrement x h) n := rfl

/-- The explicit step schedule for the tangent-chart derivative: a step at
most `1 / (2 (n + 1))` makes the rational error `h + h^2` no larger than the
requested stage tolerance. -/
private theorem tangentChart_stepError_le_precision
    {h : Rat} (n : Nat) (hpos : 0 < h)
    (hsmall : h <= 1 / (((2 * (n + 1) : Nat) : Rat))) :
    h + h * h <= (precisionAtStage n).val := by
  let m : Rat := ((n + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hmne : m ≠ 0 := Rat.ne_of_gt hmpos
  have hdenpos : 0 < 2 * m := Rat.mul_pos (by decide +kernel) hmpos
  have hsmall' : h <= 1 / (2 * m) := by
    simpa [m] using hsmall
  have hle_one : h <= 1 := by
    have hdenone : 1 <= 2 * m := by
      have hmone : 1 <= m := by
        dsimp [m]
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      calc
        1 = 1 * 1 := by grind
        _ <= 2 * 1 := Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
          (by decide +kernel)
        _ <= 2 * m := Rat.mul_le_mul_of_nonneg_left hmone (by decide +kernel)
    have hinv : (2 * m)⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := 2 * m)
      · calc
          (2 * m)⁻¹ * (2 * m) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
          _ <= 1 * (2 * m) := by simpa using hdenone
      · exact hdenpos
    calc
      h <= 1 / (2 * m) := hsmall'
      _ = (2 * m)⁻¹ := by rw [Rat.div_def, Rat.one_mul]
      _ <= 1 := hinv
  have hsquare : h * h <= h := by
    calc
      h * h <= h * 1 :=
        Rat.mul_le_mul_of_nonneg_left hle_one (Rat.le_of_lt hpos)
      _ = h := by grind
  have htwice : 2 * h <= 1 / m := by
    apply Rat.le_of_mul_le_mul_right (c := m)
    · calc
        (2 * h) * m = h * (2 * m) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (1 / (2 * m)) * (2 * m) :=
          Rat.mul_le_mul_of_nonneg_right hsmall' (Rat.le_of_lt hdenpos)
        _ = 1 := by
          rw [Rat.div_def]
          have hne : 2 * m ≠ 0 := Rat.ne_of_gt hdenpos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ = (1 / m) * m := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hmpos
  have hstage : 1 / m <= (precisionAtStage n).val := by
    dsimp [m]
    by_cases hn : n = 0
    · subst n
      decide +kernel
    · simp only [precisionAtStage, dif_neg hn]
      exact FTC.one_div_nat_antitone (Nat.pos_of_ne_zero hn)
        (Nat.succ_pos n) (Nat.le_succ n)
  calc
    h + h * h <= h + h := (Rat.add_le_add_left).2 hsquare
    _ = 2 * h := by grind
    _ <= 1 / m := htwice
    _ <= (precisionAtStage n).val := hstage

/-- A stronger step schedule reserves three quarters of the requested
precision for finite chart-transport and rectangle-evaluation error. -/
private theorem tangentChart_stepError_le_quarterPrecision
    {h : Rat} (n : Nat) (hpos : 0 < h)
    (hsmall : h <= 1 / (((8 * (n + 1) : Nat) : Rat))) :
    h + h * h <= (precisionAtStage n).val / 4 := by
  let m : Rat := ((n + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hdenpos : 0 < 8 * m := Rat.mul_pos (by decide +kernel) hmpos
  have hsmall' : h <= 1 / (8 * m) := by
    simpa [m] using hsmall
  have hle_one : h <= 1 := by
    have hdenone : 1 <= 8 * m := by
      have hmone : 1 <= m := by
        dsimp [m]
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      calc
        1 = 1 * 1 := by grind
        _ <= 8 * 1 := Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
          (by decide +kernel)
        _ <= 8 * m := Rat.mul_le_mul_of_nonneg_left hmone (by decide +kernel)
    have hinv : (8 * m)⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := 8 * m)
      · calc
          (8 * m)⁻¹ * (8 * m) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
          _ <= 1 * (8 * m) := by simpa using hdenone
      · exact hdenpos
    calc
      h <= 1 / (8 * m) := hsmall'
      _ = (8 * m)⁻¹ := by rw [Rat.div_def, Rat.one_mul]
      _ <= 1 := hinv
  have hsquare : h * h <= h := by
    calc
      h * h <= h * 1 :=
        Rat.mul_le_mul_of_nonneg_left hle_one (Rat.le_of_lt hpos)
      _ = h := by grind
  have htwice : 2 * h <= 1 / (4 * m) := by
    have hfourmpos : 0 < 4 * m := Rat.mul_pos (by decide +kernel) hmpos
    apply Rat.le_of_mul_le_mul_right (c := 4 * m)
    · calc
        (2 * h) * (4 * m) = h * (8 * m) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (1 / (8 * m)) * (8 * m) :=
          Rat.mul_le_mul_of_nonneg_right hsmall' (Rat.le_of_lt hdenpos)
        _ = 1 := by
          rw [Rat.div_def]
          have hne : 8 * m ≠ 0 := Rat.ne_of_gt hdenpos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ = (1 / (4 * m)) * (4 * m) := by
          rw [Rat.div_def]
          have hne : 4 * m ≠ 0 := Rat.ne_of_gt hfourmpos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hfourmpos
  have hstage : 1 / m <= (precisionAtStage n).val := by
    dsimp [m]
    by_cases hn : n = 0
    · subst n
      decide +kernel
    · simp only [precisionAtStage, dif_neg hn]
      exact FTC.one_div_nat_antitone (Nat.pos_of_ne_zero hn)
        (Nat.succ_pos n) (Nat.le_succ n)
  have hquarter : 1 / (4 * m) <= (precisionAtStage n).val / 4 := by
    have hfactor : 0 <= (1 : Rat) / 4 := by decide +kernel
    have hscale := Rat.mul_le_mul_of_nonneg_left hstage hfactor
    calc
      1 / (4 * m) = ((1 : Rat) / 4) * (1 / m) := by
        rw [Rat.div_def, Rat.inv_mul_rev]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((1 : Rat) / 4) * (precisionAtStage n).val := hscale
      _ = (precisionAtStage n).val / 4 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  calc
    h + h * h <= h + h := (Rat.add_le_add_left).2 hsquare
    _ = 2 * h := by grind
    _ <= 1 / (4 * m) := htwice
    _ <= (precisionAtStage n).val / 4 := hquarter

/-- Evaluation stage for transporting the tangent-chart rectangle quotient
back to an ordinary basepoint.  For a positive step it asks for rectangle and
chart boxes of width at most `h * precision / 16`; the zero/negative branch
is irrelevant to the forward derivative interface. -/
def arctanRectangleTangentTransportPrecision (h : Rat) (n : Nat) : Nat :=
  if hpos : 0 < h then
    let eps : QPos :=
      { val := h * (precisionAtStage n).val / 16
        property := by
          rw [Rat.div_def]
          apply Rat.mul_pos
          · exact Rat.mul_pos hpos (precisionAtStage n).property
          · exact (Rat.inv_pos).2 (by decide +kernel) }
    256 * (eps.val.den + 1)
  else
    0

/-- The tangent-chart rectangle evaluator has the derivative kernel
`1 / (1 + x^2)` at its zero increment.  This is an actual
`HasForwardDerivativeAt` certificate for the charted evaluator; transferring
it to the geometric arctangent still requires a quantitative equivalence
transport theorem. -/
def arctanIntegralRectangleTangentChartOnHalf_forwardDerivativeAtZero
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    HasForwardDerivativeAt
      (arctanIntegralRectangleTangentChartOnHalf x hx0)
      0 (RealCompute.ofRat (ArctanGeometry.integralKernel x)) := by
  refine
    { x_mem := by
        change (0 : Rat) <= 0 /\ 0 <= (1 : Rat) / 2
        exact ⟨Rat.le_refl, by decide +kernel⟩
      derivative_valid := by
        exact RealCompute.ofRat_valid (ArctanGeometry.integralKernel x)
      stepPrecision := fun n => 2 * (n + 1)
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hzeroAdd : (0 : Rat) + h = h := by grind
  have hmemAtH : inDomainInterval
      (arctanIntegralRectangleTangentChartOnHalf x hx0).lower
      (arctanIntegralRectangleTangentChartOnHalf x hx0).upper h := by
    exact hzeroAdd ▸ hmem
  have hzero : inDomainInterval
      (arctanIntegralRectangleTangentChartOnHalf x hx0).lower
      (arctanIntegralRectangleTangentChartOnHalf x hx0).upper 0 := by
    change (0 : Rat) <= 0 /\ 0 <= (1 : Rat) / 2
    exact ⟨Rat.le_refl, by decide +kernel⟩
  have herror : h + h * h <= (precisionAtStage n).val := by
    change h <= 1 / (((2 * (n + 1) : Nat) : Rat)) at hsmall
    exact tangentChart_stepError_le_precision n hpos hsmall
  have htmem := ArctanGeometry.tangentChartIncrement_mem_unit_of_mem_half
    hx0 hmemAtH.1 hmemAtH.2
  have hquotientContains :=
    ArctanGeometry.arctanIntegralRectangleCompute_tangentChart_quotient_kernel_contains
      hx0 hx1 hpos 0
  have hzeroChart : ArctanGeometry.tangentChartIncrement x 0 = 0 := by
    unfold ArctanGeometry.tangentChartIncrement
    rw [Rat.div_def, Rat.zero_mul]
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hleftOrdered :
      (ArctanGeometry.arctanIntegralRectangleCompute
        (ArctanGeometry.tangentChartIncrement x h) 0).lo <=
      (ArctanGeometry.arctanIntegralRectangleCompute
        (ArctanGeometry.tangentChartIncrement x h) 0).hi := by
    have hwidth := ArctanGeometry.arctanIntegralRectangleCompute_ordered
      htmem.1 0
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hzeroOrdered :
      (ArctanGeometry.arctanIntegralRectangleCompute 0 0).lo <=
      (ArctanGeometry.arctanIntegralRectangleCompute 0 0).hi := by
    have hwidth := ArctanGeometry.arctanIntegralRectangleCompute_ordered
      (x := 0) (by decide +kernel) 0
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hquotientOrdered :
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute
          (ArctanGeometry.tangentChartIncrement x h) 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).lo <=
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute
          (ArctanGeometry.tangentChartIncrement x h) 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi := by
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat
    rw [if_pos hinv]
    apply Rat.mul_le_mul_of_nonneg_left _ hinv
    grind [Rat.sub_eq_add_neg]
  suffices hnear : intervalNearAtPrecision
      (QInterval.differenceQuotient
        ((arctanIntegralRectangleTangentChartOnHalf x hx0).compute h hmemAtH 0)
        ((arctanIntegralRectangleTangentChartOnHalf x hx0).compute 0 hzero 0) h)
      ((RealCompute.ofRat (ArctanGeometry.integralKernel x)).compute 0) n by
    simpa only [Rat.zero_add] using hnear
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      ((arctanIntegralRectangleTangentChartOnHalf x hx0).compute h hmemAtH 0)
      ((arctanIntegralRectangleTangentChartOnHalf x hx0).compute 0 hzero 0) h)
    ((RealCompute.ofRat (ArctanGeometry.integralKernel x)).compute 0) n
  rw [arctanIntegralRectangleTangentChartOnHalf_compute x hx0 h hmemAtH 0,
    arctanIntegralRectangleTangentChartOnHalf_compute x hx0 0 hzero 0,
    hzeroChart]
  unfold intervalNearAtPrecision QInterval.NearAt
  unfold QInterval.ContainsInterval at hquotientContains
  simp only [RealCompute.ofRat_compute]
  constructor
  · calc
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute
          (ArctanGeometry.tangentChartIncrement x h) 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).lo <=
          (QInterval.differenceQuotient
            (ArctanGeometry.arctanIntegralRectangleCompute
              (ArctanGeometry.tangentChartIncrement x h) 0)
            (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi :=
        hquotientOrdered
      _ <= ArctanGeometry.integralKernel x := hquotientContains.2
      _ <= ArctanGeometry.integralKernel x + (precisionAtStage n).val := by
        grind
  constructor
  · calc
      ArctanGeometry.integralKernel x =
          (ArctanGeometry.integralKernel x - (h + h * h)) + (h + h * h) := by
            grind [Rat.sub_eq_add_neg]
      _ <=
          (QInterval.differenceQuotient
            (ArctanGeometry.arctanIntegralRectangleCompute
              (ArctanGeometry.tangentChartIncrement x h) 0)
            (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi +
              (precisionAtStage n).val := by
            have hlower := hquotientContains.1
            grind [Rat.sub_eq_add_neg]
  constructor
  · calc
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute
          (ArctanGeometry.tangentChartIncrement x h) 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).width <=
          ({ lo := ArctanGeometry.integralKernel x - (h + h * h),
             hi := ArctanGeometry.integralKernel x } : QInterval).width :=
        QInterval.width_le_of_contains hquotientContains
      _ = h + h * h := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg]
      _ <= (precisionAtStage n).val := herror
  · unfold QInterval.width
    rw [show ArctanGeometry.integralKernel x -
      ArctanGeometry.integralKernel x = 0 by grind]
    exact Rat.le_of_lt (precisionAtStage n).property

/-- On the full unit branch, the ordinary rectangle arctangent has the
expected forward derivative.  The proof transports the local chart quotient
through finite overlapping brackets whose evaluation precision is explicitly
scaled by the rational step; the right half uses the local tangent-chart pole
margin rather than a second arctangent construction. -/
def arctanIntegralRectangleOnUnit_forwardDerivativeAt
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    HasForwardDerivativeAt arctanIntegralRectangleOnUnit x
      (RealCompute.ofRat (ArctanGeometry.integralKernel x)) := by
  refine
    { x_mem := ⟨hx0, hx1⟩
      derivative_valid := RealCompute.ofRat_valid (ArctanGeometry.integralKernel x)
      stepPrecision := fun n => 8 * (n + 1)
      evalPrecision := arctanRectangleTangentTransportPrecision
      close := ?_ }
  intro h n hmem hpos hsmall
  change 0 <= x + h /\ x + h <= 1 at hmem
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have hsmall' : h <= 1 / (((8 * (n + 1) : Nat) : Rat)) := by
    change h <= 1 / (((8 * (n + 1) : Nat) : Rat)) at hsmall
    exact hsmall
  have hkernelError : h + h * h <= (precisionAtStage n).val / 4 :=
    tangentChart_stepError_le_quarterPrecision n hpos hsmall'
  let eps : QPos :=
    { val := h * (precisionAtStage n).val / 16
      property := by
        rw [Rat.div_def]
        apply Rat.mul_pos
        · exact Rat.mul_pos hpos (precisionAtStage n).property
        · exact (Rat.inv_pos).2 (by decide +kernel) }
  let N : Nat := 256 * (eps.val.den + 1)
  have hN : arctanRectangleTangentTransportPrecision h n = N := by
    simp only [arctanRectangleTangentTransportPrecision, dif_pos hpos]
    rfl
  have hNrect : 4 * (eps.val.den + 1) <= N := by
    dsimp [N]
    omega
  have hNchart : 256 * (eps.val.den + 1) <= N := by
    dsimp [N]
    exact Nat.le_refl _
  have ht0 : 0 <= ArctanGeometry.tangentChartIncrement x h :=
    Rat.le_of_lt (ArctanGeometry.tangentChartIncrement_pos hx0 hpos)
  have ht1 : ArctanGeometry.tangentChartIncrement x h <= 1 :=
    Rat.le_trans (ArctanGeometry.tangentChartIncrement_le_step hx0 hpos) hh1
  have hchartParam := ArctanGeometry.chartAddParameter_tangentChartIncrement
    hx0 hxh0
  have hchartImage : RationalCircle.Trigonometry.chartAddParameter x
      (ArctanGeometry.tangentChartIncrement x h) <= 1 := by
    rw [hchartParam]
    exact hmem.2
  have hAplusWidth :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      hxh0 hmem.2 eps N hNrect
  have hAxWidth :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      hx0 hx1 eps N hNrect
  have hCWidth := ArctanGeometry.tangentChartAreaLoopCompute_width_le_eps_on_unit
    hx0 hx1 hpos hmem.2 eps N hNchart
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscaleEps : (1 / h) * eps.val = (precisionAtStage n).val / 16 := by
    dsimp [eps]
    rw [Rat.div_def]
    have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h (Rat.ne_of_gt hpos)
    grind [Rat.mul_assoc, Rat.mul_comm]
  let C : QInterval := QInterval.scaleRat (1 / h)
    (ArctanGeometry.chartAddAreaLoopCompute x
      (ArctanGeometry.tangentChartIncrement x h) N)
  let P : QInterval := QInterval.differenceQuotient
    (ArctanGeometry.arctanIntegralRectangleCompute
      (ArctanGeometry.tangentChartIncrement x h) N)
    (ArctanGeometry.arctanIntegralRectangleCompute 0 N) h
  let Q : QInterval := QInterval.differenceQuotient
    (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
    (ArctanGeometry.arctanIntegralRectangleCompute x N) h
  have hCcontainsP : C.ContainsInterval P := by
    dsimp [C, P]
    exact ArctanGeometry.tangentChart_transport_scaled_contains_chartQuotient_on_unit
      hx0 hx1 hpos hmem.2 N
  have hCoverlapsQ : C.Overlaps Q := by
    dsimp [C, Q]
    exact ArctanGeometry.tangentChart_transport_scaled_overlaps_forwardQuotient_on_unit
      hx0 hx1 hpos hmem.2 N
  have hPkernel :
      ({ lo := ArctanGeometry.integralKernel x - (h + h * h),
         hi := ArctanGeometry.integralKernel x } : QInterval).ContainsInterval P := by
    dsimp [P]
    exact ArctanGeometry.arctanIntegralRectangleCompute_tangentChart_quotient_kernel_contains
      hx0 hx1 hpos N
  have hCwidth : C.width <= (precisionAtStage n).val / 16 := by
    dsimp [C]
    rw [QInterval.scaleRat_width_of_nonneg hinv]
    calc
      (1 / h) *
          (ArctanGeometry.chartAddAreaLoopCompute x
            (ArctanGeometry.tangentChartIncrement x h) N).width <=
          (1 / h) * eps.val :=
        Rat.mul_le_mul_of_nonneg_left hCWidth hinv
      _ = (precisionAtStage n).val / 16 := hscaleEps
  have hQwidth : Q.width <= (precisionAtStage n).val / 8 := by
    dsimp [Q]
    unfold QInterval.differenceQuotient QInterval.divRat
    rw [QInterval.scaleRat_width_of_nonneg hinv, QInterval.sub_width]
    calc
      (1 / h) *
          ((ArctanGeometry.arctanIntegralRectangleCompute (x + h) N).width +
            (ArctanGeometry.arctanIntegralRectangleCompute x N).width) <=
          (1 / h) * (eps.val + eps.val) :=
        Rat.mul_le_mul_of_nonneg_left
          (rat_add_le_add hAplusWidth hAxWidth) hinv
      _ = 2 * ((1 / h) * eps.val) := by
        grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
      _ = (precisionAtStage n).val / 8 := by
        rw [hscaleEps]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hPordered : P.lo <= P.hi := by
    dsimp [P]
    have hleft := ArctanGeometry.arctanIntegralRectangleCompute_ordered ht0 N
    have hzero := ArctanGeometry.arctanIntegralRectangleCompute_ordered
      (x := 0) (by decide +kernel) N
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat
    rw [if_pos hinv]
    apply Rat.mul_le_mul_of_nonneg_left _ hinv
    unfold QInterval.width at hleft hzero
    grind [Rat.sub_eq_add_neg]
  have hnear : intervalNearAtPrecision Q
      { lo := ArctanGeometry.integralKernel x,
        hi := ArctanGeometry.integralKernel x } n := by
    unfold intervalNearAtPrecision QInterval.NearAt
      QInterval.ContainsInterval QInterval.Overlaps at *
    constructor
    · calc
        Q.lo <= C.hi := hCoverlapsQ.2
        _ = C.lo + C.width := by
          unfold QInterval.width
          grind [Rat.sub_eq_add_neg]
        _ <= P.lo + C.width := (Rat.add_le_add_right).2 hCcontainsP.1
        _ <= P.hi + C.width := (Rat.add_le_add_right).2 hPordered
        _ <= ArctanGeometry.integralKernel x + C.width :=
          (Rat.add_le_add_right).2 hPkernel.2
        _ <= ArctanGeometry.integralKernel x + (precisionAtStage n).val := by
          grind
    constructor
    · calc
        ArctanGeometry.integralKernel x =
            (ArctanGeometry.integralKernel x - (h + h * h)) + (h + h * h) := by
              grind [Rat.sub_eq_add_neg]
        _ <= P.lo + (h + h * h) :=
          (Rat.add_le_add_right).2 hPkernel.1
        _ <= C.hi + (h + h * h) :=
          (Rat.add_le_add_right).2 (Rat.le_trans hPordered hCcontainsP.2)
        _ = C.lo + C.width + (h + h * h) := by
          unfold QInterval.width
          grind [Rat.sub_eq_add_neg]
        _ <= Q.hi + C.width + (h + h * h) := by
          exact (Rat.add_le_add_right).2
            ((Rat.add_le_add_right).2 hCoverlapsQ.1)
        _ <= Q.hi + (precisionAtStage n).val := by
          grind
    constructor
    · exact Rat.le_trans hQwidth (by
        have hpositive := Rat.le_of_lt (precisionAtStage n).property
        grind)
    · unfold QInterval.width
      rw [show ArctanGeometry.integralKernel x -
        ArctanGeometry.integralKernel x = 0 by grind]
      exact Rat.le_of_lt (precisionAtStage n).property
  suffices hnearFunction : intervalNearAtPrecision
      (QInterval.differenceQuotient
        (arctanIntegralRectangleOnUnit.compute (x + h) hmem
          (arctanRectangleTangentTransportPrecision h n))
        (arctanIntegralRectangleOnUnit.compute x
          (by exact ⟨hx0, hx1⟩)
          (arctanRectangleTangentTransportPrecision h n)) h)
      ((RealCompute.ofRat (ArctanGeometry.integralKernel x)).compute
        (arctanRectangleTangentTransportPrecision h n)) n by
    exact hnearFunction
  rw [hN]
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      (arctanIntegralRectangleOnUnit.compute (x + h) hmem N)
      (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩ N) h)
    { lo := ArctanGeometry.integralKernel x,
      hi := ArctanGeometry.integralKernel x } n
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      (arctanIntegralRectangleOnUnit.compute (x + h) hmem N)
      (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩ N) h)
    { lo := ArctanGeometry.integralKernel x,
      hi := ArctanGeometry.integralKernel x } n at hnear
  exact hnear

/-! The next three finite estimates reserve precision for transporting the
forward rectangle certificate across a negative step.  They use only rational
arithmetic and the project-wide `1/n` stage schedule. -/

private theorem twoSided_precision_stage_le_eighth (n : Nat) :
    (precisionAtStage (8 * (n + 1))).val <=
      (precisionAtStage n).val / 8 := by
  let m : Rat := ((n + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hstage : 1 / m <= (precisionAtStage n).val := by
    dsimp [m]
    by_cases hn : n = 0
    · subst n
      decide +kernel
    · simp only [precisionAtStage, dif_neg hn]
      exact FTC.one_div_nat_antitone (Nat.pos_of_ne_zero hn)
        (Nat.succ_pos n) (Nat.le_succ n)
  have hfactor : 0 <= (1 : Rat) / 8 := by decide +kernel
  have hscale := Rat.mul_le_mul_of_nonneg_left hstage hfactor
  have hindex : 8 * (n + 1) ≠ 0 := by omega
  simp only [precisionAtStage, dif_neg hindex]
  calc
    1 / (((8 * (n + 1) : Nat) : Rat)) = ((1 : Rat) / 8) * (1 / m) := by
      rw [Rat.natCast_mul]
      change 1 / (8 * m) = ((1 : Rat) / 8) * (1 / m)
      rw [Rat.div_def, Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= ((1 : Rat) / 8) * (precisionAtStage n).val := hscale
    _ = (precisionAtStage n).val / 8 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem twoSided_step_le_quarterPrecision
    {k : Rat} (n : Nat)
    (hsmall : k <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    2 * k <= (precisionAtStage n).val / 4 := by
  let m : Rat := ((n + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hsmall' : k <= 1 / (72 * m) := by
    simpa [m] using hsmall
  have hdenpos : 0 < 72 * m := Rat.mul_pos (by decide +kernel) hmpos
  have hthirtySixPos : 0 < 36 * m := Rat.mul_pos (by decide +kernel) hmpos
  have htwice : 2 * k <= 1 / (36 * m) := by
    apply Rat.le_of_mul_le_mul_right (c := 36 * m)
    · calc
        (2 * k) * (36 * m) = k * (72 * m) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (1 / (72 * m)) * (72 * m) :=
          Rat.mul_le_mul_of_nonneg_right hsmall' (Rat.le_of_lt hdenpos)
        _ = 1 := by
          rw [Rat.div_def]
          have hne : 72 * m ≠ 0 := Rat.ne_of_gt hdenpos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ = (1 / (36 * m)) * (36 * m) := by
          rw [Rat.div_def]
          have hne : 36 * m ≠ 0 := Rat.ne_of_gt hthirtySixPos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hthirtySixPos
  have hstage : 1 / m <= (precisionAtStage n).val := by
    dsimp [m]
    by_cases hn : n = 0
    · subst n
      decide +kernel
    · simp only [precisionAtStage, dif_neg hn]
      exact FTC.one_div_nat_antitone (Nat.pos_of_ne_zero hn)
        (Nat.succ_pos n) (Nat.le_succ n)
  have hsixthirtySix : 1 / (36 * m) <= (precisionAtStage n).val / 36 := by
    have hfactor : 0 <= (1 : Rat) / 36 := by decide +kernel
    have hscale := Rat.mul_le_mul_of_nonneg_left hstage hfactor
    calc
      1 / (36 * m) = ((1 : Rat) / 36) * (1 / m) := by
        rw [Rat.div_def, Rat.inv_mul_rev]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((1 : Rat) / 36) * (precisionAtStage n).val := hscale
      _ = (precisionAtStage n).val / 36 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hprecisionNonneg : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  calc
    2 * k <= 1 / (36 * m) := htwice
    _ <= (precisionAtStage n).val / 36 := hsixthirtySix
    _ <= (precisionAtStage n).val / 4 := by
      grind [Rat.div_def]

private theorem twoSided_step_implies_forward
    {k : Rat} (n : Nat)
    (hsmall : k <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    k <= 1 / (((8 * (8 * (n + 1) + 1) : Nat) : Rat)) := by
  have hsmallDenPos : 0 < 72 * (n + 1) := by omega
  have hforwardDenPos : 0 < 8 * (8 * (n + 1) + 1) := by omega
  have hdenOrder : 8 * (8 * (n + 1) + 1) <= 72 * (n + 1) := by omega
  have hreciprocal := FTC.one_div_nat_antitone hforwardDenPos hsmallDenPos
    hdenOrder
  calc
    k <= 1 / (((72 * (n + 1) : Nat) : Rat)) := hsmall
    _ <= 1 / (((8 * (8 * (n + 1) + 1) : Nat) : Rat)) := hreciprocal

private theorem intervalNearAtPrecision_weaken
    {I J : QInterval} {m n : Nat}
    (hnear : intervalNearAtPrecision I J m)
    (hprecision : (precisionAtStage m).val <= (precisionAtStage n).val) :
    intervalNearAtPrecision I J n := by
  unfold intervalNearAtPrecision QInterval.NearAt at hnear ⊢
  rcases hnear with ⟨hleft, hright, hwidthI, hwidthJ⟩
  exact ⟨Rat.le_trans hleft ((Rat.add_le_add_left).2 hprecision),
    Rat.le_trans hright ((Rat.add_le_add_left).2 hprecision),
    Rat.le_trans hwidthI hprecision, Rat.le_trans hwidthJ hprecision⟩

/-- The rectangle arctangent has a certified forward derivative equal to one
at the rational endpoint zero.  This uses the direct finite tangent bracket;
it does not yet assert a two-sided derivative away from that endpoint. -/
def arctanIntegralRectangleOnUnit_forwardDerivativeAtZero :
    HasForwardDerivativeAt arctanIntegralRectangleOnUnit 0 RealCompute.one := by
  refine
    { x_mem := by
        constructor <;> decide +kernel
      derivative_valid := by
        change RealCompute.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
        exact RealCompute.ofRat_valid (1 : Rat)
      stepPrecision := fun n => if n = 0 then 1 else n
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hprecision : h <= (precisionAtStage n).val := by
    change h <= 1 / (((if n = 0 then 1 else n : Nat) : Rat)) at hsmall
    by_cases hn : n = 0
    · subst n
      calc
        h <= 1 / (1 : Rat) := by
          change h <= 1 / (1 : Rat) at hsmall
          exact hsmall
        _ = (precisionAtStage 0).val := by decide +kernel
    · simpa [precisionAtStage, hn] using hsmall
  have hprecision_le_one : (precisionAtStage n).val <= 1 := by
    by_cases hn : n = 0
    · subst n
      decide +kernel
    ·
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hnat : (1 : Rat) <= (n : Rat) := by
        exact_mod_cast hnpos
      have hfrac : 1 / (n : Rat) <= 1 := by
        apply Rat.le_of_mul_le_mul_right (c := (n : Rat))
        · calc
            (1 / (n : Rat)) * (n : Rat) = 1 := by
              have hne : (n : Rat) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt hnpos)
              rw [Rat.div_def]
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
            _ <= 1 * (n : Rat) := by simpa using hnat
        · exact_mod_cast hnpos
      simpa only [precisionAtStage, dif_neg hn] using hfrac
  have hle_one : h <= 1 :=
    Rat.le_trans hprecision hprecision_le_one
  have hsquare : h * h <= (precisionAtStage n).val := by
    calc
      h * h <= h * 1 :=
        Rat.mul_le_mul_of_nonneg_left hle_one (Rat.le_of_lt hpos)
      _ = h := by grind
      _ <= (precisionAtStage n).val := hprecision
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hhordered :
      (ArctanGeometry.arctanIntegralRectangleCompute h 0).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi := by
    have hwidth :=
      ArctanGeometry.arctanIntegralRectangleCompute_ordered
        (Rat.le_of_lt hpos) 0
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hzeroordered :
      (ArctanGeometry.arctanIntegralRectangleCompute 0 0).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0).hi := by
    have hwidth :=
      ArctanGeometry.arctanIntegralRectangleCompute_ordered
        (x := 0) (by decide +kernel) 0
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hquotient_ordered :
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute h 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).lo <=
        (QInterval.differenceQuotient
          (ArctanGeometry.arctanIntegralRectangleCompute h 0)
          (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi := by
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat
    rw [if_pos hinv]
    apply Rat.mul_le_mul_of_nonneg_left _ hinv
    grind [Rat.sub_eq_add_neg]
  have hcontains :=
    ArctanGeometry.arctanIntegralRectangleCompute_zero_tangent_quotient_contains
      hpos 0
  unfold QInterval.ContainsInterval at hcontains
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      ((arctanIntegralRectangleFor (0 + h) hmem.1 hmem.2).compute 0)
      ((arctanIntegralRectangleFor 0 (by decide +kernel) (by decide +kernel)).compute 0)
      h)
    (RealCompute.one.compute 0) n
  simp only [arctanIntegralRectangleFor_compute_eq, Rat.zero_add,
    RealCompute.one, RealCompute.ofRat_compute]
  unfold intervalNearAtPrecision QInterval.NearAt
  constructor
  · calc
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute h 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).lo <=
          (QInterval.differenceQuotient
            (ArctanGeometry.arctanIntegralRectangleCompute h 0)
            (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi :=
        hquotient_ordered
      _ <= 1 := hcontains.2
      _ <= 1 + (precisionAtStage n).val := by
        calc
          1 = 1 + 0 := by grind
          _ <= 1 + (precisionAtStage n).val :=
            (Rat.add_le_add_left).2
              (Rat.le_of_lt (precisionAtStage n).property)
  constructor
  · calc
      1 = (1 - h * h) + h * h := by
        grind [Rat.sub_eq_add_neg]
      _ <=
          (QInterval.differenceQuotient
            (ArctanGeometry.arctanIntegralRectangleCompute h 0)
            (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi +
            (precisionAtStage n).val := by
          have hlower :
              1 - h * h <=
                (QInterval.differenceQuotient
                  (ArctanGeometry.arctanIntegralRectangleCompute h 0)
                  (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi :=
            Rat.le_trans hcontains.1 hquotient_ordered
          grind [Rat.sub_eq_add_neg]
  constructor
  · unfold QInterval.width
    calc
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute h 0)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).hi -
          (QInterval.differenceQuotient
            (ArctanGeometry.arctanIntegralRectangleCompute h 0)
            (ArctanGeometry.arctanIntegralRectangleCompute 0 0) h).lo <=
          1 - (1 - h * h) := by
            grind [Rat.sub_eq_add_neg]
      _ = h * h := by
        grind [Rat.sub_eq_add_neg]
      _ <= (precisionAtStage n).val := hsquare
  · unfold QInterval.width
    rw [show (1 : Rat) - 1 = 0 by decide +kernel]
    exact Rat.le_of_lt (precisionAtStage n).property

/-- The geometric rectangle construction has a two-sided interval derivative
on the whole rational unit branch.  A negative step is reversed into the
positive step based at its left endpoint; the kernel's finite Lipschitz bound
then transports the derivative value back to the requested basepoint. -/
def arctanIntegralRectangleOnUnit_hasDerivative :
    HasDerivativeOnInterval arctanIntegralRectangleOnUnit
      arctanKernelIntervalAtOne := by
  refine
    { same_lower := rfl
      same_upper := rfl
      stepPrecision := fun n => 72 * (n + 1)
      evalPrecision := fun _x h n =>
        arctanRectangleTangentTransportPrecision (qabs h) (8 * (n + 1))
      close := ?_ }
  intro x h n hx hxh hdx hh hsmall
  change 0 <= x /\ x <= 1 at hx hdx
  change 0 <= x + h /\ x + h <= 1 at hxh
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      (arctanIntegralRectangleOnUnit.compute (x + h) hxh
        (arctanRectangleTangentTransportPrecision (qabs h) (8 * (n + 1))))
      (arctanIntegralRectangleOnUnit.compute x hx
        (arctanRectangleTangentTransportPrecision (qabs h) (8 * (n + 1)))) h)
    { lo := ArctanGeometry.integralKernel x,
      hi := ArctanGeometry.integralKernel x } n
  have hprecisionNonneg : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  have hstageLe :
      (precisionAtStage (8 * (n + 1))).val <= (precisionAtStage n).val := by
    calc
      (precisionAtStage (8 * (n + 1))).val <=
          (precisionAtStage n).val / 8 :=
        twoSided_precision_stage_le_eighth n
      _ <= (precisionAtStage n).val := by
        grind [Rat.div_def]
  by_cases hpos : 0 < h
  · have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
    rw [hqabs] at hsmall ⊢
    have hforwardSmall := twoSided_step_implies_forward n hsmall
    have hforward :=
      (arctanIntegralRectangleOnUnit_forwardDerivativeAt x hx.1 hx.2).close
        h (8 * (n + 1)) hxh hpos hforwardSmall
    have hforward' : intervalNearAtPrecision
        (QInterval.differenceQuotient
          (arctanIntegralRectangleOnUnit.compute (x + h) hxh
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
          (arctanIntegralRectangleOnUnit.compute x hx
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) h)
        { lo := ArctanGeometry.integralKernel x,
          hi := ArctanGeometry.integralKernel x }
        (8 * (n + 1)) := by
      change intervalNearAtPrecision
        (QInterval.differenceQuotient
          (arctanIntegralRectangleOnUnit.compute (x + h) hxh
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
          (arctanIntegralRectangleOnUnit.compute x hx
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) h)
        { lo := ArctanGeometry.integralKernel x,
          hi := ArctanGeometry.integralKernel x }
        (8 * (n + 1)) at hforward
      simpa [RealCompute.ofRat_compute] using hforward
    exact intervalNearAtPrecision_weaken hforward' hstageLe
  · have hneg : h < 0 := by grind
    let k : Rat := -h
    have hkpos : 0 < k := by
      dsimp [k]
      grind
    have hk0 : 0 <= k := Rat.le_of_lt hkpos
    have hqabs : qabs h = k := by
      dsimp [k]
      exact qabs_eq_neg_of_nonpos (Rat.le_of_lt hneg)
    rw [hqabs] at hsmall ⊢
    have hforwardSmall := twoSided_step_implies_forward n hsmall
    have hy : 0 <= x + h /\ x + h <= 1 := hxh
    have hyplus : 0 <= (x + h) + k /\ (x + h) + k <= 1 := by
      rw [show x + h + k = x by dsimp [k]; grind]
      exact hx
    have hforward :=
      (arctanIntegralRectangleOnUnit_forwardDerivativeAt (x + h) hy.1 hy.2).close
        k (8 * (n + 1)) hyplus hkpos hforwardSmall
    have hforward' : intervalNearAtPrecision
        (QInterval.differenceQuotient
          (arctanIntegralRectangleOnUnit.compute x hx
            (arctanRectangleTangentTransportPrecision k (8 * (n + 1))))
          (arctanIntegralRectangleOnUnit.compute (x + h) hxh
            (arctanRectangleTangentTransportPrecision k (8 * (n + 1)))) k)
        { lo := ArctanGeometry.integralKernel (x + h),
          hi := ArctanGeometry.integralKernel (x + h) }
        (8 * (n + 1)) := by
      have hsum : x + h + k = x := by
        dsimp [k]
        grind
      simpa [hsum, arctanIntegralRectangleOnUnit_forwardDerivativeAt,
        RealCompute.ofRat_compute] using hforward
    have hkernelLip := oneOverOnePlusSquare_lipschitz_on_unit.2
      (x + h) x hy.1 hy.2 hx.1 hx.2
    have hkernelDiff :
        qabs (ArctanGeometry.integralKernel (x + h) -
          ArctanGeometry.integralKernel x) <= 2 * k := by
      simpa [ArctanGeometry.integralKernel, show x - (x + h) = k by
        dsimp [k]
        grind, qabs_eq_self_of_nonneg hk0] using hkernelLip
    have hkernelForward : ArctanGeometry.integralKernel (x + h) <=
        ArctanGeometry.integralKernel x + 2 * k := by
      have h := Rat.le_trans
        (self_le_qabs (ArctanGeometry.integralKernel (x + h) -
          ArctanGeometry.integralKernel x)) hkernelDiff
      grind [Rat.sub_eq_add_neg]
    have hkernelBackward : ArctanGeometry.integralKernel x <=
        ArctanGeometry.integralKernel (x + h) + 2 * k := by
      have hneg := Rat.neg_le_neg
        (neg_qabs_le_self (ArctanGeometry.integralKernel (x + h) -
          ArctanGeometry.integralKernel x))
      have hrev : -(ArctanGeometry.integralKernel (x + h) -
          ArctanGeometry.integralKernel x) <=
          qabs (ArctanGeometry.integralKernel (x + h) -
            ArctanGeometry.integralKernel x) := by
        calc
          -(ArctanGeometry.integralKernel (x + h) -
              ArctanGeometry.integralKernel x) <=
              -(-qabs (ArctanGeometry.integralKernel (x + h) -
                ArctanGeometry.integralKernel x)) := hneg
          _ = qabs (ArctanGeometry.integralKernel (x + h) -
            ArctanGeometry.integralKernel x) := by grind
      have h := Rat.le_trans hrev hkernelDiff
      grind [Rat.sub_eq_add_neg]
    have htransportBudget :
        (precisionAtStage (8 * (n + 1))).val + 2 * k <=
          (precisionAtStage n).val := by
      have hstep := twoSided_step_le_quarterPrecision n hsmall
      calc
        (precisionAtStage (8 * (n + 1))).val + 2 * k <=
            (precisionAtStage n).val / 8 + (precisionAtStage n).val / 4 :=
          rat_add_le_add (twoSided_precision_stage_le_eighth n) hstep
        _ <= (precisionAtStage n).val := by
          grind [Rat.div_def]
    let leftValue : QInterval := arctanIntegralRectangleOnUnit.compute (x + h) hxh
      (arctanRectangleTangentTransportPrecision k (8 * (n + 1)))
    let baseValue : QInterval := arctanIntegralRectangleOnUnit.compute x hx
      (arctanRectangleTangentTransportPrecision k (8 * (n + 1)))
    have hforward'' : intervalNearAtPrecision
        (QInterval.differenceQuotient baseValue leftValue k)
        { lo := ArctanGeometry.integralKernel (x + h),
          hi := ArctanGeometry.integralKernel (x + h) }
        (8 * (n + 1)) := by
      simpa [leftValue, baseValue] using hforward'
    have hquotient :
        QInterval.differenceQuotient leftValue baseValue h =
          QInterval.differenceQuotient baseValue leftValue k := by
      change QInterval.differenceQuotient leftValue baseValue h = _
      have hhneg : h = -k := by
        dsimp [k]
        grind
      rw [hhneg]
      exact QInterval.differenceQuotient_reverse_of_pos (A := baseValue)
        (B := leftValue) hkpos
    have hrewritten : intervalNearAtPrecision
        (QInterval.differenceQuotient leftValue baseValue h)
        { lo := ArctanGeometry.integralKernel (x + h),
          hi := ArctanGeometry.integralKernel (x + h) }
        (8 * (n + 1)) := by
      change intervalNearAtPrecision
        (QInterval.differenceQuotient leftValue baseValue h) _ _
      rw [hquotient]
      exact hforward''
    change intervalNearAtPrecision
      (QInterval.differenceQuotient leftValue baseValue h)
      { lo := ArctanGeometry.integralKernel x,
        hi := ArctanGeometry.integralKernel x } n
    generalize hq : QInterval.differenceQuotient leftValue baseValue h = quotient at hrewritten ⊢
    unfold intervalNearAtPrecision QInterval.NearAt at hrewritten ⊢
    rcases hrewritten with ⟨hleft, hright, hwidth, _⟩
    refine ⟨?_, ?_, Rat.le_trans hwidth hstageLe, ?_⟩
    · calc
        quotient.lo <=
            ArctanGeometry.integralKernel (x + h) +
              (precisionAtStage (8 * (n + 1))).val := hleft
        _ <= ArctanGeometry.integralKernel x + (precisionAtStage n).val := by
          calc
            ArctanGeometry.integralKernel (x + h) +
                (precisionAtStage (8 * (n + 1))).val <=
                (ArctanGeometry.integralKernel x + 2 * k) +
                  (precisionAtStage (8 * (n + 1))).val :=
              (Rat.add_le_add_right).2 hkernelForward
            _ = ArctanGeometry.integralKernel x +
                ((precisionAtStage (8 * (n + 1))).val + 2 * k) := by
              grind [Rat.add_assoc, Rat.add_comm]
            _ <= ArctanGeometry.integralKernel x + (precisionAtStage n).val :=
              (Rat.add_le_add_left).2 htransportBudget
    · calc
        ArctanGeometry.integralKernel x <=
            ArctanGeometry.integralKernel (x + h) + 2 * k := hkernelBackward
        _ <=
            quotient.hi +
              (precisionAtStage (8 * (n + 1))).val + 2 * k := by
                exact (Rat.add_le_add_right).2 hright
        _ <=
            quotient.hi +
              (precisionAtStage n).val := by
                calc
                  quotient.hi +
                      (precisionAtStage (8 * (n + 1))).val + 2 * k =
                      quotient.hi +
                        ((precisionAtStage (8 * (n + 1))).val + 2 * k) := by
                    grind [Rat.add_assoc]
                  _ <= quotient.hi +
                      (precisionAtStage n).val :=
                    (Rat.add_le_add_left).2 htransportBudget
    · unfold QInterval.width
      rw [show ArctanGeometry.integralKernel x -
        ArctanGeometry.integralKernel x = 0 by grind]
      exact Rat.le_of_lt (precisionAtStage n).property

/-- The finite rectangle arctangent is nondecreasing in its upper endpoint on
the rational unit branch. -/
theorem arctanIntegralRectangleOnUnit_nondecreasing :
    NondecreasingOnInterval arctanIntegralRectangleOnUnit := by
  intro x y hx hy hxy n
  change
    ((arctanIntegralRectangleFor x hx.1 hx.2).compute n).lo <=
      ((arctanIntegralRectangleFor y hy.1 hy.2).compute n).hi
  change
    (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
      (ArctanGeometry.arctanIntegralRectangleCompute y n).hi
  exact ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
    hx.1 hxy n

/-- The packaged weak-monotonicity witness for the rectangle arctangent. -/
def arctanIntegralRectangleOnUnit_monotone :
    MonotoneOnInterval arctanIntegralRectangleOnUnit :=
  MonotoneOnInterval.ofNondecreasing
    arctanIntegralRectangleOnUnit_nondecreasing

/-! The finite rectangle evaluator already has the strict separation data
needed by a branch-local inverse search.  Keep this certificate attached to
the same function object as its monotonicity witness; no inverse or attained
real value is introduced here. -/

def arctanIntegralRectangleOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation arctanIntegralRectangleOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun n => 64 * (n + 1)
  separated := by
    intro x y hx hy n hsep
    change
      (ArctanGeometry.arctanIntegralRectangleCompute x
        (64 * (n + 1))).hi <
        (ArctanGeometry.arctanIntegralRectangleCompute y
          (64 * (n + 1))).lo
    exact ArctanGeometry.arctanIntegralRectangleCompute_boxes_strictly_separated
      hx.1 hx.2 hy.1 hy.2 n hsep

/-- A fixed-tolerance, fixed-stage form of rational continuity for the
rectangle arctangent.  It exposes the literal schedule used by the later FTC
cell construction: input distance at most `eps` and any rectangle stage at
least `4 * (eps.den + 1)` give `eps`-near output boxes. -/
theorem arctanIntegralRectangleOnUnit_near_of_qabs_le
    (eps : QPos) (n : Nat) (hn : 4 * (eps.val.den + 1) <= n)
    {x y : Rat}
    (hx : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper x)
    (hy : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper y)
    (hclose : qabs (y - x) <= eps.val) :
    QInterval.NearAt
      (arctanIntegralRectangleOnUnit.compute x hx n)
      (arctanIntegralRectangleOnUnit.compute y hy n) eps := by
  have hwidthX :
      (ArctanGeometry.arctanIntegralRectangleCompute x n).width <= eps.val :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      hx.1 hx.2 eps n hn
  have hwidthY :
      (ArctanGeometry.arctanIntegralRectangleCompute y n).width <= eps.val :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      hy.1 hy.2 eps n hn
  change QInterval.NearAt
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
    (ArctanGeometry.arctanIntegralRectangleCompute y n) eps
  unfold QInterval.NearAt
  rcases (Rat.le_total : x <= y \/ y <= x) with hxy | hyx
  · have hstep0 : 0 <= y - x := by grind [Rat.sub_eq_add_neg]
    have hstep : y - x <= eps.val := by
      rw [← qabs_eq_self_of_nonneg hstep0]
      exact hclose
    have hmonotone :
        (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
          (ArctanGeometry.arctanIntegralRectangleCompute y n).hi :=
      ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        hx.1 hxy n
    have hforward :
        (ArctanGeometry.arctanIntegralRectangleCompute y n).lo -
            (ArctanGeometry.arctanIntegralRectangleCompute x n).hi <=
          y - x := by
      by_cases heq : x = y
      · subst y
        have hordered :=
          ArctanGeometry.arctanIntegralRectangleCompute_ordered hx.1 n
        grind [Rat.sub_eq_add_neg]
      · have hpos : 0 < y - x := by grind [Rat.sub_eq_add_neg]
        have hy1 : y <= (1 : Rat) := by
          simpa [arctanIntegralRectangleOnUnit] using hy.2
        have hsum : x + (y - x) = y := by
          grind [Rat.sub_eq_add_neg]
        have hupper : x + (y - x) <= 1 := by
          calc
            x + (y - x) = y := hsum
            _ <= 1 := hy1
        have h :=
          ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
            hx.1 hx.2 hpos hupper n
        rw [hsum] at h
        exact h
    refine ⟨?_, ?_, hwidthX, hwidthY⟩
    · grind [Rat.sub_eq_add_neg]
    · calc
        (ArctanGeometry.arctanIntegralRectangleCompute y n).lo <=
            (ArctanGeometry.arctanIntegralRectangleCompute x n).hi + (y - x) := by
              grind [Rat.sub_eq_add_neg]
        _ <= (ArctanGeometry.arctanIntegralRectangleCompute x n).hi + eps.val :=
              (Rat.add_le_add_left).2 hstep
  · have hstep0 : 0 <= x - y := by grind [Rat.sub_eq_add_neg]
    have hstep : x - y <= eps.val := by
      have hqabs : qabs (y - x) = x - y := by
        rw [qabs_eq_neg_of_nonpos (by grind [Rat.sub_eq_add_neg])]
        grind [Rat.sub_eq_add_neg]
      rw [← hqabs]
      exact hclose
    have hmonotone :
        (ArctanGeometry.arctanIntegralRectangleCompute y n).lo <=
          (ArctanGeometry.arctanIntegralRectangleCompute x n).hi :=
      ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        hy.1 hyx n
    have hforward :
        (ArctanGeometry.arctanIntegralRectangleCompute x n).lo -
            (ArctanGeometry.arctanIntegralRectangleCompute y n).hi <=
          x - y := by
      by_cases heq : y = x
      · subst y
        have hordered :=
          ArctanGeometry.arctanIntegralRectangleCompute_ordered hx.1 n
        grind [Rat.sub_eq_add_neg]
      · have hpos : 0 < x - y := by grind [Rat.sub_eq_add_neg]
        have hx1 : x <= (1 : Rat) := by
          simpa [arctanIntegralRectangleOnUnit] using hx.2
        have hsum : y + (x - y) = x := by
          grind [Rat.sub_eq_add_neg]
        have hupper : y + (x - y) <= 1 := by
          calc
            y + (x - y) = x := hsum
            _ <= 1 := hx1
        have h :=
          ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
            hy.1 hy.2 hpos hupper n
        rw [hsum] at h
        exact h
    refine ⟨?_, ?_, hwidthX, hwidthY⟩
    · calc
        (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
            (ArctanGeometry.arctanIntegralRectangleCompute y n).hi + (x - y) := by
              grind [Rat.sub_eq_add_neg]
        _ <= (ArctanGeometry.arctanIntegralRectangleCompute y n).hi + eps.val :=
              (Rat.add_le_add_left).2 hstep
    · grind [Rat.sub_eq_add_neg]

/-- The rectangle-integral arctangent is epsilon--delta continuous on the
rational unit branch, in the project's literal finite-box sense.  The input
modulus is the identity: a forward step of size `h` changes the enclosed
arctangent by at most `h`, and stage
`4 * (eps.den + 1)` makes each rectangle box no wider than `eps`.  This proof
uses neither a topology import nor completeness of a real-number model. -/
theorem arctanIntegralRectangleOnUnit_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn arctanIntegralRectangleOnUnit := by
  intro eps
  let delta : QPos := ⟨eps.val, eps.property⟩
  let n : Nat := 4 * (eps.val.den + 1)
  refine ⟨delta, n, ?_⟩
  intro x y hx hy hclose
  apply arctanIntegralRectangleOnUnit_near_of_qabs_le eps n
  · dsimp [n]
    omega
  · simpa [delta] using hclose

/-- A computable modulus for the rectangle arctangent on the unit branch.
At requested stage `n`, an input distance at most `1/(n+1)` is sufficient;
the rectangle evaluation stage is the explicit denominator schedule for the
requested output box `precisionAtStage n`. -/
def arctanIntegralRectangleOnUnit_effectiveModulus :
    EffectiveModulusFor arctanIntegralRectangleOnUnit where
  inputPrecision := fun n => n + 1
  evalPrecision := fun n =>
    4 * ((precisionAtStage n).val.den + 1)
  close := by
    intro x y n hx hy hclose
    let eps : QPos := precisionAtStage n
    let N : Nat := 4 * (eps.val.den + 1)
    have hinput : qabs (y - x) <= eps.val := by
      cases n with
      | zero =>
          have hone : (1 : Rat) / 1 = 1 := by decide +kernel
          simpa [eps, precisionAtStage, hone] using hclose
      | succ n =>
          have hreciprocal :
              1 / (((n + 2 : Nat) : Rat)) <= 1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (by omega) (by omega) (by omega)
          simpa [eps, precisionAtStage] using Rat.le_trans hclose hreciprocal
    have hnear := arctanIntegralRectangleOnUnit_near_of_qabs_le
      eps N (by omega) hx hy hinput
    change intervalNearAtPrecision
      (arctanIntegralRectangleOnUnit.compute x hx N)
      (arctanIntegralRectangleOnUnit.compute y hy N) n
    change QInterval.NearAt
      (arctanIntegralRectangleOnUnit.compute x hx N)
      (arctanIntegralRectangleOnUnit.compute y hy N)
      (precisionAtStage n)
    simpa [eps, N] using hnear

/-- The exact coordinate evaluator on the unit interval.  It is the first
factor in the literal product `x * arctan x` used by the constructive
integration-by-parts route. -/
def coordinateOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => x) 0 1

/-- The coordinate factor in the unit-branch product has the exact
interval-valued derivative `1`.  This supplies one of the two component
certificates needed for the eventual derivative of `x * arctan x`; the
arctangent derivative and the product closure are separate work. -/
def coordinateOnUnitDerivative :
    HasDerivativeOnInterval coordinateOnUnit
      (FunctionOnInterval.exactRat (fun _x => 1) 0 1) := by
  simpa [coordinateOnUnit] using
    FunctionOnInterval.exactRatIdDerivative 0 1

theorem coordinateOnUnit_bounds :
    forall x (hx : inDomainInterval coordinateOnUnit.lower
      coordinateOnUnit.upper x), Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (coordinateOnUnit.compute x hx n).lo /\
          (coordinateOnUnit.compute x hx n).hi <= B := by
  intro x hx
  refine ⟨1, by decide +kernel, ?_⟩
  intro n
  change 0 <= x /\ x <= 1
  exact hx

/-- Uniform nonnegative bounds for the geometric arctangent rectangles on
the unit branch. -/
theorem arctanIntegralRectangleOnUnit_bounds :
    forall x (hx : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper x), Exists fun B : Rat => 0 < B /\
        forall n, 0 <= (arctanIntegralRectangleOnUnit.compute x hx n).lo /\
          (arctanIntegralRectangleOnUnit.compute x hx n).hi <= B := by
  intro x hx
  refine ⟨1, by decide +kernel, ?_⟩
  intro n
  change
    0 <= (ArctanGeometry.arctanIntegralRectangleCompute x n).lo /\
      (ArctanGeometry.arctanIntegralRectangleCompute x n).hi <= 1
  constructor
  · exact ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative
      hx.1 n
  · exact Rat.le_trans
      (ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input hx.1 n)
      hx.2

/-- The certified evaluator-level product `x * arctan x` on the unit
interval.  The construction uses only positive interval multiplication; it
does not assert a product derivative or an integral identity. -/
def coordinateTimesArctanIntegralRectangleOnUnit : FunctionOnInterval :=
  FunctionOnInterval.mulOfNonnegBounded
    coordinateOnUnit arctanIntegralRectangleOnUnit rfl rfl
    coordinateOnUnit_bounds arctanIntegralRectangleOnUnit_bounds

/-- At every rational input and precision, the product evaluator is the
literal interval product of the exact coordinate and arctangent rectangle
boxes. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_compute
    (x : Rat)
    (hx : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper x) (n : Nat) :
    coordinateTimesArctanIntegralRectangleOnUnit.compute x hx n =
      QBox.mulRealInterval x x
        (ArctanGeometry.arctanIntegralRectangleCompute x n).lo
        (ArctanGeometry.arctanIntegralRectangleCompute x n).hi := by
  rfl

/-- Since both factors are nonnegative on the unit interval, the four-corner
interval product for `x * arctan x` reduces to its lower--lower and
upper--upper corners. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg
    (x : Rat)
    (hx : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper x) (n : Nat) :
    coordinateTimesArctanIntegralRectangleOnUnit.compute x hx n =
      { lo := x * (ArctanGeometry.arctanIntegralRectangleCompute x n).lo,
        hi := x * (ArctanGeometry.arctanIntegralRectangleCompute x n).hi } := by
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute x hx n]
  apply QBox.mulRealInterval_of_nonneg
  · exact hx.1
  · exact Rat.le_refl
  · exact ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative
      hx.1 n
  · have hordered :
        0 <= (ArctanGeometry.arctanIntegralRectangleCompute x n).width :=
      ArctanGeometry.arctanIntegralRectangleCompute_ordered hx.1 n
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]

/-- The positive product branch x times arctan x is nondecreasing on the
unit interval.  This is a finite interval-order certificate for the
monotone-piece integration-by-parts route; it is not a product-derivative
or FTC theorem. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_nondecreasing :
    NondecreasingOnInterval coordinateTimesArctanIntegralRectangleOnUnit := by
  intro x y hx hy hxy n
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg x hx n,
    coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg y hy n]
  change
    x * (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
      y * (ArctanGeometry.arctanIntegralRectangleCompute y n).hi
  have hlow : 0 <= (ArctanGeometry.arctanIntegralRectangleCompute x n).lo :=
    ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative hx.1 n
  have hcross :
      (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute y n).hi :=
    ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
      hx.1 hxy n
  calc
    x * (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
        y * (ArctanGeometry.arctanIntegralRectangleCompute x n).lo :=
      Rat.mul_le_mul_of_nonneg_right hxy hlow
    _ <= y * (ArctanGeometry.arctanIntegralRectangleCompute y n).hi :=
      Rat.mul_le_mul_of_nonneg_left hcross hy.1

/-- The packaged monotonicity witness for the positive product branch
x times arctan x. -/
def coordinateTimesArctanIntegralRectangleOnUnit_monotone :
    MonotoneOnInterval coordinateTimesArctanIntegralRectangleOnUnit :=
  MonotoneOnInterval.ofNondecreasing
    coordinateTimesArctanIntegralRectangleOnUnit_nondecreasing

/-- At the left endpoint, the positive product branch is the exact zero
interval at every stage. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_toRealFunRaw_compute_zero
    (n : Nat) :
    coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw.compute 0 n =
      { lo := 0, hi := 0 } := by
  have hzero : inDomainInterval
      coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper 0 := by
    change (0 : Rat) <= 0 /\ 0 <= 1
    exact ⟨Rat.le_refl, by decide +kernel⟩
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    coordinateTimesArctanIntegralRectangleOnUnit (x := 0)
      (hx := hzero) n]
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg 0
    hzero n]
  grind

/-- At the right endpoint, the positive product branch literally has the
geometric rectangle box for arctangent at one. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_toRealFunRaw_compute_one
    (n : Nat) :
    coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw.compute 1 n =
      ArctanGeometry.arctanIntegralRectangleComputeAtOne n := by
  have hone : inDomainInterval
      coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper 1 := by
    change (0 : Rat) <= 1 /\ 1 <= 1
    exact ⟨by decide +kernel, Rat.le_refl⟩
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    coordinateTimesArctanIntegralRectangleOnUnit (x := 1)
      (hx := hone) n]
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg 1
    hone n]
  simp [ArctanGeometry.arctanIntegralRectangleComputeAtOne,
    ArctanGeometry.arctanIntegralRectangleCompute]

/-- The endpoint difference of the positive product branch is exactly the
rectangle evaluator for arctangent at one, before any derivative or FTC
argument. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq
    (n : Nat) :
    endpointDifferenceCompute
      coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 n =
      ArctanGeometry.arctanIntegralRectangleComputeAtOne n := by
  unfold endpointDifferenceCompute endpointDifferenceInterval
  rw [coordinateTimesArctanIntegralRectangleOnUnit_toRealFunRaw_compute_one,
    coordinateTimesArctanIntegralRectangleOnUnit_toRealFunRaw_compute_zero]
  change
    { lo := (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo - 0,
      hi := (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi - 0 } =
      ArctanGeometry.arctanIntegralRectangleComputeAtOne n
  have hlo :
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo - 0 =
        (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo := by
    grind [Rat.sub_eq_add_neg]
  have hhi :
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi - 0 =
        (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi := by
    grind [Rat.sub_eq_add_neg]
  rw [hlo, hhi]

/-- The explicitly anchored endpoint difference of the positive product
branch is a valid raw real. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1) := by
  have hcompute :
      endpointDifferenceCompute
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 =
        ArctanGeometry.arctanIntegralRectangleRawAtOne.compute := by
    funext n
    exact coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq n
  rw [hcompute]
  exact ArctanGeometry.arctanIntegralRectangleRawAtOne_valid

/-- The endpoint difference of the positive product branch is equivalent to
the geometric arctangent at one.  This packages only its boundary value, not
a product derivative or an integral identity. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_equiv_arctanGeom_one :
    (endpointDifferenceRaw
      coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
  have hEndpointValid :
      (endpointDifferenceRaw
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid
  have hEndpointRectangle :
      (endpointDifferenceRaw
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Equiv
          ArctanGeometry.arctanIntegralRectangleRawAtOne := by
    apply RealCompute.sameStageOverlap_equiv
    intro n
    apply (RealCompute.compareAt_overlap_iff
      (endpointDifferenceRaw
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid)
      ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
    change QInterval.Overlaps
      (endpointDifferenceCompute
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 n)
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n)
    rw [coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq]
    have hordered := RealCompute.interval_order_of_valid
      ArctanGeometry.arctanIntegralRectangleRawAtOne
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid n
    exact ⟨hordered, hordered⟩
  exact RealCompute.equiv_trans hEndpointValid
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel))
    hEndpointRectangle
    ArctanGeometry.arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one

/-- At the zero basepoint, the finite difference quotient of the positive
product branch is exactly the corresponding arctangent rectangle box. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_zero_differenceQuotient_compute_eq
    (h : Rat) (hpos : 0 < h)
    (hmem : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper h)
    (hzero : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper 0)
    (n : Nat) :
    QInterval.differenceQuotient
      (coordinateTimesArctanIntegralRectangleOnUnit.compute h hmem n)
      (coordinateTimesArctanIntegralRectangleOnUnit.compute 0 hzero n) h =
      ArctanGeometry.arctanIntegralRectangleCompute h n := by
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg h hmem n,
    coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg 0 hzero n]
  simp only [Rat.zero_mul]
  unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
    QInterval.scaleRat
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  rw [if_pos hinv]
  let A := ArctanGeometry.arctanIntegralRectangleCompute h n
  change
    { lo := (1 / h) * (h * A.lo - 0),
      hi := (1 / h) * (h * A.hi - 0) } = A
  have hcancel : h⁻¹ * h = 1 :=
    Rat.inv_mul_cancel h (Rat.ne_of_gt hpos)
  have hscale (q : Rat) : (1 / h) * (h * q - 0) = q := by
    have hsub : h * q - 0 = h * q := by
      grind [Rat.sub_eq_add_neg]
    rw [hsub, Rat.div_def, Rat.one_mul]
    calc
      h⁻¹ * (h * q) = (h⁻¹ * h) * q := by
        exact (Rat.mul_assoc _ _ _).symm
      _ = q := by
        rw [hcancel]
        grind
  apply (QInterval.mk.injEq _ _ _ _).mpr
  exact ⟨hscale A.lo, hscale A.hi⟩

/-- The pointwise product-rule candidate
`arctan x + x / (1 + x^2)`.  Its first summand is deliberately the same
rectangle evaluator as the primitive, so the derivative certificate below
compares finite boxes rather than postulating an exact arctangent value. -/
def coordinateTimesArctanIntegralRectangleDerivativeRaw
    (x : Rat)
    (hx : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper x) : RealCompute :=
  RealFunRaw.apply arctanIntegralRectangleOnUnit.toRealFunRaw
    (FunctionOnInterval.toRealFunRaw_valid arctanIntegralRectangleOnUnit) x hx +
    RealCompute.ofRat (x * ArctanGeometry.integralKernel x)

theorem coordinateTimesArctanIntegralRectangleDerivativeRaw_valid
    (x : Rat)
    (hx : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper x) :
    (coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).Valid := by
  apply RealCompute.add_valid
  · exact FunctionOnInterval.toRealFunRaw_valid arctanIntegralRectangleOnUnit x hx
  · exact RealCompute.ofRat_valid _

theorem coordinateTimesArctanIntegralRectangleDerivativeRaw_compute
    (x : Rat)
    (hx : inDomainInterval arctanIntegralRectangleOnUnit.lower
      arctanIntegralRectangleOnUnit.upper x) (n : Nat) :
    (coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute n =
      { lo := (arctanIntegralRectangleOnUnit.compute x hx n).lo +
          x * ArctanGeometry.integralKernel x,
        hi := (arctanIntegralRectangleOnUnit.compute x hx n).hi +
          x * ArctanGeometry.integralKernel x } := by
  unfold coordinateTimesArctanIntegralRectangleDerivativeRaw
  change RealCompute.addCompute
      (RealFunRaw.apply arctanIntegralRectangleOnUnit.toRealFunRaw
        (FunctionOnInterval.toRealFunRaw_valid arctanIntegralRectangleOnUnit) x hx)
      (RealCompute.ofRat (x * ArctanGeometry.integralKernel x)) n = _
  simp only [RealCompute.addCompute, RealFunRaw.apply, RealFunRaw.applyCompute,
    RealCompute.ofRat_compute]
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    arctanIntegralRectangleOnUnit hx]

/-- The product-rule candidate as an interval function on the rational unit
branch.  Keeping this evaluator separate from the raw pointwise expression
makes it available as the right-hand side of a two-sided derivative and,
later, an effective fundamental-theorem certificate. -/
def coordinateTimesArctanIntegralRectangleDerivativeOnUnit : FunctionOnInterval where
  raw :=
    { definedAt := fun x =>
        inDomainInterval arctanIntegralRectangleOnUnit.lower
          arctanIntegralRectangleOnUnit.upper x
      compute := fun x hx n =>
        (coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute n }
  lower := arctanIntegralRectangleOnUnit.lower
  upper := arctanIntegralRectangleOnUnit.upper
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hvalid := coordinateTimesArctanIntegralRectangleDerivativeRaw_valid x hx
    change RealCompute.ValidCompute
      (coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute
    exact hvalid

theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute
    (x : Rat)
    (hx : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x)
    (n : Nat) :
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n =
      { lo := (arctanIntegralRectangleOnUnit.compute x hx n).lo +
          x * ArctanGeometry.integralKernel x,
        hi := (arctanIntegralRectangleOnUnit.compute x hx n).hi +
          x * ArctanGeometry.integralKernel x } := by
  exact coordinateTimesArctanIntegralRectangleDerivativeRaw_compute x hx n

/-- Uniform finite range bound for the concrete product derivative on the
unit branch.  This is the first derivative-bound datum needed by the
derivative-bound FTC route: every evaluated box for
`arctan x + x / (1 + x^2)` lies in `[0,2]`. -/
theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_range
    (x : Rat)
    (hx : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x)
    (n : Nat) :
    0 <=
        (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n).lo /\
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n).hi <= 2 := by
  change 0 <= x /\ x <= 1 at hx
  have hcompute := coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute
    x ⟨hx.1, hx.2⟩ n
  change
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x
      ⟨hx.1, hx.2⟩ n =
      { lo := (arctanIntegralRectangleOnUnit.compute x hx n).lo +
          x * ArctanGeometry.integralKernel x,
        hi := (arctanIntegralRectangleOnUnit.compute x hx n).hi +
          x * ArctanGeometry.integralKernel x } at hcompute
  rw [hcompute]
  have hAlo : 0 <= (arctanIntegralRectangleOnUnit.compute x hx n).lo := by
    change 0 <= (ArctanGeometry.arctanIntegralRectangleCompute x n).lo
    exact ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative hx.1 n
  have hAhi : (arctanIntegralRectangleOnUnit.compute x hx n).hi <= x := by
    change (ArctanGeometry.arctanIntegralRectangleCompute x n).hi <= x
    exact ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input hx.1 n
  have hkernel0 : 0 <= ArctanGeometry.integralKernel x :=
    Rat.le_of_lt (ArctanGeometry.integralKernel_pos x)
  have hxkernel0 : 0 <= x * ArctanGeometry.integralKernel x :=
    Rat.mul_nonneg hx.1 hkernel0
  have hxkernel : x * ArctanGeometry.integralKernel x <= x := by
    calc
      x * ArctanGeometry.integralKernel x <= x * 1 :=
        Rat.mul_le_mul_of_nonneg_left
          (ArctanGeometry.integralKernel_le_one x) hx.1
      _ = x := by grind
  constructor
  · exact Rat.add_nonneg hAlo hxkernel0
  · calc
      (arctanIntegralRectangleOnUnit.compute x hx n).hi +
          x * ArctanGeometry.integralKernel x <= x + x :=
        rat_add_le_add hAhi hxkernel
      _ <= 1 + 1 := rat_add_le_add hx.2 hx.2
      _ = 2 := by decide +kernel

/-- The same range fact in the positive-bounded form consumed by the
interval-product and derivative-bound FTC APIs. -/
theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_nonneg_bounded
    (x : Rat)
    (hx : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x) :
    Exists fun B : Rat => 0 < B /\ forall n,
      0 <=
          (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n).lo /\
        (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n).hi <= B := by
  refine ⟨2, by decide +kernel, ?_⟩
  intro n
  exact coordinateTimesArctanIntegralRectangleDerivativeOnUnit_range x hx n

/-- The rational correction in the product derivative is nondecreasing on
the positive unit branch.  This is proved by clearing its two positive
denominators: the remaining difference is
`(y - x) * (1 - x * y)`.  Keeping that finite algebra explicit is useful for
the later monotone-cell FTC construction. -/
theorem coordinate_integralKernel_nondecreasing_on_unit
    {x y : Rat}
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hxy : x <= y) :
    x * ArctanGeometry.integralKernel x <=
      y * ArctanGeometry.integralKernel y := by
  let dx : Rat := 1 + x * x
  let dy : Rat := 1 + y * y
  have hdxpos : 0 < dx := by
    dsimp [dx]
    have hsq := RationalCircle.Stage.ratSquare_nonneg x
    grind
  have hdypos : 0 < dy := by
    dsimp [dy]
    have hsq := RationalCircle.Stage.ratSquare_nonneg y
    grind
  have hprodpos : 0 < dx * dy := Rat.mul_pos hdxpos hdypos
  have hdxne : dx ≠ 0 := Rat.ne_of_gt hdxpos
  have hdyne : dy ≠ 0 := Rat.ne_of_gt hdypos
  have hxyprod : x * y <= 1 := by
    calc
      x * y <= 1 * y := Rat.mul_le_mul_of_nonneg_right hx1 hy0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hy1 (by decide +kernel)
      _ = 1 := by decide +kernel
  have hfactor : 0 <= (y - x) * (1 - x * y) := by
    apply Rat.mul_nonneg
    · grind
    · have hproductNonneg : 0 <= x * y := Rat.mul_nonneg hx0 hy0
      grind [Rat.sub_eq_add_neg]
  have hcross : x * dy <= y * dx := by
    calc
      x * dy = y * dx - ((y - x) * (1 - x * y)) := by
        dsimp [dx, dy]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
          Rat.mul_comm]
      _ <= y * dx := by grind [Rat.sub_eq_add_neg]
  apply Rat.le_of_mul_le_mul_right (c := dx * dy)
  · unfold ArctanGeometry.integralKernel
    rw [Rat.div_def, Rat.div_def]
    have hcancelx : dx⁻¹ * dx = 1 := Rat.inv_mul_cancel dx hdxne
    have hcancely : dy⁻¹ * dy = 1 := Rat.inv_mul_cancel dy hdyne
    calc
      (x * (1 * dx⁻¹)) * (dx * dy) = x * dy := by
        calc
          (x * (1 * dx⁻¹)) * (dx * dy) =
              (x * dy) * (dx⁻¹ * dx) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
          _ = x * dy := by rw [hcancelx, Rat.mul_one]
      _ <= y * dx := hcross
      _ = (y * (1 * dy⁻¹)) * (dx * dy) := by
        symm
        calc
          (y * (1 * dy⁻¹)) * (dx * dy) =
              (y * dx) * (dy⁻¹ * dy) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
          _ = y * dx := by rw [hcancely, Rat.mul_one]
  · exact hprodpos

/-- The rational correction `x / (1 + x^2)` in the product derivative is
three-Lipschitz on the unit interval.  The deliberately slack constant comes
from the already certified two-Lipschitz reciprocal kernel plus one factor
for moving the coordinate.  It is a finite rational estimate used to give
the product derivative its own continuity modulus. -/
theorem coordinate_integralKernel_lipschitz_on_unit :
    Integral.LipschitzOnUnit
      (fun x : Rat => x * ArctanGeometry.integralKernel x) 3 := by
  constructor
  · decide +kernel
  · intro s t hs0 hs1 ht0 ht1
    have hkernel := oneOverOnePlusSquare_lipschitz_on_unit.2
      s t hs0 hs1 ht0 ht1
    have hkernel' :
        qabs (ArctanGeometry.integralKernel s -
          ArctanGeometry.integralKernel t) <= 2 * qabs (t - s) := by
      simpa [ArctanGeometry.integralKernel] using hkernel
    have hkernelT0 : 0 <= ArctanGeometry.integralKernel t :=
      Rat.le_of_lt (ArctanGeometry.integralKernel_pos t)
    have hkernelT1 : ArctanGeometry.integralKernel t <= 1 :=
      ArctanGeometry.integralKernel_le_one t
    have hfirst :
        qabs (s * (ArctanGeometry.integralKernel s -
          ArctanGeometry.integralKernel t)) <= 2 * qabs (t - s) := by
      rw [qabs_mul, qabs_eq_self_of_nonneg hs0]
      calc
        s * qabs (ArctanGeometry.integralKernel s -
            ArctanGeometry.integralKernel t) <=
            s * (2 * qabs (t - s)) :=
          Rat.mul_le_mul_of_nonneg_left hkernel' hs0
        _ <= 1 * (2 * qabs (t - s)) :=
          Rat.mul_le_mul_of_nonneg_right hs1 (by
            exact Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
        _ = 2 * qabs (t - s) := by grind
    have hsecond :
        qabs ((s - t) * ArctanGeometry.integralKernel t) <= qabs (t - s) := by
      rw [qabs_mul, qabs_eq_self_of_nonneg hkernelT0]
      have hdist : qabs (s - t) = qabs (t - s) := by
        have hneg : s - t = -(t - s) := by grind [Rat.sub_eq_add_neg]
        rw [hneg, qabs_neg]
      rw [hdist]
      calc
        qabs (t - s) * ArctanGeometry.integralKernel t <=
            qabs (t - s) * 1 :=
          Rat.mul_le_mul_of_nonneg_left hkernelT1 (qabs_nonneg _)
        _ = qabs (t - s) := by grind
    have hsplit :
        s * ArctanGeometry.integralKernel s -
            t * ArctanGeometry.integralKernel t =
          s * (ArctanGeometry.integralKernel s -
            ArctanGeometry.integralKernel t) +
          (s - t) * ArctanGeometry.integralKernel t := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hsplit]
    calc
      qabs (s * (ArctanGeometry.integralKernel s -
          ArctanGeometry.integralKernel t) +
          (s - t) * ArctanGeometry.integralKernel t) <=
          qabs (s * (ArctanGeometry.integralKernel s -
            ArctanGeometry.integralKernel t)) +
            qabs ((s - t) * ArctanGeometry.integralKernel t) :=
        qabs_add_le _ _
      _ <= 2 * qabs (t - s) + qabs (t - s) :=
        rat_add_le_add hfirst hsecond
      _ = 3 * qabs (t - s) := by grind

/-- The two-sided product derivative is itself nondecreasing on `[0,1]`.
The rectangle arctangent summand is monotone by geometric inclusion, while
the rational correction is monotone by the denominator-clearing calculation
above.  This is an endpoint-range input for the derivative-bound FTC route;
it does not by itself establish the required endpoint secant containment. -/
theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_nondecreasing :
    NondecreasingOnInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit := by
  intro x y hx hy hxy n
  change 0 <= x /\ x <= 1 at hx
  change 0 <= y /\ y <= 1 at hy
  have hcomputex := coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute
    x ⟨hx.1, hx.2⟩ n
  have hcomputey := coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute
    y ⟨hy.1, hy.2⟩ n
  change
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x
      ⟨hx.1, hx.2⟩ n = _ at hcomputex
  change
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute y
      ⟨hy.1, hy.2⟩ n = _ at hcomputey
  rw [hcomputex, hcomputey]
  exact rat_add_le_add
    (ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
      hx.1 hxy n)
    (coordinate_integralKernel_nondecreasing_on_unit
      hx.1 hx.2 hy.1 hy.2 hxy)

/-- Packaged weak monotonicity of the derivative candidate for use by
piecewise-monotone and derivative-bound constructions. -/
def coordinateTimesArctanIntegralRectangleDerivativeOnUnit_monotone :
    MonotoneOnInterval coordinateTimesArctanIntegralRectangleDerivativeOnUnit :=
  MonotoneOnInterval.ofNondecreasing
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit_nondecreasing

/-- A fixed-tolerance, explicit-stage continuity estimate for the derivative
candidate `arctan x + x / (1 + x^2)`.  Input distance at most `eps/6` gives
`eps`-near derivative boxes at the stated rectangle stage.  Exposing this
schedule is what later lets a uniform FTC partition remain executable. -/
theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_near_of_qabs_le
    (eps : QPos) {x y : Rat}
    (hx : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x)
    (hy : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper y)
    (hclose : qabs (y - x) <= eps.val / 6) :
    QInterval.NearAt
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx
        (4 * ((eps.val / 2).den + 1)))
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute y hy
        (4 * ((eps.val / 2).den + 1))) eps := by
  let eta : QPos :=
    { val := eps.val / 2
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel)) }
  let rho : QPos :=
    { val := eps.val / 6
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel)) }
  let n : Nat := 4 * (eta.val.den + 1)
  have hrho_le_eta : rho.val <= eta.val := by
    dsimp [rho, eta]
    rw [Rat.div_def, Rat.div_def]
    apply Rat.mul_le_mul_of_nonneg_left
    · decide +kernel
    · exact Rat.le_of_lt eps.property
  have hAnear := arctanIntegralRectangleOnUnit_near_of_qabs_le eta n
    (by dsimp [n]; omega) hx hy (Rat.le_trans (by simpa [rho] using hclose) hrho_le_eta)
  rcases hAnear with ⟨hAxy, hAyx, hAwidthX, hAwidthY⟩
  have hcorrection := coordinate_integralKernel_lipschitz_on_unit.2
    x y hx.1 hx.2 hy.1 hy.2
  have hinputRho : qabs (y - x) <= rho.val := by
    simpa [rho] using hclose
  have hthreeRho : (3 : Rat) * rho.val = eta.val := by
    dsimp [rho, eta]
    rw [Rat.div_def, Rat.div_def]
    have hsix : (6 : Rat) * (6 : Rat)⁻¹ = 1 := by decide +kernel
    have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hcorrectionNear :
      qabs (x * ArctanGeometry.integralKernel x -
        y * ArctanGeometry.integralKernel y) <= eta.val := by
    calc
      qabs (x * ArctanGeometry.integralKernel x -
          y * ArctanGeometry.integralKernel y) <=
          3 * qabs (y - x) := hcorrection
      _ <= 3 * rho.val :=
        Rat.mul_le_mul_of_nonneg_left hinputRho (by decide +kernel)
      _ = eta.val := hthreeRho
  have hcorrectionXY :
      x * ArctanGeometry.integralKernel x <=
        y * ArctanGeometry.integralKernel y + eta.val := by
    have h := Rat.le_trans
      (self_le_qabs (x * ArctanGeometry.integralKernel x -
        y * ArctanGeometry.integralKernel y)) hcorrectionNear
    grind [Rat.sub_eq_add_neg]
  have hcorrectionYX :
      y * ArctanGeometry.integralKernel y <=
        x * ArctanGeometry.integralKernel x + eta.val := by
    have hrev :
        qabs (y * ArctanGeometry.integralKernel y -
          x * ArctanGeometry.integralKernel x) <= eta.val := by
      rw [show y * ArctanGeometry.integralKernel y -
          x * ArctanGeometry.integralKernel x =
          -(x * ArctanGeometry.integralKernel x -
            y * ArctanGeometry.integralKernel y) by
          grind [Rat.sub_eq_add_neg], qabs_neg]
      exact hcorrectionNear
    have h := Rat.le_trans
      (self_le_qabs (y * ArctanGeometry.integralKernel y -
        x * ArctanGeometry.integralKernel x)) hrev
    grind [Rat.sub_eq_add_neg]
  have heta_le_eps : eta.val <= eps.val := by
    dsimp [eta]
    rw [Rat.div_def]
    calc
      eps.val * (2 : Rat)⁻¹ <= eps.val * 1 :=
        Rat.mul_le_mul_of_nonneg_left (by decide +kernel)
          (Rat.le_of_lt eps.property)
      _ = eps.val := by grind
  change QInterval.NearAt
    (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx n)
    (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute y hy n) eps
  rw [coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute,
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute]
  unfold QInterval.NearAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (arctanIntegralRectangleOnUnit.compute x hx n).lo +
          x * ArctanGeometry.integralKernel x <=
          ((arctanIntegralRectangleOnUnit.compute y hy n).hi + eta.val) +
            (y * ArctanGeometry.integralKernel y + eta.val) :=
        rat_add_le_add hAxy hcorrectionXY
      _ = (arctanIntegralRectangleOnUnit.compute y hy n).hi +
          y * ArctanGeometry.integralKernel y + eps.val := by
        dsimp [eta]
        rw [Rat.div_def]
        have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
        grind [Rat.add_assoc, Rat.add_comm, Rat.mul_assoc]
  · calc
      (arctanIntegralRectangleOnUnit.compute y hy n).lo +
          y * ArctanGeometry.integralKernel y <=
          ((arctanIntegralRectangleOnUnit.compute x hx n).hi + eta.val) +
            (x * ArctanGeometry.integralKernel x + eta.val) :=
        rat_add_le_add hAyx hcorrectionYX
      _ = (arctanIntegralRectangleOnUnit.compute x hx n).hi +
          x * ArctanGeometry.integralKernel x + eps.val := by
        dsimp [eta]
        rw [Rat.div_def]
        have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
        grind [Rat.add_assoc, Rat.add_comm, Rat.mul_assoc]
  · unfold QInterval.width
    have :
        (arctanIntegralRectangleOnUnit.compute x hx n).hi -
            (arctanIntegralRectangleOnUnit.compute x hx n).lo <= eps.val :=
      Rat.le_trans hAwidthX heta_le_eps
    grind [Rat.sub_eq_add_neg]
  · unfold QInterval.width
    have :
        (arctanIntegralRectangleOnUnit.compute y hy n).hi -
            (arctanIntegralRectangleOnUnit.compute y hy n).lo <= eps.val :=
      Rat.le_trans hAwidthY heta_le_eps
    grind [Rat.sub_eq_add_neg]

/-- The concrete derivative candidate `arctan x + x / (1 + x^2)` has literal
rational epsilon--delta continuity on the unit branch.  Its executable
schedule is the fixed-stage theorem above: the radius is `eps/6` and the
rectangle stage is determined by the denominator of `eps/2`. -/
theorem coordinateTimesArctanIntegralRectangleDerivativeOnUnit_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit := by
  intro eps
  let rho : QPos :=
    { val := eps.val / 6
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel)) }
  let n : Nat := 4 * ((eps.val / 2).den + 1)
  refine ⟨rho, n, ?_⟩
  intro x y hx hy hclose
  simpa [n] using
    (coordinateTimesArctanIntegralRectangleDerivativeOnUnit_near_of_qabs_le
      eps hx hy (by simpa [rho] using hclose))

/-- The elementary denominator schedule used to turn the fixed-tolerance
derivative estimate into an `EffectiveModulusFor`. -/
private theorem one_div_six_mul_succ_le_precision_div_six (n : Nat) :
    1 / (((6 * (n + 1) : Nat) : Rat)) <= (precisionAtStage n).val / 6 := by
  cases n with
  | zero => decide +kernel
  | succ n =>
      have hreciprocal :
          1 / (((6 * (n + 2) : Nat) : Rat)) <=
            1 / (((6 * (n + 1) : Nat) : Rat)) :=
        FTC.one_div_nat_antitone (by omega) (by omega) (by omega)
      calc
        1 / (((6 * (Nat.succ n + 1) : Nat) : Rat)) =
            1 / (((6 * (n + 2) : Nat) : Rat)) := by congr 3 <;> omega
        _ <= 1 / (((6 * (n + 1) : Nat) : Rat)) := hreciprocal
        _ = (precisionAtStage (Nat.succ n)).val / 6 := by
          rw [precisionAtStage, dif_neg (Nat.succ_ne_zero n), Rat.natCast_mul]
          change 1 / (6 * ((n + 1 : Nat) : Rat)) =
            (1 / ((n + 1 : Nat) : Rat)) / 6
          rw [Rat.div_def, Rat.inv_mul_rev]
          grind [Rat.mul_comm]

/-- A computable modulus for the derivative of the unit-branch product
`x * arctan x`.  The stage and radius are explicit finite rational functions
of the requested output stage, so the later FTC partition can be computed
without extracting a witness from an existential continuity statement. -/
def coordinateTimesArctanIntegralRectangleDerivativeOnUnit_effectiveModulus :
    EffectiveModulusFor
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit where
  inputPrecision := fun n => 6 * (n + 1)
  evalPrecision := fun n =>
    4 * (((precisionAtStage n).val / 2).den + 1)
  close := by
    intro x y n hx hy hclose
    let eps : QPos := precisionAtStage n
    have hinput : qabs (y - x) <= eps.val / 6 := by
      exact Rat.le_trans hclose (by simpa [eps] using
        one_div_six_mul_succ_le_precision_div_six n)
    have hnear := coordinateTimesArctanIntegralRectangleDerivativeOnUnit_near_of_qabs_le
      eps hx hy hinput
    change intervalNearAtPrecision
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx
        (4 * (((precisionAtStage n).val / 2).den + 1)))
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute y hy
        (4 * (((precisionAtStage n).val / 2).den + 1))) n at hnear
    simpa [eps] using hnear

/-- The literal rational radius selected for the product derivative at a
requested forward-derivative stage.  This is deliberately a definition, so a
uniform partition can use it without extracting an existential witness from
continuity. -/
def coordinateTimesArctanForwardContinuityRadius (n : Nat) : QPos :=
  { val := (precisionAtStage n).val / 6
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos (precisionAtStage n).property
        ((Rat.inv_pos).2 (by decide +kernel)) }

/-- The matching common derivative-evaluation stage for
`coordinateTimesArctanForwardContinuityRadius`. -/
def coordinateTimesArctanForwardContinuityStage (n : Nat) : Nat :=
  4 * (((precisionAtStage n).val / 2).den + 1)

/-- The positive-step quotient of the literal interval product has an exact
endpoint decomposition.  The terms use the arctangent quotient at the same
evaluation stage; the swapped endpoint of the base arctangent box is exactly
what makes the formula valid for interval enclosures. -/
private theorem coordinateTimesArctan_forwardQuotient_decompose
    (x h : Rat) (A B : QInterval) (hpos : 0 < h) :
    QInterval.differenceQuotient
      { lo := (x + h) * B.lo, hi := (x + h) * B.hi }
      { lo := x * A.lo, hi := x * A.hi } h =
      { lo := A.hi + (x + h) *
          (QInterval.differenceQuotient B A h).lo,
        hi := A.lo + (x + h) *
          (QInterval.differenceQuotient B A h).hi } := by
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hne : h ≠ 0 := Rat.ne_of_gt hpos
  unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
    QInterval.scaleRat
  rw [if_pos hinv, if_pos hinv]
  apply (QInterval.mk.injEq _ _ _ _).mpr
  constructor <;>
    rw [Rat.div_def]
  · have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hne
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  · have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hne
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]

/-- Finite enclosure form of the product rule.  The arctangent quotient is
already within its kernel at a finer stage; the exact quotient decomposition
above spends the remaining budget on the two bounded product terms. -/
private theorem coordinateTimesArctan_forwardQuotient_near
    {x h K : Rat} {A B : QInterval} {m n : Nat}
    (hpos : 0 < h) (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy1 : x + h <= 1)
    (hAordered : 0 <= A.width) (hBordered : 0 <= B.width)
    (hAwidth : A.width <= h * (precisionAtStage m).val / 16)
    (hstage : (precisionAtStage m).val <= (precisionAtStage n).val / 8)
    (hstep : 2 * h <= (precisionAtStage n).val / 4)
    (hprecision : (precisionAtStage n).val <= 1)
    (hKnonneg : 0 <= K) (hKle : K <= 1)
    (hnear : intervalNearAtPrecision
      (QInterval.differenceQuotient B A h) { lo := K, hi := K } m) :
    intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := (x + h) * B.lo, hi := (x + h) * B.hi }
        { lo := x * A.lo, hi := x * A.hi } h)
      { lo := A.lo + x * K, hi := A.hi + x * K } n := by
  let Q : QInterval := QInterval.differenceQuotient B A h
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hy0 : 0 <= x + h := by grind
  have hpm0 : 0 <= (precisionAtStage m).val :=
    Rat.le_of_lt (precisionAtStage m).property
  have hen : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  have hpmLeOne : (precisionAtStage m).val <= 1 := by
    calc
      (precisionAtStage m).val <= (precisionAtStage n).val / 8 := hstage
      _ <= (1 : Rat) / 8 := by
        exact Rat.mul_le_mul_of_nonneg_right hprecision (by decide +kernel)
      _ <= 1 := by decide +kernel
  have hqordered : 0 <= Q.width := by
    dsimp [Q]
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat QInterval.width
    rw [if_pos hinv]
    dsimp
    have hdiff : 0 <= (B.hi - A.lo) - (B.lo - A.hi) := by
      unfold QInterval.width at hAordered hBordered
      grind [Rat.sub_eq_add_neg]
    calc
      0 <= (1 / h) * ((B.hi - A.lo) - (B.lo - A.hi)) :=
        Rat.mul_nonneg hinv hdiff
      _ = (1 / h) * (B.hi - A.lo) - (1 / h) * (B.lo - A.hi) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  have hquotientFormula := coordinateTimesArctan_forwardQuotient_decompose x h A B hpos
  rw [hquotientFormula]
  change intervalNearAtPrecision
    { lo := A.hi + (x + h) * Q.lo,
      hi := A.lo + (x + h) * Q.hi }
    { lo := A.lo + x * K, hi := A.hi + x * K } n
  have hnearQ : intervalNearAtPrecision Q { lo := K, hi := K } m := by
    simpa [Q] using hnear
  unfold intervalNearAtPrecision QInterval.NearAt at hnearQ ⊢
  rcases hnearQ with ⟨hQlo, hQhi, hQwidth, _⟩
  have hQloLeTwo : Q.lo <= 2 := by
    calc
      Q.lo <= K + (precisionAtStage m).val := hQlo
      _ <= 1 + 1 := rat_add_le_add hKle hpmLeOne
      _ = 2 := by decide +kernel
  have hQhiGeNegOne : -1 <= Q.hi := by
    have hnegPm : -(precisionAtStage m).val <= Q.hi := by
      have hzero : 0 <= Q.hi + (precisionAtStage m).val :=
        Rat.le_trans hKnonneg hQhi
      grind [Rat.sub_eq_add_neg]
    calc
      -1 <= -(precisionAtStage m).val := by grind
      _ <= Q.hi := hnegPm
  have hxm : x * (precisionAtStage m).val <= (precisionAtStage m).val := by
    calc
      x * (precisionAtStage m).val <= 1 * (precisionAtStage m).val :=
        Rat.mul_le_mul_of_nonneg_right hx1 hpm0
      _ = (precisionAtStage m).val := by grind
  have herrorLarge : (precisionAtStage m).val + 2 * h <=
      (precisionAtStage n).val := by
    calc
      (precisionAtStage m).val + 2 * h <=
          (precisionAtStage n).val / 8 + (precisionAtStage n).val / 4 :=
        rat_add_le_add hstage hstep
      _ <= (precisionAtStage n).val := by
        rw [Rat.div_def]
        grind
  have herrorSmall : (precisionAtStage m).val + h <=
      (precisionAtStage n).val := by
    calc
      (precisionAtStage m).val + h <=
          (precisionAtStage m).val + 2 * h :=
        (Rat.add_le_add_left).2 (by grind)
      _ <= (precisionAtStage n).val := herrorLarge
  have hleft : (x + h) * Q.lo <= x * K + (precisionAtStage n).val := by
    calc
      (x + h) * Q.lo = x * Q.lo + h * Q.lo := by
        grind [Rat.add_mul]
      _ <= x * (K + (precisionAtStage m).val) + h * 2 :=
        rat_add_le_add
          (Rat.mul_le_mul_of_nonneg_left hQlo hx0)
          (Rat.mul_le_mul_of_nonneg_left hQloLeTwo (Rat.le_of_lt hpos))
      _ = x * K + x * (precisionAtStage m).val + 2 * h := by
        grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
      _ <= x * K + ((precisionAtStage m).val + 2 * h) := by
        calc
          x * K + x * (precisionAtStage m).val + 2 * h =
              x * K + (x * (precisionAtStage m).val + 2 * h) := by
                grind [Rat.add_assoc]
          _ <= x * K + ((precisionAtStage m).val + 2 * h) :=
            (Rat.add_le_add_left).2 ((Rat.add_le_add_right).2 hxm)
      _ <= x * K + (precisionAtStage n).val :=
        (Rat.add_le_add_left).2 herrorLarge
  have hrightBase : x * Q.hi <= (x + h) * Q.hi + h := by
    have hnonneg : 0 <= h * (Q.hi + 1) :=
      Rat.mul_nonneg (Rat.le_of_lt hpos) (by grind [Rat.sub_eq_add_neg])
    calc
      x * Q.hi <= x * Q.hi + h * Q.hi + h := by
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]
      _ = (x + h) * Q.hi + h := by
        grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hright : x * K <= (x + h) * Q.hi + (precisionAtStage n).val := by
    calc
      x * K <= x * (Q.hi + (precisionAtStage m).val) :=
        Rat.mul_le_mul_of_nonneg_left hQhi hx0
      _ = x * Q.hi + x * (precisionAtStage m).val := by
        grind [Rat.mul_add]
      _ <= ((x + h) * Q.hi + h) + (precisionAtStage m).val :=
        rat_add_le_add hrightBase hxm
      _ = (x + h) * Q.hi + ((precisionAtStage m).val + h) := by
        grind [Rat.add_assoc, Rat.add_comm]
      _ <= (x + h) * Q.hi + (precisionAtStage n).val :=
        (Rat.add_le_add_left).2 herrorSmall
  have hleftWidth :
      ({ lo := A.hi + (x + h) * Q.lo,
         hi := A.lo + (x + h) * Q.hi } : QInterval).width <=
        (precisionAtStage n).val := by
    unfold QInterval.width
    calc
      A.lo + (x + h) * Q.hi - (A.hi + (x + h) * Q.lo) =
          (x + h) * Q.width - A.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_add,
          Rat.add_mul]
      _ <= (x + h) * Q.width := by grind
      _ <= 1 * Q.width :=
        Rat.mul_le_mul_of_nonneg_right hy1 hqordered
      _ = Q.width := by grind
      _ <= (precisionAtStage m).val := hQwidth
      _ <= (precisionAtStage n).val :=
        Rat.le_trans hstage (by
          rw [Rat.div_def]
          have : (0 : Rat) <= 1 / 8 := by decide +kernel
          grind)
  have htargetWidth :
      ({ lo := A.lo + x * K, hi := A.hi + x * K } : QInterval).width <=
        (precisionAtStage n).val := by
    unfold QInterval.width
    have hhLeOne : h <= 1 := by
      calc
        h <= 2 * h := by grind
        _ <= (precisionAtStage n).val / 4 := hstep
        _ <= (1 : Rat) / 4 :=
          Rat.mul_le_mul_of_nonneg_right hprecision (by decide +kernel)
        _ <= 1 := by decide +kernel
    calc
      A.hi + x * K - (A.lo + x * K) = A.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg]
      _ <= h * (precisionAtStage m).val / 16 := hAwidth
      _ <= (precisionAtStage m).val := by
        have hscale := Rat.mul_le_mul_of_nonneg_right hhLeOne hpm0
        calc
          h * (precisionAtStage m).val / 16 <=
              (1 : Rat) * (precisionAtStage m).val / 16 := by
                exact Rat.mul_le_mul_of_nonneg_right hscale (by decide +kernel)
          _ <= (precisionAtStage m).val := by
            rw [Rat.div_def]
            have : (0 : Rat) <= (1 : Rat) / 16 := by decide +kernel
            grind
      _ <= (precisionAtStage n).val :=
        Rat.le_trans hstage (by
          rw [Rat.div_def]
          have : (0 : Rat) <= (1 : Rat) / 8 := by decide +kernel
          grind)
  exact ⟨by
      calc
        A.hi + (x + h) * Q.lo <=
            A.hi + (x * K + (precisionAtStage n).val) :=
          (Rat.add_le_add_left).2 hleft
        _ = (A.hi + x * K) + (precisionAtStage n).val := by
          grind [Rat.add_assoc],
    by
      calc
        A.lo + x * K <= A.lo + ((x + h) * Q.hi + (precisionAtStage n).val) :=
          (Rat.add_le_add_left).2 hright
        _ = (A.lo + (x + h) * Q.hi) + (precisionAtStage n).val := by
          grind [Rat.add_assoc],
    hleftWidth, htargetWidth⟩

private theorem precisionAtStage_le_one (n : Nat) :
    (precisionAtStage n).val <= 1 := by
  by_cases hn : n = 0
  · subst n
    decide +kernel
  · simp only [precisionAtStage, dif_neg hn]
    have hpos : 1 <= n := Nat.pos_of_ne_zero hn
    calc
      1 / (n : Rat) <= 1 / ((1 : Nat) : Rat) :=
        FTC.one_div_nat_antitone (Nat.succ_pos 0)
          (Nat.pos_of_ne_zero hn) hpos
      _ = 1 := by decide +kernel

/-- The positive product evaluator has the forward product derivative
\(\arctan(x)+x/(1+x^2)\) at every rational point of the unit branch.
This is a genuine interval certificate: it derives the product quotient from
the rectangle arctangent quotient at a finer step-aware evaluation stage. -/
def coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    HasForwardDerivativeAt coordinateTimesArctanIntegralRectangleOnUnit x
      (coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩) := by
  refine
    { x_mem := ⟨hx0, hx1⟩
      derivative_valid :=
        coordinateTimesArctanIntegralRectangleDerivativeRaw_valid x ⟨hx0, hx1⟩
      stepPrecision := fun n => 72 * (n + 1)
      evalPrecision := fun h n =>
        arctanRectangleTangentTransportPrecision h (8 * (n + 1))
      close := ?_ }
  intro h n hmem hpos hsmall
  change 0 <= x + h /\ x + h <= 1 at hmem
  have hforwardSmall := twoSided_step_implies_forward n hsmall
  have hforward :=
    (arctanIntegralRectangleOnUnit_forwardDerivativeAt x hx0 hx1).close
      h (8 * (n + 1)) hmem hpos hforwardSmall
  have hnear : intervalNearAtPrecision
      (QInterval.differenceQuotient
        (arctanIntegralRectangleOnUnit.compute (x + h) hmem
          (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
        (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩
          (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) h)
      { lo := ArctanGeometry.integralKernel x,
        hi := ArctanGeometry.integralKernel x }
      (8 * (n + 1)) := by
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        (arctanIntegralRectangleOnUnit.compute (x + h) hmem
          (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
        (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩
          (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) h)
      { lo := ArctanGeometry.integralKernel x,
        hi := ArctanGeometry.integralKernel x } (8 * (n + 1)) at hforward
    exact hforward
  have hAwidth :
      (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width <=
        h * (precisionAtStage (8 * (n + 1))).val / 16 := by
    let eps : QPos :=
      { val := h * (precisionAtStage (8 * (n + 1))).val / 16
        property := by
          rw [Rat.div_def]
          apply Rat.mul_pos
          · exact Rat.mul_pos hpos (precisionAtStage (8 * (n + 1))).property
          · exact (Rat.inv_pos).2 (by decide +kernel) }
    let N : Nat := 256 * (eps.val.den + 1)
    have hN : arctanRectangleTangentTransportPrecision h (8 * (n + 1)) = N := by
      simp only [arctanRectangleTangentTransportPrecision, dif_pos hpos]
      rfl
    have hNrect : 4 * (eps.val.den + 1) <= N := by
      dsimp [N]
      omega
    rw [hN]
    change (ArctanGeometry.arctanIntegralRectangleCompute x N).width <= _
    exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      hx0 hx1 eps N hNrect
  have hAordered : 0 <=
      (arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width := by
    change 0 <=
      (ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width
    exact ArctanGeometry.arctanIntegralRectangleCompute_ordered hx0 _
  have hBordered : 0 <=
      (arctanIntegralRectangleOnUnit.compute (x + h) hmem
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width := by
    change 0 <=
      (ArctanGeometry.arctanIntegralRectangleCompute (x + h)
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width
    exact ArctanGeometry.arctanIntegralRectangleCompute_ordered hmem.1 _
  have hcore := coordinateTimesArctan_forwardQuotient_near
    (x := x) (h := h) (K := ArctanGeometry.integralKernel x)
    (A := arctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩
      (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
    (B := arctanIntegralRectangleOnUnit.compute (x + h) hmem
      (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
    (m := 8 * (n + 1)) (n := n)
    hpos hx0 hx1 hmem.2 hAordered hBordered hAwidth
    (twoSided_precision_stage_le_eighth n)
    (twoSided_step_le_quarterPrecision n hsmall)
    (precisionAtStage_le_one n)
    (Rat.le_of_lt (ArctanGeometry.integralKernel_pos x))
    (ArctanGeometry.integralKernel_le_one x) hnear
  rw [coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg
    (x + h) hmem,
    coordinateTimesArctanIntegralRectangleOnUnit_compute_of_nonneg x ⟨hx0, hx1⟩]
  rw [coordinateTimesArctanIntegralRectangleDerivativeRaw_compute x
    (by exact ⟨hx0, hx1⟩)
    (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))]
  exact hcore

/-- The finite forward derivative certificate for `x * arctan(x)` also gives
the local endpoint enclosure required by the derivative-bound FTC interface.
For a positive cell of admissible width, its endpoint difference is contained
in the cell width times the left-endpoint derivative box widened by twice the
requested precision.  This is a secant enclosure, not yet a global FTC: a
separate cell-range argument will make one common derivative bound cover all
points of the cell. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_enclosure
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat)
    (hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    QInterval.ContainsInterval
      (QInterval.scaleByRat h
        (QInterval.expand
          (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x
            ⟨hx0, hx1⟩
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
          (2 * (precisionAtStage n).val)))
      (endpointDifferenceInterval
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw x (x + h)
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) := by
  have hmem : inDomainInterval
      coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper (x + h) := by
    change 0 <= x + h /\ x + h <= 1
    exact ⟨by grind, hupper⟩
  let N : Nat := arctanRectangleTangentTransportPrecision h (8 * (n + 1))
  have hnearRaw :=
    (coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt x hx0 hx1).close
      h n hmem hpos hsmall
  have hnear : intervalNearAtPrecision
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h) hmem N)
        (coordinateTimesArctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩ N) h)
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute N)
      n := by
    simpa only [coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt,
      N] using hnearRaw
  have hsecant :=
    QInterval.scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
      hpos hnear
  change QInterval.ContainsInterval
      (QInterval.scaleByRat h
        (QInterval.expand
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute N)
          (2 * (precisionAtStage n).val)))
      (endpointDifferenceInterval
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw x (x + h) N)
  unfold endpointDifferenceInterval
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
        coordinateTimesArctanIntegralRectangleOnUnit hmem,
    FunctionOnInterval.toRealFunRaw_compute_of_mem
      coordinateTimesArctanIntegralRectangleOnUnit ⟨hx0, hx1⟩]
  exact hsecant

/-- A local common box can combine the step-aware secant evaluator for the
arctangent product with a possibly different continuity-evaluation stage of
its derivative.  The caller supplies the finite continuity comparison between
the left endpoint and a candidate point in the same short cell.  The
resulting box contains both that candidate derivative value and the primitive
endpoint difference after multiplication by the positive cell width; its
width costs at most ten requested tolerances. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_forward_common_secant_value_enclosure
    {x h t : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1)
    (ht : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t)
    (n m : Nat)
    (hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat)))
    (hvalue :
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute m).NearAt
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
        (precisionAtStage n)) :
    let N := arctanRectangleTangentTransportPrecision h (8 * (n + 1))
    let bound :=
      QInterval.hull
        (QInterval.expand
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
            ⟨hx0, hx1⟩).compute N)
          (2 * (precisionAtStage n).val))
        (QInterval.expand
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
            ⟨hx0, hx1⟩).compute m)
          (2 * (precisionAtStage n).val))
    bound.ContainsInterval
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
      (QInterval.scaleByRat h bound).ContainsInterval
        (QInterval.subInterval
          (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h)
            (by
              change 0 <= x + h /\ x + h <= 1
              exact ⟨by grind, hupper⟩) N)
          (coordinateTimesArctanIntegralRectangleOnUnit.compute x
            ⟨hx0, hx1⟩ N)) /\
        bound.width <= 10 * (precisionAtStage n).val := by
  let N : Nat := arctanRectangleTangentTransportPrecision h (8 * (n + 1))
  let Dleft : RealCompute :=
    coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩
  let Dvalue : RealCompute :=
    coordinateTimesArctanIntegralRectangleDerivativeRaw t ht
  have hmem : inDomainInterval
      coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper (x + h) := by
    change 0 <= x + h /\ x + h <= 1
    exact ⟨by grind, hupper⟩
  have hnearRaw :=
    (coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt x hx0 hx1).close
      h n hmem hpos hsmall
  have hnear :
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h) hmem N)
        (coordinateTimesArctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩ N) h).NearAt
      (Dleft.compute N) (precisionAtStage n) := by
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h) hmem N)
        (coordinateTimesArctanIntegralRectangleOnUnit.compute x ⟨hx0, hx1⟩ N) h)
      (Dleft.compute N) (precisionAtStage n) at hnearRaw
    simpa only [coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt,
      N, Dleft] using hnearRaw
  have hvalue' : (Dleft.compute m).NearAt (Dvalue.compute m)
      (precisionAtStage n) := by
    simpa only [Dleft, Dvalue] using hvalue
  have hDleftValid : Dleft.Valid := by
    dsimp [Dleft]
    exact coordinateTimesArctanIntegralRectangleDerivativeRaw_valid x ⟨hx0, hx1⟩
  have hover : (Dleft.compute N).Overlaps (Dleft.compute m) :=
    (RealCompute.compareAt_overlap_iff Dleft Dleft N m).mp
      (RealCompute.allStagesOverlap_refl Dleft hDleftValid N m)
  have hcommon :=
    QInterval.common_secant_derivative_bound_of_near hpos hnear hvalue' hover
      (hDleftValid.1 N) (hDleftValid.1 m)
  simpa only [N, Dleft, Dvalue] using hcommon

/-- The concrete common box used by a forward unit-branch cell of
`x * arctan x`.  It combines the step-aware endpoint stage with the explicit
continuity stage of the derivative. -/
def coordinateTimesArctanForwardSecantBound
    (x h : Rat)
    (hx : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x)
    (n : Nat) : QInterval :=
  QInterval.hull
    (QInterval.expand
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute
        (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
      (2 * (precisionAtStage n).val))
    (QInterval.expand
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute
        (coordinateTimesArctanForwardContinuityStage n))
      (2 * (precisionAtStage n).val))

/-- The preceding common secant box has a fully explicit continuity radius
and derivative stage.  This is the non-existential local theorem used by a
computable uniform-cell constructor. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_explicit_uniform_range_enclosure
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat)
    (hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    (forall t
      (ht : inDomainInterval
        coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
        coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t),
      qabs (t - x) <= (coordinateTimesArctanForwardContinuityRadius n).val ->
        (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n).ContainsInterval
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute
            (coordinateTimesArctanForwardContinuityStage n))) /\
      (QInterval.scaleByRat h
        (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n)).ContainsInterval
        (endpointDifferenceInterval
          coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
          x (x + h)
          (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) /\
        (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n).width <=
          10 * (precisionAtStage n).val := by
  let eps : QPos := precisionAtStage n
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let m : Nat := coordinateTimesArctanForwardContinuityStage n
  have hboxed : forall t
      (ht : inDomainInterval
        coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
        coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t),
      qabs (t - x) <= delta.val ->
        (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n).ContainsInterval
            ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
          (QInterval.scaleByRat h
            (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n)).ContainsInterval
            (QInterval.subInterval
              (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h)
                (by
                  change 0 <= x + h /\ x + h <= 1
                  exact ⟨by grind, hupper⟩)
                (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))
              (coordinateTimesArctanIntegralRectangleOnUnit.compute x
                ⟨hx0, hx1⟩
                (arctanRectangleTangentTransportPrecision h (8 * (n + 1))))) /\
          (coordinateTimesArctanForwardSecantBound x h ⟨hx0, hx1⟩ n).width <=
            10 * (precisionAtStage n).val := by
    intro t ht hclose
    have hvalueFunction :=
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit_near_of_qabs_le
        eps ⟨hx0, hx1⟩ ht (by
          simpa [eps, delta, coordinateTimesArctanForwardContinuityRadius] using hclose)
    have hvalue :
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute m).NearAt
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
          (precisionAtStage n) := by
      change ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute m).NearAt
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
        (precisionAtStage n) at hvalueFunction
      exact hvalueFunction
    simpa only [m, coordinateTimesArctanForwardSecantBound] using
      coordinateTimesArctanIntegralRectangleOnUnit_forward_common_secant_value_enclosure
        hx0 hx1 hpos hupper ht n m hsmall hvalue
  constructor
  · intro t ht hclose
    simpa [delta, m] using (hboxed t ht (by simpa [delta] using hclose)).1
  constructor
  · have hzero : qabs (x - x) <= delta.val := by
      have hsub : x - x = 0 := by grind
      rw [hsub]
      simpa [qabs] using Rat.le_of_lt delta.property
    have hlocal := (hboxed x ⟨hx0, hx1⟩ hzero).2.1
    have hmem : inDomainInterval
        coordinateTimesArctanIntegralRectangleOnUnit.lower
        coordinateTimesArctanIntegralRectangleOnUnit.upper (x + h) := by
      change 0 <= x + h /\ x + h <= 1
      exact ⟨by grind, hupper⟩
    unfold endpointDifferenceInterval
    rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
          coordinateTimesArctanIntegralRectangleOnUnit hmem,
        FunctionOnInterval.toRealFunRaw_compute_of_mem
          coordinateTimesArctanIntegralRectangleOnUnit ⟨hx0, hx1⟩]
    exact hlocal
  · have hzero : qabs (x - x) <= delta.val := by
      have hsub : x - x = 0 := by grind
      rw [hsub]
      simpa [qabs] using Rat.le_of_lt delta.property
    simpa [delta] using (hboxed x ⟨hx0, hx1⟩ hzero).2.2

/-- The step-aware rectangle stage used by a positive unit-branch cell is
already narrow enough at the global endpoint.  This supplies the endpoint
width half of the later two-stage FTC certificate without selecting a second
ad hoc rectangle schedule. -/
theorem arctanRectangleTangentTransportPrecision_atOne_width_le_stageTolerance
    {h : Rat} (hpos : 0 < h) (hle : h <= 1) (n : Nat) :
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne
      (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))).width <=
        (precisionAtStage n).val := by
  let eps : QPos :=
    { val := h * (precisionAtStage (8 * (n + 1))).val / 16
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos (Rat.mul_pos hpos
          (precisionAtStage (8 * (n + 1))).property)
          ((Rat.inv_pos).2 (by decide +kernel)) }
  let N : Nat := 256 * (eps.val.den + 1)
  have hN : arctanRectangleTangentTransportPrecision h (8 * (n + 1)) = N := by
    simp only [arctanRectangleTangentTransportPrecision, dif_pos hpos]
    rfl
  have hNrect : 4 * (eps.val.den + 1) <= N := by
    dsimp [N]
    omega
  have hrectangle :
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne N).width <= eps.val := by
    change (ArctanGeometry.arctanIntegralRectangleCompute (1 : Rat) N).width <= _
    exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
      (by decide +kernel) (by decide +kernel) eps N hNrect
  have heps : eps.val <= (precisionAtStage n).val := by
    have hp8 : 0 <= (precisionAtStage (8 * (n + 1))).val :=
      Rat.le_of_lt (precisionAtStage (8 * (n + 1))).property
    have hscaled : h * (precisionAtStage (8 * (n + 1))).val / 16 <=
        (precisionAtStage (8 * (n + 1))).val := by
      calc
        h * (precisionAtStage (8 * (n + 1))).val / 16 =
            h * ((precisionAtStage (8 * (n + 1))).val / 16) := by
              grind [Rat.div_def]
        _ <= 1 * ((precisionAtStage (8 * (n + 1))).val / 16) :=
          Rat.mul_le_mul_of_nonneg_right hle (by
            rw [Rat.div_def]
            exact Rat.mul_nonneg hp8 (by decide +kernel))
        _ = (precisionAtStage (8 * (n + 1))).val / 16 := by grind
        _ <= (precisionAtStage (8 * (n + 1))).val := by
          rw [Rat.div_def]
          grind
    calc
      eps.val = h * (precisionAtStage (8 * (n + 1))).val / 16 := by rfl
      _ <= (precisionAtStage (8 * (n + 1))).val := hscaled
      _ <= (precisionAtStage n).val / 8 :=
        twoSided_precision_stage_le_eighth n
      _ <= (precisionAtStage n).val := by
        rw [Rat.div_def]
        grind
  rw [hN]
  exact Rat.le_trans hrectangle heps

/-- The outer derivative stage used for the product FTC candidate spends a
factor ten on the local common-box width. -/
def coordinateTimesArctanForwardOuterStage (eps : QPos) : Nat :=
  10 * (eps.val.den + 1)

/-- The ten local tolerances in the forward common box fit inside the
requested outer tolerance at `coordinateTimesArctanForwardOuterStage`. -/
theorem ten_mul_precisionAtStage_coordinateTimesArctanForwardOuterStage_le
    (eps : QPos) :
    10 * (precisionAtStage (coordinateTimesArctanForwardOuterStage eps)).val <=
      eps.val := by
  let d : Nat := eps.val.den + 1
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hstagepos : 0 < 10 * d := Nat.mul_pos (by decide +kernel) hdpos
  have hfactor : 0 <= (10 : Rat) := by decide +kernel
  have hden : 1 / (d : Rat) <= eps.val :=
    FTC.one_div_den_succ_le_of_pos eps.property
  have hrewrite :
      (10 : Rat) * (1 / (((10 * d : Nat) : Rat))) = 1 / (d : Rat) := by
    rw [Rat.natCast_mul]
    change (10 : Rat) * (1 / ((10 : Rat) * (d : Rat))) = 1 / (d : Rat)
    rw [Rat.div_def, Rat.inv_mul_rev]
    have hten : (10 : Rat) * (10 : Rat)⁻¹ = 1 := by decide +kernel
    grind [Rat.mul_assoc, Rat.mul_comm]
  unfold coordinateTimesArctanForwardOuterStage
  change 10 * (precisionAtStage (10 * d)).val <= eps.val
  rw [precisionAtStage, dif_neg (Nat.ne_of_gt hstagepos)]
  calc
    10 * (1 / (((10 * d : Nat) : Rat))) = 1 / (d : Rat) := hrewrite
    _ <= eps.val := hden

/-- The preceding common-box construction is available directly from the
checked rational epsilon--delta continuity theorem for the product
derivative.  For every forward-derivative stage it chooses one continuity
radius and one derivative evaluation stage.  Any derivative value in that
radius and the concrete endpoint secant then share a box of width at most ten
stage tolerances.  A later partition proof need only choose every cell width
below this displayed radius. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_range_enclosure
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat)
    (hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    Exists fun delta : QPos => Exists fun m : Nat =>
      forall t
        (ht : inDomainInterval
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t),
        qabs (t - x) <= delta.val ->
          Exists fun bound : QInterval =>
            bound.ContainsInterval
                ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
              (QInterval.scaleByRat h bound).ContainsInterval
                (endpointDifferenceInterval
                  coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
                  x (x + h)
                  (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) /\
                bound.width <= 10 * (precisionAtStage n).val := by
  obtain ⟨delta, m, hcontinuous⟩ :=
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit_epsilonDeltaContinuous
      (precisionAtStage n)
  refine ⟨delta, m, ?_⟩
  intro t ht hclose
  have hvalueFunction := hcontinuous x t ⟨hx0, hx1⟩ ht hclose
  have hvalue :
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute m).NearAt
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
        (precisionAtStage n) := by
    change ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
        ⟨hx0, hx1⟩).compute m).NearAt
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
      (precisionAtStage n) at hvalueFunction
    exact hvalueFunction
  let N : Nat := arctanRectangleTangentTransportPrecision h (8 * (n + 1))
  let bound : QInterval :=
    QInterval.hull
      (QInterval.expand
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute N)
        (2 * (precisionAtStage n).val))
      (QInterval.expand
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute m)
        (2 * (precisionAtStage n).val))
  have hboxed :
      bound.ContainsInterval
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
        (QInterval.scaleByRat h bound).ContainsInterval
          (QInterval.subInterval
            (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h)
              (by
                change 0 <= x + h /\ x + h <= 1
                exact ⟨by grind, hupper⟩) N)
            (coordinateTimesArctanIntegralRectangleOnUnit.compute x
              ⟨hx0, hx1⟩ N)) /\
          bound.width <= 10 * (precisionAtStage n).val := by
    simpa only [N, bound] using
      coordinateTimesArctanIntegralRectangleOnUnit_forward_common_secant_value_enclosure
        hx0 hx1 hpos hupper ht n m hsmall hvalue
  refine ⟨bound, hboxed.1, ?_, hboxed.2.2⟩
  have hmem : inDomainInterval
      coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper (x + h) := by
    change 0 <= x + h /\ x + h <= 1
    exact ⟨by grind, hupper⟩
  unfold endpointDifferenceInterval
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
        coordinateTimesArctanIntegralRectangleOnUnit hmem,
    FunctionOnInterval.toRealFunRaw_compute_of_mem
      coordinateTimesArctanIntegralRectangleOnUnit ⟨hx0, hx1⟩]
  exact hboxed.2.1

/-- The common secant-and-range box can be selected before the point in its
continuity radius is given.  This quantifier order is the form needed for a
rational partition cell: one finite box covers every candidate derivative
value in the cell and its one endpoint difference. -/
theorem coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_uniform_range_enclosure
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat)
    (hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat))) :
    Exists fun delta : QPos => Exists fun m : Nat => Exists fun bound : QInterval =>
      (forall t
        (ht : inDomainInterval
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t),
        qabs (t - x) <= delta.val ->
          bound.ContainsInterval
            ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)) /\
        (QInterval.scaleByRat h bound).ContainsInterval
          (endpointDifferenceInterval
            coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
            x (x + h)
            (arctanRectangleTangentTransportPrecision h (8 * (n + 1)))) /\
          bound.width <= 10 * (precisionAtStage n).val := by
  let eps : QPos := precisionAtStage n
  let delta : QPos :=
    { val := eps.val / 6
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel)) }
  let m : Nat := 4 * ((eps.val / 2).den + 1)
  have hcontinuous :
      forall x y
        (hx : inDomainInterval
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper x)
        (hy : inDomainInterval
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper y),
        qabs (y - x) <= delta.val ->
          QInterval.NearAt
            (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx m)
            (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute y hy m) eps := by
    intro x y hx hy hclose
    simpa [eps, delta, m] using
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit_near_of_qabs_le
        eps hx hy (by simpa [delta] using hclose))
  let N : Nat := arctanRectangleTangentTransportPrecision h (8 * (n + 1))
  let bound : QInterval :=
    QInterval.hull
      (QInterval.expand
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute N)
        (2 * (precisionAtStage n).val))
      (QInterval.expand
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute m)
        (2 * (precisionAtStage n).val))
  have hboxed :
      forall t
        (ht : inDomainInterval
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
          coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t),
        qabs (t - x) <= delta.val ->
          bound.ContainsInterval
              ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
            (QInterval.scaleByRat h bound).ContainsInterval
              (endpointDifferenceInterval
                coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
                x (x + h) N) /\
              bound.width <= 10 * (precisionAtStage n).val := by
    intro t ht hclose
    have hvalueFunction := hcontinuous x t ⟨hx0, hx1⟩ ht hclose
    have hvalue :
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x ⟨hx0, hx1⟩).compute m).NearAt
          ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
          (precisionAtStage n) := by
      change ((coordinateTimesArctanIntegralRectangleDerivativeRaw x
          ⟨hx0, hx1⟩).compute m).NearAt
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m)
        (precisionAtStage n) at hvalueFunction
      exact hvalueFunction
    have hlocal :=
      coordinateTimesArctanIntegralRectangleOnUnit_forward_common_secant_value_enclosure
        hx0 hx1 hpos hupper ht n m hsmall hvalue
    have hlocal' :
        bound.ContainsInterval
            ((coordinateTimesArctanIntegralRectangleDerivativeRaw t ht).compute m) /\
          (QInterval.scaleByRat h bound).ContainsInterval
            (QInterval.subInterval
              (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h)
                (by
                  change 0 <= x + h /\ x + h <= 1
                  exact ⟨by grind, hupper⟩) N)
              (coordinateTimesArctanIntegralRectangleOnUnit.compute x
                ⟨hx0, hx1⟩ N)) /\
            bound.width <= 10 * (precisionAtStage n).val := by
      simpa only [N, bound] using hlocal
    refine ⟨hlocal'.1, ?_, hlocal'.2.2⟩
    have hmem : inDomainInterval
        coordinateTimesArctanIntegralRectangleOnUnit.lower
        coordinateTimesArctanIntegralRectangleOnUnit.upper (x + h) := by
      change 0 <= x + h /\ x + h <= 1
      exact ⟨by grind, hupper⟩
    unfold endpointDifferenceInterval
    rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
          coordinateTimesArctanIntegralRectangleOnUnit hmem,
      FunctionOnInterval.toRealFunRaw_compute_of_mem
        coordinateTimesArctanIntegralRectangleOnUnit ⟨hx0, hx1⟩]
    exact hlocal'.2.1
  have hzero : qabs (x - x) <= delta.val := by
    have hsub : x - x = 0 := by grind
    rw [hsub]
    simpa [qabs] using Rat.le_of_lt delta.property
  have hbase := hboxed x ⟨hx0, hx1⟩ hzero
  exact ⟨delta, m, bound, fun t ht hclose => (hboxed t ht hclose).1,
    hbase.2.1, hbase.2.2⟩

/-- A concrete number of unit cells that is small enough both for a rational
continuity radius and for the forward derivative's stage-dependent step
budget.  It is a finite denominator product, so selecting the partition uses
no density or completeness principle. -/
def coordinateTimesArctanForwardPartitionPieces (delta : QPos) (n : Nat) : Nat :=
  (delta.val.den + 1) * (72 * (n + 1))

theorem coordinateTimesArctanForwardPartitionPieces_positive
    (delta : QPos) (n : Nat) :
    0 < coordinateTimesArctanForwardPartitionPieces delta n := by
  unfold coordinateTimesArctanForwardPartitionPieces
  exact Nat.mul_pos (Nat.succ_pos _) (by omega)

theorem coordinateTimesArctanForwardPartition_mesh_eq_inverse
    (delta : QPos) (n : Nat) :
    mesh 0 1 (coordinateTimesArctanForwardPartitionPieces delta n) =
      1 / ((coordinateTimesArctanForwardPartitionPieces delta n : Nat) : Rat) := by
  have hpos : 0 < coordinateTimesArctanForwardPartitionPieces delta n :=
    coordinateTimesArctanForwardPartitionPieces_positive delta n
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hpos)]
  grind [Rat.sub_eq_add_neg]

/-- The selected unit mesh is within the supplied continuity radius. -/
theorem coordinateTimesArctanForwardPartition_mesh_le_radius
    (delta : QPos) (n : Nat) :
    mesh 0 1 (coordinateTimesArctanForwardPartitionPieces delta n) <= delta.val := by
  let p : Nat := delta.val.den + 1
  let q : Nat := 72 * (n + 1)
  have hp : 0 < p := by
    dsimp [p]
    exact Nat.succ_pos _
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hpieces : coordinateTimesArctanForwardPartitionPieces delta n = p * q := by
    rfl
  have hmesh := coordinateTimesArctanForwardPartition_mesh_eq_inverse delta n
  rw [hpieces] at hmesh
  rw [hpieces, hmesh]
  calc
    1 / ((p * q : Nat) : Rat) <= 1 / (p : Rat) :=
      FTC.one_div_nat_antitone hp hpq (Nat.le_mul_of_pos_right p hq)
    _ <= delta.val := one_div_den_succ_le_of_pos delta.property

/-- The same selected unit mesh is within the forward derivative's positive
step budget at stage n. -/
theorem coordinateTimesArctanForwardPartition_mesh_le_forward_step
    (delta : QPos) (n : Nat) :
    mesh 0 1 (coordinateTimesArctanForwardPartitionPieces delta n) <=
      1 / (((72 * (n + 1) : Nat) : Rat)) := by
  let p : Nat := delta.val.den + 1
  let q : Nat := 72 * (n + 1)
  have hp : 0 < p := by
    dsimp [p]
    exact Nat.succ_pos _
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hpieces : coordinateTimesArctanForwardPartitionPieces delta n = p * q := by
    rfl
  have hmesh := coordinateTimesArctanForwardPartition_mesh_eq_inverse delta n
  rw [hpieces] at hmesh
  rw [hpieces, hmesh]
  have hqle : q <= p * q := by
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right q hp
  exact FTC.one_div_nat_antitone hq hpq hqle

/-- The uniform partition used by the concrete two-stage FTC candidate for
the positive product.  Its mesh simultaneously meets the explicit
continuity radius and the forward derivative step budget. -/
def coordinateTimesArctanForwardFTCPartition (eps : QPos) :
    RationalPartition 0 1 :=
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let pieces : Nat := coordinateTimesArctanForwardPartitionPieces delta n
  RationalPartition.uniform 0 1 pieces
    (coordinateTimesArctanForwardPartitionPieces_positive delta n)
    (by decide +kernel)

/-- The common derivative stage assigned to all cells of the selected
positive-product partition. -/
def coordinateTimesArctanForwardFTCDerivativeStage (eps : QPos) : Nat :=
  coordinateTimesArctanForwardContinuityStage
    (coordinateTimesArctanForwardOuterStage eps)

/-- The common endpoint stage assigned to all cells of the selected uniform
partition.  Uniformity makes the step-aware transport stage literally the
same natural number on every cell. -/
def coordinateTimesArctanForwardFTCEndpointStage (eps : QPos) : Nat :=
  arctanRectangleTangentTransportPrecision
    (mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces)
    (8 * (coordinateTimesArctanForwardOuterStage eps + 1))

/-- The executable derivative bound on one selected uniform cell. -/
def coordinateTimesArctanForwardFTCDerivativeBound
    (eps : QPos) (k : Nat)
    (hk : k < (coordinateTimesArctanForwardFTCPartition eps).pieces) : QInterval :=
  let P := coordinateTimesArctanForwardFTCPartition eps
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  coordinateTimesArctanForwardSecantBound
    (P.point k) (mesh 0 1 P.pieces)
    (by
      change 0 <= P.point k /\ P.point k <= 1
      exact P.point_in_bounds (Nat.le_of_lt hk)) n

theorem coordinateTimesArctanForwardFTCPartition_mesh_le_radius (eps : QPos) :
    mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces <=
      (coordinateTimesArctanForwardContinuityRadius
        (coordinateTimesArctanForwardOuterStage eps)).val := by
  change mesh 0 1
    (coordinateTimesArctanForwardPartitionPieces
      (coordinateTimesArctanForwardContinuityRadius
        (coordinateTimesArctanForwardOuterStage eps))
      (coordinateTimesArctanForwardOuterStage eps)) <= _
  exact coordinateTimesArctanForwardPartition_mesh_le_radius _ _

theorem coordinateTimesArctanForwardFTCPartition_mesh_le_forward_step (eps : QPos) :
    mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces <=
      1 / (((72 * (coordinateTimesArctanForwardOuterStage eps + 1) : Nat) : Rat)) := by
  change mesh 0 1
    (coordinateTimesArctanForwardPartitionPieces
      (coordinateTimesArctanForwardContinuityRadius
        (coordinateTimesArctanForwardOuterStage eps))
      (coordinateTimesArctanForwardOuterStage eps)) <= _
  exact coordinateTimesArctanForwardPartition_mesh_le_forward_step _ _

theorem coordinateTimesArctanForwardFTCPartition_mesh_pos (eps : QPos) :
    0 < mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces := by
  let P := coordinateTimesArctanForwardFTCPartition eps
  have hp : 0 < P.pieces := P.positive
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hp), Rat.div_def]
  exact Rat.mul_pos (by decide +kernel)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hp))

theorem coordinateTimesArctanForwardFTCPartition_mesh_le_one (eps : QPos) :
    mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces <= 1 := by
  let P := coordinateTimesArctanForwardFTCPartition eps
  have hp : 0 < P.pieces := P.positive
  have hpOne : 1 <= P.pieces := Nat.succ_le_of_lt hp
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hp)]
  calc
    (1 - 0) / (P.pieces : Rat) = 1 / (P.pieces : Rat) := by grind
    _ <= 1 / ((1 : Nat) : Rat) :=
      FTC.one_div_nat_antitone (Nat.succ_pos 0) hp hpOne
    _ = 1 := by decide +kernel

/-- Each selected derivative bound contains every derivative value on its
own uniform cell, at the single executable continuity stage. -/
theorem coordinateTimesArctanForwardFTCDerivativeBound_contains
    (eps : QPos) (k : Nat)
    (hk : k < (coordinateTimesArctanForwardFTCPartition eps).pieces)
    (t : Rat)
    (ht : ((coordinateTimesArctanForwardFTCPartition eps).cell k hk).contains t) :
    (coordinateTimesArctanForwardFTCDerivativeBound eps k hk).ContainsInterval
      (coordinateTimesArctanIntegralRectangleDerivativeOnUnit.toRealFunRaw.compute t
        (coordinateTimesArctanForwardFTCDerivativeStage eps)) := by
  let P := coordinateTimesArctanForwardFTCPartition eps
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let h : Rat := mesh 0 1 P.pieces
  change (P.cell k hk).contains t at ht
  have htInDomain : inDomainInterval 0 1 t :=
    (P.cell k hk).contains_inDomain ht
  change P.point k <= t /\ t <= P.point (k + 1) at ht
  have hleft : 0 <= P.point k /\ P.point k <= 1 :=
    P.point_in_bounds (Nat.le_of_lt hk)
  have htDomain : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t := by
    change 0 <= t /\ t <= 1
    exact htInDomain
  have hpos : 0 < h := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_pos eps
  have hupper : P.point k + h <= 1 := by
    dsimp [P, h]
    let pieces := coordinateTimesArctanForwardPartitionPieces delta n
    change leftPoint 0 1 pieces k + mesh 0 1 pieces <= 1
    have hstep := leftPoint_step 0 1 pieces k
    have hpieces : 0 < pieces :=
      coordinateTimesArctanForwardPartitionPieces_positive delta n
    calc
      leftPoint 0 1 pieces k + mesh 0 1 pieces = leftPoint 0 1 pieces (k + 1) := by
        rw [← hstep]
        grind [Rat.sub_eq_add_neg]
      _ <= leftPoint 0 1 pieces pieces :=
        leftPoint_monotone hpieces (by decide +kernel) (Nat.succ_le_of_lt hk)
      _ = 1 := leftPoint_endpoint hpieces
  have hstep : P.point (k + 1) - P.point k = h := by
    dsimp [P, h]
    exact leftPoint_step 0 1
      (coordinateTimesArctanForwardPartitionPieces delta n) k
  have hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat)) := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_le_forward_step eps
  have hclose : qabs (t - P.point k) <= delta.val := by
    have hnonneg : 0 <= t - P.point k := by grind [Rat.sub_eq_add_neg]
    rw [qabs_eq_self_of_nonneg hnonneg]
    calc
      t - P.point k <= P.point (k + 1) - P.point k := by
        grind [Rat.sub_eq_add_neg]
      _ = h := hstep
      _ <= delta.val := by
        simpa [delta] using coordinateTimesArctanForwardFTCPartition_mesh_le_radius eps
  have hlocal :=
    coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_explicit_uniform_range_enclosure
      hleft.1 hleft.2 hpos hupper n hsmall
  have hvalue := hlocal.1 t htDomain hclose
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit htDomain]
  have htDeriv : inDomainInterval
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.lower
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.upper t := by
    change 0 <= t /\ t <= 1
    exact htDomain
  change QInterval.ContainsInterval _
    ((coordinateTimesArctanIntegralRectangleDerivativeRaw t htDeriv).compute
      (coordinateTimesArctanForwardContinuityStage
        (coordinateTimesArctanForwardOuterStage eps)))
  simpa [coordinateTimesArctanForwardFTCDerivativeBound,
    coordinateTimesArctanForwardFTCDerivativeStage,
    coordinateTimesArctanIntegralRectangleDerivativeRaw,
    FunctionOnInterval.toRealFunRaw_compute_of_mem, P, n, h] using hvalue

/-- The same selected cell bound contains the primitive's endpoint
difference when scaled by that cell's width.  Because the partition is
uniform, all of these endpoint intervals use one literal transport stage. -/
theorem coordinateTimesArctanForwardFTCDerivativeBound_contains_endpointDifference
    (eps : QPos) (k : Nat)
    (hk : k < (coordinateTimesArctanForwardFTCPartition eps).pieces) :
    QInterval.ContainsInterval
      (((coordinateTimesArctanForwardFTCPartition eps).cell k hk).scaleBound
        (coordinateTimesArctanForwardFTCDerivativeBound eps k hk))
      (endpointDifferenceInterval
        coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
        ((coordinateTimesArctanForwardFTCPartition eps).cell k hk).lower
        ((coordinateTimesArctanForwardFTCPartition eps).cell k hk).upper
        (coordinateTimesArctanForwardFTCEndpointStage eps)) := by
  let P := coordinateTimesArctanForwardFTCPartition eps
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let h : Rat := mesh 0 1 P.pieces
  have hleft : 0 <= P.point k /\ P.point k <= 1 :=
    P.point_in_bounds (Nat.le_of_lt hk)
  have hpos : 0 < h := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_pos eps
  have hupper : P.point k + h <= 1 := by
    dsimp [P, h]
    let pieces := coordinateTimesArctanForwardPartitionPieces delta n
    change leftPoint 0 1 pieces k + mesh 0 1 pieces <= 1
    have hstep := leftPoint_step 0 1 pieces k
    have hpieces : 0 < pieces :=
      coordinateTimesArctanForwardPartitionPieces_positive delta n
    calc
      leftPoint 0 1 pieces k + mesh 0 1 pieces = leftPoint 0 1 pieces (k + 1) := by
        rw [← hstep]
        grind [Rat.sub_eq_add_neg]
      _ <= leftPoint 0 1 pieces pieces :=
        leftPoint_monotone hpieces (by decide +kernel) (Nat.succ_le_of_lt hk)
      _ = 1 := leftPoint_endpoint hpieces
  have hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat)) := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_le_forward_step eps
  have hnext : P.point k + h = P.point (k + 1) := by
    have hstep : P.point (k + 1) - P.point k = h := by
      dsimp [P, h]
      exact leftPoint_step 0 1
        (coordinateTimesArctanForwardPartitionPieces delta n) k
    grind [Rat.sub_eq_add_neg]
  have hlocal :=
    coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_explicit_uniform_range_enclosure
      hleft.1 hleft.2 hpos hupper n hsmall
  change QInterval.ContainsInterval
    (QInterval.scaleByRat (P.point (k + 1) - P.point k)
      (coordinateTimesArctanForwardFTCDerivativeBound eps k hk))
    (endpointDifferenceInterval
      coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
      (P.point k) (P.point (k + 1))
      (coordinateTimesArctanForwardFTCEndpointStage eps))
  rw [← hnext]
  have hscale : P.point k + h - P.point k = h := by
    grind [Rat.sub_eq_add_neg]
  rw [hscale]
  simpa [coordinateTimesArctanForwardFTCDerivativeBound,
    coordinateTimesArctanForwardFTCEndpointStage, P, n, h] using hlocal.2.1

/-- Every selected derivative hull has the ten-tolerance width budget used in
the finite uniform Riemann-sum estimate. -/
theorem coordinateTimesArctanForwardFTCDerivativeBound_width_le
    (eps : QPos) (k : Nat)
    (hk : k < (coordinateTimesArctanForwardFTCPartition eps).pieces) :
    (coordinateTimesArctanForwardFTCDerivativeBound eps k hk).width <=
      10 * (precisionAtStage (coordinateTimesArctanForwardOuterStage eps)).val := by
  let P := coordinateTimesArctanForwardFTCPartition eps
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let h : Rat := mesh 0 1 P.pieces
  have hleft : 0 <= P.point k /\ P.point k <= 1 :=
    P.point_in_bounds (Nat.le_of_lt hk)
  have hpos : 0 < h := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_pos eps
  have hupper : P.point k + h <= 1 := by
    dsimp [P, h]
    let pieces := coordinateTimesArctanForwardPartitionPieces delta n
    change leftPoint 0 1 pieces k + mesh 0 1 pieces <= 1
    have hstep := leftPoint_step 0 1 pieces k
    have hpieces : 0 < pieces :=
      coordinateTimesArctanForwardPartitionPieces_positive delta n
    calc
      leftPoint 0 1 pieces k + mesh 0 1 pieces = leftPoint 0 1 pieces (k + 1) := by
        rw [← hstep]
        grind [Rat.sub_eq_add_neg]
      _ <= leftPoint 0 1 pieces pieces :=
        leftPoint_monotone hpieces (by decide +kernel) (Nat.succ_le_of_lt hk)
      _ = 1 := leftPoint_endpoint hpieces
  have hsmall : h <= 1 / (((72 * (n + 1) : Nat) : Rat)) := by
    simpa [h, P] using coordinateTimesArctanForwardFTCPartition_mesh_le_forward_step eps
  have hlocal :=
    coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_explicit_uniform_range_enclosure
      hleft.1 hleft.2 hpos hupper n hsmall
  simpa [coordinateTimesArctanForwardFTCDerivativeBound, P, n, h] using hlocal.2.2

/-- The finite derivative-bound sum on the selected unit partition has width
at most the requested outer tolerance. -/
theorem coordinateTimesArctanForwardFTCRiemann_width_le (eps : QPos) :
    ((coordinateTimesArctanForwardFTCPartition eps).boundIntegralSum
      (fun k hk => coordinateTimesArctanForwardFTCDerivativeBound eps k hk)).width <=
        eps.val := by
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let delta : QPos := coordinateTimesArctanForwardContinuityRadius n
  let pieces := coordinateTimesArctanForwardPartitionPieces delta n
  have hpieces : 0 < pieces :=
    coordinateTimesArctanForwardPartitionPieces_positive delta n
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le
    (a := (0 : Rat)) (b := (1 : Rat)) pieces hpieces (by decide +kernel)
    (fun k hk => coordinateTimesArctanForwardFTCDerivativeBound eps k
      (by simpa [coordinateTimesArctanForwardFTCPartition, RationalPartition.uniform,
        pieces, delta, n] using hk))
    (10 * (precisionAtStage n).val) (by
      intro k hk
      simpa [coordinateTimesArctanForwardFTCPartition, RationalPartition.uniform,
        pieces, delta, n] using
        coordinateTimesArctanForwardFTCDerivativeBound_width_le eps k
          (by simpa [coordinateTimesArctanForwardFTCPartition, RationalPartition.uniform,
            pieces, delta, n] using hk))
  have houter := ten_mul_precisionAtStage_coordinateTimesArctanForwardOuterStage_le eps
  change ((RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)).boundIntegralSum
    (fun k hk => coordinateTimesArctanForwardFTCDerivativeBound eps k
      (by simpa [coordinateTimesArctanForwardFTCPartition, RationalPartition.uniform,
        pieces, delta, n] using hk))).width <= eps.val
  calc
    _ <= (1 - 0) * (10 * (precisionAtStage n).val) := hsum
    _ = 10 * (precisionAtStage n).val := by grind
    _ <= eps.val := by simpa [n] using houter

/-- The selected common endpoint stage is narrow enough for the global
primitive endpoint interval as well. -/
theorem coordinateTimesArctanForwardFTCEndpoint_width_le (eps : QPos) :
    (endpointDifferenceInterval
      coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
      (coordinateTimesArctanForwardFTCEndpointStage eps)).width <= eps.val := by
  let n : Nat := coordinateTimesArctanForwardOuterStage eps
  let h : Rat := mesh 0 1 (coordinateTimesArctanForwardFTCPartition eps).pieces
  have hpos : 0 < h := by
    simpa [h] using coordinateTimesArctanForwardFTCPartition_mesh_pos eps
  have hle : h <= 1 := by
    simpa [h] using coordinateTimesArctanForwardFTCPartition_mesh_le_one eps
  have hendpoint := arctanRectangleTangentTransportPrecision_atOne_width_le_stageTolerance
    hpos hle n
  change (endpointDifferenceCompute coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
    (coordinateTimesArctanForwardFTCEndpointStage eps)).width <= eps.val
  rw [coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq]
  calc
    _ <= (precisionAtStage n).val := by
      simpa [coordinateTimesArctanForwardFTCEndpointStage, h, n] using hendpoint
    _ = 1 * (precisionAtStage n).val := by grind
    _ <= 10 * (precisionAtStage n).val :=
      Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
        (Rat.le_of_lt (precisionAtStage n).property)
    _ <= eps.val := by
      simpa [n] using ten_mul_precisionAtStage_coordinateTimesArctanForwardOuterStage_le eps

/-- A fully executable two-stage finite FTC certificate for the positive
product `x * arctan x` on `[0,1]`.  Its derivative stage is selected by the
explicit continuity modulus; its endpoint stage is the common uniform-cell
tangent-transport precision. -/
def coordinateTimesArctanForwardTwoStageFTC :
    TwoStageCandidateDerivativeFTC
      coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit.toRealFunRaw 0 1 where
  primitive_valid := FunctionOnInterval.toRealFunRaw_valid
    coordinateTimesArctanIntegralRectangleOnUnit
  choosePartition := coordinateTimesArctanForwardFTCPartition
  chooseDerivativeStage := coordinateTimesArctanForwardFTCDerivativeStage
  chooseEndpointStage := coordinateTimesArctanForwardFTCEndpointStage
  derivativeBound := coordinateTimesArctanForwardFTCDerivativeBound
  primitive_domain_on := by
    intro eps i hi
    change 0 <= (coordinateTimesArctanForwardFTCPartition eps).point i /\
      (coordinateTimesArctanForwardFTCPartition eps).point i <= 1
    exact (coordinateTimesArctanForwardFTCPartition eps).point_in_bounds hi
  candidate_domain_on := by
    intro eps k hk x hx
    change 0 <= x /\ x <= 1
    exact ((coordinateTimesArctanForwardFTCPartition eps).cell k hk).contains_inDomain hx
  candidate_contained := by
    intro eps k hk x hx
    exact coordinateTimesArctanForwardFTCDerivativeBound_contains eps k hk x hx
  local_endpoint_contained := by
    intro eps k hk
    simpa [RationalPartition.cell] using
      coordinateTimesArctanForwardFTCDerivativeBound_contains_endpointDifference eps k hk
  riemann_width := coordinateTimesArctanForwardFTCRiemann_width_le
  endpoint_width := coordinateTimesArctanForwardFTCEndpoint_width_le

/-- The derivative-bound Riemann raw and primitive endpoint raw for
`x * arctan x` are equivalent by the finite two-stage FTC assembly. -/
theorem coordinateTimesArctanForwardTwoStageFTC_equiv_endpoint :
    coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.Equiv
      coordinateTimesArctanForwardTwoStageFTC.endpointRaw :=
  twoStageCandidateDerivativeFTC coordinateTimesArctanForwardTwoStageFTC

/-- The stricter two-sided product budget is small enough both for the
forward product certificate at the reversed basepoint and for transporting
the explicit derivative box back across a negative step. -/
private theorem coordinateTimesArctan_twoSided_step_implies_forward
    {k : Rat} (n : Nat)
    (hsmall : k <= 1 / (((648 * (n + 1) : Nat) : Rat))) :
    k <= 1 / (((72 * (8 * (n + 1) + 1) : Nat) : Rat)) := by
  have hforwardPos : 0 < 72 * (8 * (n + 1) + 1) := by omega
  have htwoSidedPos : 0 < 648 * (n + 1) := by omega
  have hdenOrder : 72 * (8 * (n + 1) + 1) <= 648 * (n + 1) := by omega
  have hreciprocal := FTC.one_div_nat_antitone hforwardPos htwoSidedPos hdenOrder
  exact Rat.le_trans hsmall hreciprocal

private theorem coordinateTimesArctan_twoSided_step_le_arctanBudget
    {k : Rat} (n : Nat)
    (hsmall : k <= 1 / (((648 * (n + 1) : Nat) : Rat))) :
    k <= 1 / (((72 * (n + 1) : Nat) : Rat)) := by
  have harctanPos : 0 < 72 * (n + 1) := by omega
  have htwoSidedPos : 0 < 648 * (n + 1) := by omega
  have hdenOrder : 72 * (n + 1) <= 648 * (n + 1) := by omega
  have hreciprocal := FTC.one_div_nat_antitone harctanPos htwoSidedPos hdenOrder
  exact Rat.le_trans hsmall hreciprocal

/-- The literal interval product `x ↦ x * arctan(x)` has the two-sided
derivative `arctan(x) + x / (1 + x^2)` throughout the rational unit branch.

For a negative step the finite quotient is reversed to a positive quotient
at `x + h`.  The proof then transports the *explicit* product-rule box back
to `x`, using the rectangle arctangent quotient and the kernel's rational
Lipschitz estimate.  Thus this is still a finite certificate, rather than an
invocation of a general product rule or of real-number completeness. -/
def coordinateTimesArctanIntegralRectangleOnUnit_hasDerivative :
    HasDerivativeOnInterval coordinateTimesArctanIntegralRectangleOnUnit
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit := by
  refine
    { same_lower := rfl
      same_upper := rfl
      stepPrecision := fun n => 648 * (n + 1)
      evalPrecision := fun _x h n =>
        arctanRectangleTangentTransportPrecision (qabs h)
          (8 * (8 * (n + 1) + 1))
      close := ?_ }
  intro x h n hx hxh hdx hh hsmall
  change 0 <= x /\ x <= 1 at hx hdx
  change 0 <= x + h /\ x + h <= 1 at hxh
  have hstage :
      (precisionAtStage (8 * (n + 1))).val <=
        (precisionAtStage n).val / 8 :=
    twoSided_precision_stage_le_eighth n
  have hprecisionNonneg : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  by_cases hpos : 0 < h
  · have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
    rw [hqabs] at hsmall ⊢
    let m : Nat := 8 * (n + 1)
    have hforwardSmall := coordinateTimesArctan_twoSided_step_implies_forward n hsmall
    have hforward :=
      (coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt x hx.1 hx.2).close
        h m hxh hpos hforwardSmall
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h) hxh
          (arctanRectangleTangentTransportPrecision h (8 * (m + 1))))
        (coordinateTimesArctanIntegralRectangleOnUnit.compute x hx
          (arctanRectangleTangentTransportPrecision h (8 * (m + 1)))) h)
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute
        (arctanRectangleTangentTransportPrecision h (8 * (m + 1)))) m at hforward
    have hforward' : intervalNearAtPrecision
        (QInterval.differenceQuotient
          (coordinateTimesArctanIntegralRectangleOnUnit.compute (x + h) hxh
            (arctanRectangleTangentTransportPrecision h (8 * (m + 1))))
          (coordinateTimesArctanIntegralRectangleOnUnit.compute x hx
            (arctanRectangleTangentTransportPrecision h (8 * (m + 1)))) h)
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute
          (arctanRectangleTangentTransportPrecision h (8 * (m + 1)))) m := by
      simpa [m] using hforward
    have hstage' : (precisionAtStage m).val <= (precisionAtStage n).val := by
      dsimp [m]
      exact Rat.le_trans hstage (by
        rw [Rat.div_def]
        grind)
    exact intervalNearAtPrecision_weaken hforward' hstage'
  · have hneg : h < 0 := by grind
    let k : Rat := -h
    have hkpos : 0 < k := by
      dsimp [k]
      grind
    have hk0 : 0 <= k := Rat.le_of_lt hkpos
    have hqabs : qabs h = k := by
      dsimp [k]
      exact qabs_eq_neg_of_nonpos (Rat.le_of_lt hneg)
    rw [hqabs] at hsmall ⊢
    let y : Rat := x + h
    let m : Nat := 8 * (n + 1)
    let t : Nat := 8 * (m + 1)
    let N : Nat := arctanRectangleTangentTransportPrecision k t
    have hy : 0 <= y /\ y <= 1 := by
      simpa [y] using hxh
    have hyplus : 0 <= y + k /\ y + k <= 1 := by
      rw [show y + k = x by dsimp [y, k]; grind]
      exact hx
    have hsmallForward := coordinateTimesArctan_twoSided_step_implies_forward n hsmall
    have hsmallArctan := coordinateTimesArctan_twoSided_step_le_arctanBudget n hsmall
    have hsmallArctanFine : k <= 1 / (((8 * (t + 1) : Nat) : Rat)) := by
      have hfinePos : 0 < 8 * (t + 1) := by omega
      have hproductPos : 0 < 72 * (m + 1) := by omega
      have hdenOrder : 8 * (t + 1) <= 72 * (m + 1) := by
        dsimp [t]
        omega
      have hreciprocal := FTC.one_div_nat_antitone hfinePos hproductPos hdenOrder
      calc
        k <= 1 / (((72 * (m + 1) : Nat) : Rat)) := by simpa [m] using hsmallForward
        _ <= 1 / (((8 * (t + 1) : Nat) : Rat)) := hreciprocal
    have hproductForward :=
      (coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt y hy.1 hy.2).close
        k m hyplus hkpos hsmallForward
    have harctanForward :=
      (arctanIntegralRectangleOnUnit_forwardDerivativeAt y hy.1 hy.2).close
        k t hyplus hkpos hsmallArctanFine
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute (y + k) hyplus
          (arctanRectangleTangentTransportPrecision k (8 * (m + 1))))
        (coordinateTimesArctanIntegralRectangleOnUnit.compute y hy
          (arctanRectangleTangentTransportPrecision k (8 * (m + 1)))) k)
      ((coordinateTimesArctanIntegralRectangleDerivativeRaw y hy).compute
        (arctanRectangleTangentTransportPrecision k (8 * (m + 1)))) m at hproductForward
    have hyplusEq : y + k = x := by
      dsimp [y, k]
      grind
    let A : QInterval := arctanIntegralRectangleOnUnit.compute x hx N
    let B : QInterval := arctanIntegralRectangleOnUnit.compute y hy N
    let PX : QInterval := coordinateTimesArctanIntegralRectangleOnUnit.compute x hx N
    let PY : QInterval := coordinateTimesArctanIntegralRectangleOnUnit.compute y hy N
    let DX : QInterval := coordinateTimesArctanIntegralRectangleDerivativeOnUnit.compute x hx N
    let DY : QInterval :=
      (coordinateTimesArctanIntegralRectangleDerivativeRaw y hy).compute N
    have hproductNear : intervalNearAtPrecision
        (QInterval.differenceQuotient PX PY k)
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw y hy).compute
          (arctanRectangleTangentTransportPrecision k (8 * (m + 1)))) m := by
      simpa [hyplusEq, A, B, PX, PY, DX, DY, N, t, m, y,
        coordinateTimesArctanIntegralRectangleDerivativeOnUnit_compute] using hproductForward
    have harctanNear : intervalNearAtPrecision
        (QInterval.differenceQuotient A B k)
        { lo := ArctanGeometry.integralKernel y,
          hi := ArctanGeometry.integralKernel y } m := by
      have harctanNearFine : intervalNearAtPrecision
          (QInterval.differenceQuotient A B k)
          { lo := ArctanGeometry.integralKernel y,
            hi := ArctanGeometry.integralKernel y } t := by
        simpa [hyplusEq, arctanIntegralRectangleOnUnit_forwardDerivativeAt, A, B, N, t, m, y,
          RealCompute.ofRat_compute] using harctanForward
      exact intervalNearAtPrecision_weaken harctanNearFine
        (Rat.le_trans (by
          dsimp [t]
          exact twoSided_precision_stage_le_eighth m) (by
            rw [Rat.div_def]
            grind))
    have hkLeOne : k <= 1 := by
      have houterPos : 0 < 648 * (n + 1) := by omega
      have hdenOrder : 1 <= 648 * (n + 1) := by omega
      have hreciprocal := FTC.one_div_nat_antitone (Nat.succ_pos 0) houterPos hdenOrder
      calc
        k <= 1 / (((648 * (n + 1) : Nat) : Rat)) := hsmall
        _ <= 1 / (1 : Rat) := hreciprocal
        _ = 1 := by decide +kernel
    have hkArctanBudget : k <= 1 / (((72 * (n + 1) : Nat) : Rat)) :=
      hsmallArctan
    have htwoK : 2 * k <= (precisionAtStage n).val / 4 :=
      twoSided_step_le_quarterPrecision n hkArctanBudget
    have hpmNonneg : 0 <= (precisionAtStage m).val :=
      Rat.le_of_lt (precisionAtStage m).property
    have hptNonneg : 0 <= (precisionAtStage t).val :=
      Rat.le_of_lt (precisionAtStage t).property
    have hptLePm : (precisionAtStage t).val <= (precisionAtStage m).val / 8 := by
      dsimp [t]
      exact twoSided_precision_stage_le_eighth m
    have hpmLePn : (precisionAtStage m).val <= (precisionAtStage n).val / 8 := by
      dsimp [m]
      exact hstage
    have hkpLePn : k * (precisionAtStage m).val <= (precisionAtStage n).val / 8 := by
      calc
        k * (precisionAtStage m).val <= 1 * (precisionAtStage m).val :=
          Rat.mul_le_mul_of_nonneg_right hkLeOne hpmNonneg
        _ = (precisionAtStage m).val := by grind
        _ <= (precisionAtStage n).val / 8 := hpmLePn
    have hfourK : 4 * k <= (precisionAtStage n).val / 2 := by
      calc
        4 * k = 2 * (2 * k) := by grind
        _ <= 2 * ((precisionAtStage n).val / 4) :=
          Rat.mul_le_mul_of_nonneg_left htwoK (by decide +kernel)
        _ = (precisionAtStage n).val / 2 := by
          grind [Rat.div_def]
    have hleftBudget :
        2 * (precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k <=
          (precisionAtStage n).val := by
      calc
        2 * (precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k <=
            2 * ((precisionAtStage n).val / 8) +
              ((precisionAtStage n).val / 8) +
              ((precisionAtStage n).val / 4) := by
          exact rat_add_le_add
            (rat_add_le_add
              (Rat.mul_le_mul_of_nonneg_left hpmLePn (by decide +kernel)) hkpLePn)
            htwoK
        _ <= (precisionAtStage n).val := by
          grind [Rat.div_def]
    have hrightBudget :
        2 * (precisionAtStage m).val + 4 * k +
            k * (precisionAtStage m).val <=
          (precisionAtStage n).val := by
      calc
        2 * (precisionAtStage m).val + 4 * k +
            k * (precisionAtStage m).val <=
            2 * ((precisionAtStage n).val / 8) +
              ((precisionAtStage n).val / 2) +
              ((precisionAtStage n).val / 8) := by
          exact rat_add_le_add
            (rat_add_le_add
              (Rat.mul_le_mul_of_nonneg_left hpmLePn (by decide +kernel)) hfourK) hkpLePn
        _ <= (precisionAtStage n).val := by
          grind [Rat.div_def]
    have hkernelLip := oneOverOnePlusSquare_lipschitz_on_unit.2
      y x hy.1 hy.2 hx.1 hx.2
    have hkernelDiff : qabs (ArctanGeometry.integralKernel y -
        ArctanGeometry.integralKernel x) <= 2 * k := by
      simpa [ArctanGeometry.integralKernel, y, show x - y = k by
        dsimp [y, k]
        grind, qabs_eq_self_of_nonneg hk0] using hkernelLip
    have hkernelYtoX : ArctanGeometry.integralKernel y <=
        ArctanGeometry.integralKernel x + 2 * k := by
      have h := Rat.le_trans
        (self_le_qabs (ArctanGeometry.integralKernel y -
          ArctanGeometry.integralKernel x)) hkernelDiff
      grind [Rat.sub_eq_add_neg]
    have hkernelXtoY : ArctanGeometry.integralKernel x <=
        ArctanGeometry.integralKernel y + 2 * k := by
      have h := Rat.le_trans
        (self_le_qabs (ArctanGeometry.integralKernel x -
          ArctanGeometry.integralKernel y)) (by
            rw [show ArctanGeometry.integralKernel x -
                ArctanGeometry.integralKernel y =
                -(ArctanGeometry.integralKernel y -
                  ArctanGeometry.integralKernel x) by grind [Rat.sub_eq_add_neg],
              qabs_neg]
            exact hkernelDiff)
      grind [Rat.sub_eq_add_neg]
    have hKy0 : 0 <= ArctanGeometry.integralKernel y :=
      Rat.le_of_lt (ArctanGeometry.integralKernel_pos y)
    have hKx0 : 0 <= ArctanGeometry.integralKernel x :=
      Rat.le_of_lt (ArctanGeometry.integralKernel_pos x)
    have hKy1 : ArctanGeometry.integralKernel y <= 1 :=
      ArctanGeometry.integralKernel_le_one y
    have hKx1 : ArctanGeometry.integralKernel x <= 1 :=
      ArctanGeometry.integralKernel_le_one x
    have hYproductToX : y * ArctanGeometry.integralKernel y <=
        x * ArctanGeometry.integralKernel x + 2 * k := by
      have hdiff : ArctanGeometry.integralKernel y -
          ArctanGeometry.integralKernel x <= 2 * k := by
        calc
          ArctanGeometry.integralKernel y -
              ArctanGeometry.integralKernel x <=
              qabs (ArctanGeometry.integralKernel y -
                ArctanGeometry.integralKernel x) := self_le_qabs _
          _ <= 2 * k := hkernelDiff
      have hscaled := Rat.mul_le_mul_of_nonneg_left hdiff hy.1
      have hyTwoK : y * (2 * k) <= 2 * k := by
        calc
          y * (2 * k) <= 1 * (2 * k) :=
            Rat.mul_le_mul_of_nonneg_right hy.2 (by grind)
          _ = 2 * k := by grind
      calc
        y * ArctanGeometry.integralKernel y =
            x * ArctanGeometry.integralKernel x +
              (y * (ArctanGeometry.integralKernel y -
                ArctanGeometry.integralKernel x) -
                k * ArctanGeometry.integralKernel x) := by
              dsimp [y, k]
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.mul_assoc, Rat.mul_comm]
        _ <= x * ArctanGeometry.integralKernel x +
            y * (ArctanGeometry.integralKernel y -
              ArctanGeometry.integralKernel x) := by
              have : 0 <= k * ArctanGeometry.integralKernel x :=
                Rat.mul_nonneg hk0 hKx0
              grind [Rat.sub_eq_add_neg]
        _ <= x * ArctanGeometry.integralKernel x + 2 * k :=
          (Rat.add_le_add_left).2 (Rat.le_trans hscaled hyTwoK)
    have hXproductToY : x * ArctanGeometry.integralKernel x <=
        y * ArctanGeometry.integralKernel y + 3 * k := by
      have hdiff : ArctanGeometry.integralKernel x -
          ArctanGeometry.integralKernel y <= 2 * k := by
        calc
          ArctanGeometry.integralKernel x -
              ArctanGeometry.integralKernel y <=
              qabs (ArctanGeometry.integralKernel x -
                ArctanGeometry.integralKernel y) := self_le_qabs _
          _ = qabs (ArctanGeometry.integralKernel y -
                ArctanGeometry.integralKernel x) := by
              rw [← qabs_neg]
              congr 1
              grind [Rat.sub_eq_add_neg]
          _ <= 2 * k := hkernelDiff
      have hscaled := Rat.mul_le_mul_of_nonneg_left hdiff hy.1
      have hyTwoK : y * (2 * k) <= 2 * k := by
        calc
          y * (2 * k) <= 1 * (2 * k) :=
            Rat.mul_le_mul_of_nonneg_right hy.2 (by grind)
          _ = 2 * k := by grind
      calc
        x * ArctanGeometry.integralKernel x =
            y * ArctanGeometry.integralKernel y +
              (y * (ArctanGeometry.integralKernel x -
                ArctanGeometry.integralKernel y) +
                k * ArctanGeometry.integralKernel x) := by
              dsimp [y, k]
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.mul_assoc, Rat.mul_comm]
        _ <= y * ArctanGeometry.integralKernel y +
            (y * (ArctanGeometry.integralKernel x -
              ArctanGeometry.integralKernel y) + k) := by
              have hKx : k * ArctanGeometry.integralKernel x <= k := by
                simpa using Rat.mul_le_mul_of_nonneg_left hKx1 hk0
              exact (Rat.add_le_add_left).2
                ((Rat.add_le_add_left).2
                  hKx)
        _ <= y * ArctanGeometry.integralKernel y + 3 * k := by
          apply (Rat.add_le_add_left).2
          calc
            y * (ArctanGeometry.integralKernel x -
                ArctanGeometry.integralKernel y) + k <= 2 * k + k :=
              (Rat.add_le_add_right).2 (Rat.le_trans hscaled hyTwoK)
            _ = 3 * k := by grind
    unfold intervalNearAtPrecision QInterval.NearAt at hproductNear harctanNear
    rcases hproductNear with ⟨hPlo, hPhi, hPwidth, hDYwidth⟩
    rcases harctanNear with ⟨hQlo, hQhi, _hQwidth, _⟩
    have hinv : 0 <= 1 / k := by
      rw [Rat.div_def]
      simpa using Rat.le_of_lt ((Rat.inv_pos).2 hkpos)
    have hcancel : k * (1 / k) = 1 := by
      simpa [Rat.div_def] using Rat.mul_inv_cancel k (Rat.ne_of_gt hkpos)
    have hQlo' : (1 / k) * (A.lo - B.hi) <=
        ArctanGeometry.integralKernel y + (precisionAtStage m).val := by
      simpa [QInterval.differenceQuotient, QInterval.divRat, QInterval.sub,
        QInterval.scaleRat, if_pos hinv] using hQlo
    have hQhi' : ArctanGeometry.integralKernel y <=
        (1 / k) * (A.hi - B.lo) + (precisionAtStage m).val := by
      simpa [QInterval.differenceQuotient, QInterval.divRat, QInterval.sub,
        QInterval.scaleRat, if_pos hinv] using hQhi
    have hAtoB : A.lo <= B.hi + k + k * (precisionAtStage m).val := by
      have hmult := Rat.mul_le_mul_of_nonneg_left hQlo' hk0
      have hdiff : A.lo - B.hi <=
          k * (ArctanGeometry.integralKernel y + (precisionAtStage m).val) := by
        calc
          A.lo - B.hi = k * ((1 / k) * (A.lo - B.hi)) := by
            rw [← Rat.mul_assoc, hcancel]
            grind
          _ <= k * (ArctanGeometry.integralKernel y +
              (precisionAtStage m).val) := hmult
      calc
        A.lo = B.hi + (A.lo - B.hi) := by grind [Rat.sub_eq_add_neg]
        _ <= B.hi + k * (ArctanGeometry.integralKernel y +
            (precisionAtStage m).val) := (Rat.add_le_add_left).2 hdiff
        _ = B.hi + k * ArctanGeometry.integralKernel y +
            k * (precisionAtStage m).val := by
              grind [Rat.mul_add, Rat.add_assoc]
        _ <= B.hi + k + k * (precisionAtStage m).val := by
          have hKy : k * ArctanGeometry.integralKernel y <= k := by
            simpa using Rat.mul_le_mul_of_nonneg_left hKy1 hk0
          apply (Rat.add_le_add_right).2
          exact (Rat.add_le_add_left).2
            hKy
    have hBtoA : B.lo <= A.hi + k * (precisionAtStage m).val := by
      have hnonneg : 0 <= (1 / k) * (A.hi - B.lo) +
          (precisionAtStage m).val :=
        Rat.le_trans hKy0 hQhi'
      have hscaled := Rat.mul_nonneg hk0 hnonneg
      have hdiff : 0 <= A.hi - B.lo + k * (precisionAtStage m).val := by
        calc
          0 <= k * ((1 / k) * (A.hi - B.lo) +
              (precisionAtStage m).val) := hscaled
          _ = A.hi - B.lo + k * (precisionAtStage m).val := by
            rw [Rat.mul_add, ← Rat.mul_assoc, hcancel]
            grind [Rat.sub_eq_add_neg]
      grind [Rat.sub_eq_add_neg]
    have hBwidth : B.width <= (precisionAtStage m).val := by
      have hBwidthFine : B.width <=
          k * (precisionAtStage t).val / 16 := by
        let eps : QPos :=
          { val := k * (precisionAtStage t).val / 16
            property := by
              rw [Rat.div_def]
              apply Rat.mul_pos
              · exact Rat.mul_pos hkpos (precisionAtStage t).property
              · exact (Rat.inv_pos).2 (by decide +kernel) }
        let M : Nat := 256 * (eps.val.den + 1)
        have hN : N = M := by
          dsimp [N, t]
          simp only [arctanRectangleTangentTransportPrecision, dif_pos hkpos]
          rfl
        have hMrect : 4 * (eps.val.den + 1) <= M := by
          dsimp [M]
          omega
        change (ArctanGeometry.arctanIntegralRectangleCompute y N).width <= _
        rw [hN]
        exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
          hy.1 hy.2 eps M hMrect
      calc
        B.width <= k * (precisionAtStage t).val / 16 := hBwidthFine
        _ <= (precisionAtStage t).val := by
          calc
            k * (precisionAtStage t).val / 16 =
                k * ((precisionAtStage t).val / 16) := by
                  grind [Rat.div_def]
            _ <= 1 * ((precisionAtStage t).val / 16) :=
              Rat.mul_le_mul_of_nonneg_right hkLeOne (by
                rw [Rat.div_def]
                exact Rat.mul_nonneg hptNonneg (by decide +kernel))
            _ = (precisionAtStage t).val / 16 := by grind
            _ <= (precisionAtStage t).val := by
              rw [Rat.div_def]
              grind
        _ <= (precisionAtStage m).val / 8 := hptLePm
        _ <= (precisionAtStage m).val := by
          grind [Rat.div_def]
    have hDyToDx : DY.hi <= DX.hi +
        ((precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k) := by
      change ((coordinateTimesArctanIntegralRectangleDerivativeRaw y hy).compute N).hi <=
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute N).hi +
          ((precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k)
      rw [coordinateTimesArctanIntegralRectangleDerivativeRaw_compute y hy N,
        coordinateTimesArctanIntegralRectangleDerivativeRaw_compute x hx N]
      have hBhi : B.hi <= A.hi + k * (precisionAtStage m).val +
          (precisionAtStage m).val := by
        calc
          B.hi <= B.lo + (precisionAtStage m).val := by
            unfold QInterval.width at hBwidth
            grind [Rat.sub_eq_add_neg]
          _ <= A.hi + k * (precisionAtStage m).val +
              (precisionAtStage m).val :=
            (Rat.add_le_add_right).2 hBtoA
      dsimp [A, B]
      calc
        (arctanIntegralRectangleOnUnit.compute y hy N).hi +
            y * ArctanGeometry.integralKernel y <=
            (arctanIntegralRectangleOnUnit.compute x hx N).hi +
              k * (precisionAtStage m).val +
              (precisionAtStage m).val +
              (x * ArctanGeometry.integralKernel x + 2 * k) := by
              exact rat_add_le_add hBhi hYproductToX
        _ = (arctanIntegralRectangleOnUnit.compute x hx N).hi +
            x * ArctanGeometry.integralKernel x +
              ((precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k) := by
              grind [Rat.add_assoc, Rat.add_comm]
    have hDxToDy : DX.lo <= DY.hi +
        (4 * k + k * (precisionAtStage m).val) := by
      change ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute N).lo <=
        ((coordinateTimesArctanIntegralRectangleDerivativeRaw y hy).compute N).hi +
          (4 * k + k * (precisionAtStage m).val)
      rw [coordinateTimesArctanIntegralRectangleDerivativeRaw_compute x hx N,
        coordinateTimesArctanIntegralRectangleDerivativeRaw_compute y hy N]
      dsimp [A, B] at hAtoB
      calc
        (arctanIntegralRectangleOnUnit.compute x hx N).lo +
            x * ArctanGeometry.integralKernel x <=
            ((arctanIntegralRectangleOnUnit.compute y hy N).hi + k +
              k * (precisionAtStage m).val) +
              (y * ArctanGeometry.integralKernel y + 3 * k) := by
              exact rat_add_le_add hAtoB hXproductToY
        _ = (arctanIntegralRectangleOnUnit.compute y hy N).hi +
            y * ArctanGeometry.integralKernel y +
              (4 * k + k * (precisionAtStage m).val) := by
              grind [Rat.add_assoc, Rat.add_comm]
    have hAwidthFine : A.width <=
        k * (precisionAtStage t).val / 16 := by
      let eps : QPos :=
        { val := k * (precisionAtStage t).val / 16
          property := by
            rw [Rat.div_def]
            apply Rat.mul_pos
            · exact Rat.mul_pos hkpos (precisionAtStage t).property
            · exact (Rat.inv_pos).2 (by decide +kernel) }
      let M : Nat := 256 * (eps.val.den + 1)
      have hN : N = M := by
        dsimp [N, t]
        simp only [arctanRectangleTangentTransportPrecision, dif_pos hkpos]
        rfl
      have hMrect : 4 * (eps.val.den + 1) <= M := by
        dsimp [M]
        omega
      change (arctanIntegralRectangleOnUnit.compute x hx N).width <= _
      rw [hN]
      exact ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
        hx.1 hx.2 eps M hMrect
    have hAwidth : A.width <= (precisionAtStage n).val := by
      calc
        A.width <= k * (precisionAtStage t).val / 16 := hAwidthFine
        _ <= (precisionAtStage t).val := by
          calc
            k * (precisionAtStage t).val / 16 =
                k * ((precisionAtStage t).val / 16) := by
                  grind [Rat.div_def]
            _ <= 1 * ((precisionAtStage t).val / 16) :=
              Rat.mul_le_mul_of_nonneg_right hkLeOne (by
                rw [Rat.div_def]
                exact Rat.mul_nonneg hptNonneg (by decide +kernel))
            _ = (precisionAtStage t).val / 16 := by grind
            _ <= (precisionAtStage t).val := by
              rw [Rat.div_def]
              grind
        _ <= (precisionAtStage m).val / 8 := hptLePm
        _ <= (precisionAtStage n).val := by
          calc
            (precisionAtStage m).val / 8 <=
                ((precisionAtStage n).val / 8) / 8 := by
                  exact Rat.mul_le_mul_of_nonneg_right hpmLePn (by decide +kernel)
            _ <= (precisionAtStage n).val := by
              grind [Rat.div_def]
    have hDXwidth : DX.width <= (precisionAtStage n).val := by
      change ((coordinateTimesArctanIntegralRectangleDerivativeRaw x hx).compute N).width <=
        (precisionAtStage n).val
      rw [coordinateTimesArctanIntegralRectangleDerivativeRaw_compute x hx N]
      calc
        ({ lo := (arctanIntegralRectangleOnUnit.compute x hx N).lo +
              x * ArctanGeometry.integralKernel x,
           hi := (arctanIntegralRectangleOnUnit.compute x hx N).hi +
              x * ArctanGeometry.integralKernel x } : QInterval).width =
            (arctanIntegralRectangleOnUnit.compute x hx N).width := by
              unfold QInterval.width
              grind [Rat.sub_eq_add_neg]
        _ <= (precisionAtStage n).val := by simpa [A] using hAwidth
    have hquotient :
        QInterval.differenceQuotient PY PX h =
          QInterval.differenceQuotient PX PY k := by
      have hhneg : h = -k := by
        dsimp [k]
        grind
      rw [hhneg]
      exact QInterval.differenceQuotient_reverse_of_pos (A := PX) (B := PY) hkpos
    change intervalNearAtPrecision
      (QInterval.differenceQuotient PY PX h) DX n
    rw [hquotient]
    unfold intervalNearAtPrecision QInterval.NearAt
    refine ⟨?_, ?_, Rat.le_trans hPwidth (by
      exact Rat.le_trans hpmLePn (by
        rw [Rat.div_def]
        grind)), hDXwidth⟩
    · calc
        (QInterval.differenceQuotient PX PY k).lo <=
            DY.hi + (precisionAtStage m).val := hPlo
        _ <= DX.hi +
            ((precisionAtStage m).val + k * (precisionAtStage m).val + 2 * k) +
              (precisionAtStage m).val :=
          (Rat.add_le_add_right).2 hDyToDx
        _ = DX.hi +
            (2 * (precisionAtStage m).val +
              k * (precisionAtStage m).val + 2 * k) := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ <= DX.hi + (precisionAtStage n).val :=
          (Rat.add_le_add_left).2 hleftBudget
    · calc
        DX.lo <= DY.hi + (4 * k + k * (precisionAtStage m).val) := hDxToDy
        _ <= DY.lo + (precisionAtStage m).val +
            (4 * k + k * (precisionAtStage m).val) := by
              unfold QInterval.width at hDYwidth
              exact (Rat.add_le_add_right).2 (by
                grind [Rat.sub_eq_add_neg])
        _ <= (QInterval.differenceQuotient PX PY k).hi +
            (precisionAtStage m).val +
              (precisionAtStage m).val + (4 * k + k * (precisionAtStage m).val) := by
              exact (Rat.add_le_add_right).2
                ((Rat.add_le_add_right).2 hPhi)
        _ = (QInterval.differenceQuotient PX PY k).hi +
            (2 * (precisionAtStage m).val + 4 * k +
              k * (precisionAtStage m).val) := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ <= (QInterval.differenceQuotient PX PY k).hi +
            (precisionAtStage n).val :=
          (Rat.add_le_add_left).2 hrightBudget

/-- The actual finite bounded-sum raw for the product FTC has a rational
width modulus.  Its boxes need not themselves be nested, which is why the
subsequent construction applies finite-prefix stabilization. -/
theorem coordinateTimesArctanForwardTwoStageRaw_widthsShrink :
    RealCompute.WidthsShrinkToZero
      coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  have hbound := coordinateTimesArctanForwardFTCRiemann_width_le (precisionAtStage n)
  have hdenPos : 0 < eps.val.den + 1 := Nat.succ_pos _
  have hnPos : 0 < n := Nat.lt_of_lt_of_le hdenPos hn
  have hprecision : (precisionAtStage n).val <=
      1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    rw [precisionAtStage, dif_neg (Nat.ne_of_gt hnPos)]
    exact FTC.one_div_nat_antitone hdenPos hnPos hn
  change (coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.compute n).width <= eps.val
  calc
    (coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.compute n).width <=
        (precisionAtStage n).val := by
      simpa [TwoStageCandidateDerivativeFTC.boundedIntegralRaw,
        TwoStageCandidateDerivativeFTC.boundedIntegralCompute,
        TwoStageCandidateDerivativeFTC.boundedIntegralInterval,
        coordinateTimesArctanForwardTwoStageFTC] using hbound
    _ <= 1 / (((eps.val.den + 1 : Nat) : Rat)) := hprecision
    _ <= eps.val := FTC.one_div_den_succ_le_of_pos eps.property

/-- The finite bounded-sum raw is equivalent to the independent rectangle
evaluator for arctangent at one.  At every stage its telescope contains an
endpoint box at its selected stage; that box overlaps the rectangle evaluator
at the requested stage by the primitive's validated nestedness. -/
theorem coordinateTimesArctanForwardTwoStageRaw_equiv_rectangleAtOne :
    coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  intro n
  let h := coordinateTimesArctanForwardTwoStageFTC
  let eps := precisionAtStage n
  let s := h.chooseEndpointStage eps
  have hcontains :
      QInterval.ContainsInterval
        ((h.choosePartition eps).boundIntegralSum (fun k hk => h.derivativeBound eps k hk))
        (endpointDifferenceInterval coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 s) := by
    apply RationalPartition.boundIntegralSum_contains_endpointDifference
      (P := h.choosePartition eps)
      (F := coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw)
      (prec := s) h.primitive_valid
    · intro i hi
      exact h.primitive_domain_on eps i hi
    · intro k hk
      simpa [RationalPartition.cell, s] using h.local_endpoint_contained eps k hk
  have hall := RealCompute.allStagesOverlap_refl
    ArctanGeometry.arctanIntegralRectangleRawAtOne
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid s n
  have hover := (RealCompute.compareAt_overlap_iff
    ArctanGeometry.arctanIntegralRectangleRawAtOne
    ArctanGeometry.arctanIntegralRectangleRawAtOne s n).1 hall
  apply (RealCompute.compareAt_overlap_iff
    coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw
    ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  change QInterval.Overlaps
    ((h.choosePartition eps).boundIntegralSum (fun k hk => h.derivativeBound eps k hk))
    (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n)
  have hscheduled :
      QInterval.Overlaps
        (endpointDifferenceInterval coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 s)
        (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n) := by
    change QInterval.Overlaps
      (endpointDifferenceCompute coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 s)
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n)
    rw [coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq]
    exact hover
  exact ⟨Rat.le_trans hcontains.1 hscheduled.1,
    Rat.le_trans hscheduled.2 hcontains.2⟩

/-- The public rational radius used to stabilize the finite bounded-sum FTC
raw.  The rectangle endpoint evaluator occurs only in the proof that this
radius covers the common value, never in the stabilized runtime evaluator. -/
def coordinateTimesArctanForwardTwoStageStabilizationRadius (n : Nat) : Rat :=
  4 / (((n + 1 : Nat) : Rat))

theorem coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_rectangleAtOne
    (n : Nat) :
    (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n).width <=
      coordinateTimesArctanForwardTwoStageStabilizationRadius n := by
  change (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).width <= _
  simpa [coordinateTimesArctanForwardTwoStageStabilizationRadius] using
    ArctanGeometry.arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n

theorem coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_endpointDifference
    (n : Nat) :
    ((endpointDifferenceRaw coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).compute n).width <=
      coordinateTimesArctanForwardTwoStageStabilizationRadius n := by
  change (endpointDifferenceCompute coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 n).width <= _
  rw [coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq]
  exact coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_rectangleAtOne n

theorem coordinateTimesArctanForwardTwoStageStabilizationRadius_shrinks :
    ShrinksToZero coordinateTimesArctanForwardTwoStageStabilizationRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 4)
  intro n
  exact Rat.le_refl

/-- A valid direct-only representative of the finite product FTC: at stage
`n` it intersects the widened bounded-sum boxes from stages `0` through `n`.
The primitive endpoint evaluator is proof-side support only. -/
def coordinateTimesArctanForwardTwoStageStabilizedRaw : RealCompute :=
  RealCompute.prefixStabilize coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw
    coordinateTimesArctanForwardTwoStageStabilizationRadius

theorem coordinateTimesArctanForwardTwoStageStabilizedRaw_valid :
    coordinateTimesArctanForwardTwoStageStabilizedRaw.Valid := by
  unfold coordinateTimesArctanForwardTwoStageStabilizedRaw
  exact RealCompute.prefixStabilize_valid
    coordinateTimesArctanForwardTwoStageRaw_widthsShrink
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    coordinateTimesArctanForwardTwoStageRaw_equiv_rectangleAtOne
    coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_rectangleAtOne
    coordinateTimesArctanForwardTwoStageStabilizationRadius_shrinks

theorem coordinateTimesArctanForwardTwoStageStabilizedRaw_equiv_rectangleAtOne :
    coordinateTimesArctanForwardTwoStageStabilizedRaw.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  unfold coordinateTimesArctanForwardTwoStageStabilizedRaw
  exact RealCompute.prefixStabilize_equiv_anchor
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    coordinateTimesArctanForwardTwoStageRaw_equiv_rectangleAtOne
    coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_rectangleAtOne

theorem coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_equiv_rectangleAtOne :
    (endpointDifferenceRaw coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (endpointDifferenceRaw coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid)
    ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  change QInterval.Overlaps
    (endpointDifferenceCompute coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1 n)
    (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n)
  rw [coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_compute_eq]
  have hordered := RealCompute.interval_order_of_valid
    ArctanGeometry.arctanIntegralRectangleRawAtOne
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid n
  exact ⟨hordered, hordered⟩

/-- The public integral construction for the positive product derivative,
computed by the stabilized finite bounded-sum evaluator. -/
def coordinateTimesArctanForwardTwoStageConstruction :
    Integral.CandidateConstructionFor coordinateTimesArctanIntegralRectangleDerivativeOnUnit :=
  Integral.constructionFor_of_twoStageCandidateDerivativeFTC_stabilized
    coordinateTimesArctanForwardTwoStageFTC
    coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid
    coordinateTimesArctanForwardTwoStageStabilizationRadius
    coordinateTimesArctanForwardTwoStageRaw_widthsShrink
    coordinateTimesArctanForwardTwoStageStabilizationRadius_covers_endpointDifference
    coordinateTimesArctanForwardTwoStageStabilizationRadius_shrinks

/-- The stabilized bounded-sum construction through the monotone integral
API. -/
def coordinateTimesArctanForwardTwoStageMonotoneConstruction :
    Integral.MonotoneCandidateConstructionFor
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit where
  monotone := coordinateTimesArctanIntegralRectangleDerivativeOnUnit_monotone
  construction := coordinateTimesArctanForwardTwoStageConstruction

/-- The public monotone integral raw computed from finite stabilized
derivative-bound sums. -/
def coordinateTimesArctanForwardTwoStageMonotoneIntegral : RealCompute :=
  Integral.monotoneCandidateValueFor coordinateTimesArctanIntegralRectangleDerivativeOnUnit
    coordinateTimesArctanForwardTwoStageMonotoneConstruction

theorem coordinateTimesArctanForwardTwoStageMonotoneIntegral_valid :
    coordinateTimesArctanForwardTwoStageMonotoneIntegral.Valid :=
  Integral.monotoneCandidateValueFor_valid
    coordinateTimesArctanIntegralRectangleDerivativeOnUnit
    coordinateTimesArctanForwardTwoStageMonotoneConstruction

/-- The primitive endpoint formula now follows from the actual stabilized
finite bounded-sum integral construction. -/
def coordinateTimesArctanForwardTwoStageMonotoneCandidateEndpointAgreement :
    Integral.MonotoneCandidateEndpointAgreementFor
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit
      coordinateTimesArctanIntegralRectangleOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := coordinateTimesArctanForwardTwoStageMonotoneConstruction
  endpoint_valid := coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid
  equivalent := by
    have hleft :
        (Integral.monotoneCandidateValueFor coordinateTimesArctanIntegralRectangleDerivativeOnUnit
          coordinateTimesArctanForwardTwoStageMonotoneConstruction).Valid :=
      Integral.monotoneCandidateValueFor_valid coordinateTimesArctanIntegralRectangleDerivativeOnUnit
        coordinateTimesArctanForwardTwoStageMonotoneConstruction
    have hrect : ArctanGeometry.arctanIntegralRectangleRawAtOne.Valid :=
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    have hendpoint :
        (endpointDifferenceRaw coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
          coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealCompute.Valid] using
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid
    have hleftrect :
        (Integral.monotoneCandidateValueFor coordinateTimesArctanIntegralRectangleDerivativeOnUnit
          coordinateTimesArctanForwardTwoStageMonotoneConstruction).Equiv
          ArctanGeometry.arctanIntegralRectangleRawAtOne := by
      change (coordinateTimesArctanForwardTwoStageFTC.boundedIntegralRaw.prefixStabilize
        coordinateTimesArctanForwardTwoStageStabilizationRadius).Equiv
        ArctanGeometry.arctanIntegralRectangleRawAtOne
      exact coordinateTimesArctanForwardTwoStageStabilizedRaw_equiv_rectangleAtOne
    exact RealCompute.equiv_trans hleft hrect hendpoint hleftrect
      (RealCompute.equiv_symm
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_equiv_rectangleAtOne)

/-- The stabilized bounded-sum identity through the ordinary definite
integral interface. -/
def coordinateTimesArctanForwardTwoStageCandidateEndpointAgreement :
    Integral.CandidateEndpointAgreementFor
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit
      coordinateTimesArctanIntegralRectangleOnUnit :=
  coordinateTimesArctanForwardTwoStageMonotoneCandidateEndpointAgreement.toCandidateEndpointAgreementFor

/-- The stabilized bounded-sum identity through the public finite-piece
monotone integral interface. -/
noncomputable def coordinateTimesArctanForwardTwoStageGeneralCandidateEndpointAgreement :
    Integral.GeneralCandidateEndpointAgreementFor
      coordinateTimesArctanIntegralRectangleDerivativeOnUnit
      coordinateTimesArctanIntegralRectangleOnUnit :=
  Integral.GeneralCandidateEndpointAgreementFor.ofMonotone
    coordinateTimesArctanForwardTwoStageMonotoneCandidateEndpointAgreement
    (by decide +kernel)

/-- The stabilized finite bounded-sum integral computes the geometric
arctangent at one. -/
theorem coordinateTimesArctanForwardTwoStageMonotoneIntegral_equiv_arctanGeom_one :
    coordinateTimesArctanForwardTwoStageMonotoneIntegral.Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) := by
  have hleft : coordinateTimesArctanForwardTwoStageMonotoneIntegral.Valid :=
    coordinateTimesArctanForwardTwoStageMonotoneIntegral_valid
  have hendpoint :
      (endpointDifferenceRaw coordinateTimesArctanIntegralRectangleOnUnit.toRealFunRaw 0 1
        coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_valid
  have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel)
  simpa [coordinateTimesArctanForwardTwoStageMonotoneIntegral] using
    RealCompute.equiv_trans hleft hendpoint hgeom
      coordinateTimesArctanForwardTwoStageMonotoneCandidateEndpointAgreement.equivalent
      coordinateTimesArctanIntegralRectangleOnUnit_endpointDifference_equiv_arctanGeom_one

/-- The customary fourfold normalization of the product FTC integral agrees
with four times the geometric arctangent at one.  The pi registry later
identifies that geometric raw with the certified circle-area presentation. -/
theorem four_coordinateTimesArctanForwardTwoStageMonotoneIntegral_equiv_four_arctanGeom_one :
    ((4 : Nat) * coordinateTimesArctanForwardTwoStageMonotoneIntegral : RealCompute).Equiv
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealCompute) :=
  RealCompute.natScale_equiv 4
    coordinateTimesArctanForwardTwoStageMonotoneIntegral_equiv_arctanGeom_one

/-- The certified positive product branch has right derivative zero at the
left endpoint.  The proof uses the exact finite quotient identity above,
not a global product rule. -/
def coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAtZero :
    HasForwardDerivativeAt coordinateTimesArctanIntegralRectangleOnUnit
      0 RealCompute.zero := by
  refine
    { x_mem := by
        change (0 : Rat) <= 0 /\ 0 <= 1
        exact ⟨Rat.le_refl, by decide +kernel⟩
      derivative_valid := by
        change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
        exact RealCompute.ofRat_valid (0 : Rat)
      stepPrecision := fun n => if n = 0 then 1 else n
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hprecision : h <= (precisionAtStage n).val := by
    change h <= 1 / (((if n = 0 then 1 else n : Nat) : Rat)) at hsmall
    by_cases hn : n = 0
    · subst n
      calc
        h <= 1 / (1 : Rat) := by
          simpa using hsmall
        _ = (precisionAtStage 0).val := by decide +kernel
    · simpa [precisionAtStage, hn] using hsmall
  have hzero : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper 0 := by
    change (0 : Rat) <= 0 /\ 0 <= 1
    exact ⟨Rat.le_refl, by decide +kernel⟩
  have hmemAtH : inDomainInterval coordinateTimesArctanIntegralRectangleOnUnit.lower
      coordinateTimesArctanIntegralRectangleOnUnit.upper h := by
    have hzero_add : (0 : Rat) + h = h := by grind
    rw [← hzero_add]
    exact hmem
  have hquotient :=
    coordinateTimesArctanIntegralRectangleOnUnit_zero_differenceQuotient_compute_eq
      h hpos hmemAtH hzero 0
  have hlower :
      0 <= (ArctanGeometry.arctanIntegralRectangleCompute h 0).lo :=
    ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative
      (Rat.le_of_lt hpos) 0
  have hupper :
      (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi <= h :=
    ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input
      (Rat.le_of_lt hpos) 0
  have hordered :
      (ArctanGeometry.arctanIntegralRectangleCompute h 0).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi := by
    have hwidth :=
      ArctanGeometry.arctanIntegralRectangleCompute_ordered
        (Rat.le_of_lt hpos) 0
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hnear : intervalNearAtPrecision
      (ArctanGeometry.arctanIntegralRectangleCompute h 0)
      { lo := 0, hi := 0 } n := by
    unfold intervalNearAtPrecision QInterval.NearAt
    constructor
    · calc
        (ArctanGeometry.arctanIntegralRectangleCompute h 0).lo <=
            (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi :=
          hordered
        _ <= h := hupper
        _ <= 0 + (precisionAtStage n).val := by
          grind
    constructor
    · have hupper_nonneg :
          0 <= (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi :=
        Rat.le_trans hlower hordered
      grind
    constructor
    · unfold QInterval.width
      calc
        (ArctanGeometry.arctanIntegralRectangleCompute h 0).hi -
            (ArctanGeometry.arctanIntegralRectangleCompute h 0).lo <= h := by
          grind [Rat.sub_eq_add_neg]
        _ <= (precisionAtStage n).val := hprecision
    · unfold QInterval.width
      rw [show (0 : Rat) - 0 = 0 by decide +kernel]
      exact Rat.le_of_lt (precisionAtStage n).property
  have hfromExact : intervalNearAtPrecision
      (QInterval.differenceQuotient
        (coordinateTimesArctanIntegralRectangleOnUnit.compute h hmemAtH 0)
        (coordinateTimesArctanIntegralRectangleOnUnit.compute 0 hzero 0) h)
      (RealCompute.zero.compute 0) n := by
    rw [hquotient]
    simpa [RealCompute.zero, RealCompute.ofRat_compute] using hnear
  have hzero_add : (0 : Rat) + h = h := by grind
  simpa [hzero_add] using hfromExact

/-- The fixed-stage arctangent boxes along a unit mesh, held at the final
mesh point after the last cell.  This produces a total box path suitable
for the finite integration-by-parts sums. -/
def arctanIntegralRectangleMeshBoxes
    (meshStage evalStage : Nat) : Nat -> QInterval :=
  fun k => ArctanGeometry.arctanIntegralRectangleCompute
    (unitMeshPath meshStage (min k meshStage)) evalStage

/-- The clamped unit-mesh points preserve index order. -/
theorem unitMeshPath_clamped_monotone
    (meshStage i j : Nat) (hij : i <= j) :
    unitMeshPath meshStage (min i meshStage) <=
      unitMeshPath meshStage (min j meshStage) := by
  apply unitMeshPath_monotone
  omega

/-- The arctangent rectangle boxes along a unit mesh are weakly ordered at
every fixed evaluation stage. -/
theorem arctanIntegralRectangleMeshBoxes_weaklyOrdered
    (meshStage evalStage : Nat) :
    QInterval.WeaklyOrdered
      (arctanIntegralRectangleMeshBoxes meshStage evalStage) := by
  intro i j hij
  unfold arctanIntegralRectangleMeshBoxes
  apply ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
  · exact unitMeshPath_nonnegative meshStage (min i meshStage)
  · exact unitMeshPath_clamped_monotone meshStage i j hij

/-- The rectangle width bound is uniform over all unit-mesh sample points. -/
theorem arctanIntegralRectangleMeshBoxes_width_le_eps
    (meshStage evalStage k : Nat) (eps : QPos)
    (heval : 4 * (eps.val.den + 1) <= evalStage) :
    (arctanIntegralRectangleMeshBoxes meshStage evalStage k).width <=
      eps.val := by
  unfold arctanIntegralRectangleMeshBoxes
  apply ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
  · exact unitMeshPath_nonnegative meshStage (min k meshStage)
  · exact unitMeshPath_le_one meshStage (min k meshStage)
      (Nat.min_le_right _ _)
  · exact heval

/-- The canonical nondecreasing rational arctangent sample path obtained
from the cumulative lower envelope of the fixed-stage mesh boxes. -/
def arctanIntegralRectangleMeshSamples
    (meshStage evalStage : Nat) : Nat -> Rat :=
  QInterval.lowerEnvelope
    (arctanIntegralRectangleMeshBoxes meshStage evalStage)

/-- Each canonical sample remains inside its corresponding rectangle box. -/
theorem arctanIntegralRectangleMeshSamples_mem
    (meshStage evalStage k : Nat) :
    And
      ((arctanIntegralRectangleMeshBoxes meshStage evalStage k).lo <=
        arctanIntegralRectangleMeshSamples meshStage evalStage k)
      (arctanIntegralRectangleMeshSamples meshStage evalStage k <=
        (arctanIntegralRectangleMeshBoxes meshStage evalStage k).hi) := by
  exact QInterval.lowerEnvelope_mem
    (arctanIntegralRectangleMeshBoxes meshStage evalStage)
    (arctanIntegralRectangleMeshBoxes_weaklyOrdered meshStage evalStage) k

/-- The selected sample is within the width of its own rectangle box above
the lower endpoint. -/
theorem arctanIntegralRectangleMeshSamples_sub_lower_le_boxWidth
    (meshStage evalStage k : Nat) :
    arctanIntegralRectangleMeshSamples meshStage evalStage k -
        (arctanIntegralRectangleMeshBoxes meshStage evalStage k).lo <=
      (arctanIntegralRectangleMeshBoxes meshStage evalStage k).width := by
  exact QInterval.point_sub_lower_le_width
    (arctanIntegralRectangleMeshSamples_mem meshStage evalStage k).2

/-- The selected sample is within the width of its own rectangle box below
the upper endpoint. -/
theorem arctanIntegralRectangleMeshSamples_upper_sub_le_boxWidth
    (meshStage evalStage k : Nat) :
    (arctanIntegralRectangleMeshBoxes meshStage evalStage k).hi -
        arctanIntegralRectangleMeshSamples meshStage evalStage k <=
      (arctanIntegralRectangleMeshBoxes meshStage evalStage k).width := by
  exact QInterval.upper_sub_point_le_width
    (arctanIntegralRectangleMeshSamples_mem meshStage evalStage k).1

/-- At the explicit evaluation precision, either endpoint of a sampled
rectangle box is within the requested rational error budget. -/
theorem arctanIntegralRectangleMeshSamples_sub_lower_le_eps
    (meshStage evalStage k : Nat) (eps : QPos)
    (heval : 4 * (eps.val.den + 1) <= evalStage) :
    arctanIntegralRectangleMeshSamples meshStage evalStage k -
        (arctanIntegralRectangleMeshBoxes meshStage evalStage k).lo <=
      eps.val :=
  Rat.le_trans
    (arctanIntegralRectangleMeshSamples_sub_lower_le_boxWidth
      meshStage evalStage k)
    (arctanIntegralRectangleMeshBoxes_width_le_eps
      meshStage evalStage k eps heval)

/-- At the explicit evaluation precision, the upper endpoint of a sampled
rectangle box is within the requested rational error budget of its sample. -/
theorem arctanIntegralRectangleMeshSamples_upper_sub_le_eps
    (meshStage evalStage k : Nat) (eps : QPos)
    (heval : 4 * (eps.val.den + 1) <= evalStage) :
    (arctanIntegralRectangleMeshBoxes meshStage evalStage k).hi -
        arctanIntegralRectangleMeshSamples meshStage evalStage k <=
      eps.val :=
  Rat.le_trans
    (arctanIntegralRectangleMeshSamples_upper_sub_le_boxWidth
      meshStage evalStage k)
    (arctanIntegralRectangleMeshBoxes_width_le_eps
      meshStage evalStage k eps heval)

/-- The canonical arctangent mesh sample path is nondecreasing. -/
theorem arctanIntegralRectangleMeshSamples_step_nonnegative
    (meshStage evalStage k : Nat) :
    0 <= arctanIntegralRectangleMeshSamples meshStage evalStage (k + 1) -
      arctanIntegralRectangleMeshSamples meshStage evalStage k := by
  exact QInterval.lowerEnvelope_step_nonnegative
    (arctanIntegralRectangleMeshBoxes meshStage evalStage) k

/-- The first lower-envelope sample is exactly zero because the rectangle
integral at the zero upper endpoint is exact. -/
theorem arctanIntegralRectangleMeshSamples_zero
    (meshStage evalStage : Nat) :
    arctanIntegralRectangleMeshSamples meshStage evalStage 0 = 0 := by
  unfold arctanIntegralRectangleMeshSamples QInterval.lowerEnvelope
    arctanIntegralRectangleMeshBoxes
  simp only [Nat.zero_min]
  have hpoint : unitMeshPath meshStage 0 = 0 := by
    unfold unitMeshPath
    rw [Rat.div_def]
    simp
  rw [hpoint]
  exact ArctanGeometry.arctanIntegralRectangleCompute_zero_lower evalStage

/-- The final unit-mesh sample is at most one. -/
theorem arctanIntegralRectangleMeshSamples_endpoint_le_one
    (meshStage evalStage : Nat) :
    arctanIntegralRectangleMeshSamples meshStage evalStage meshStage <= 1 := by
  have hmem := arctanIntegralRectangleMeshSamples_mem
    meshStage evalStage meshStage
  have hupper :
      (arctanIntegralRectangleMeshBoxes meshStage evalStage meshStage).hi <=
        unitMeshPath meshStage (min meshStage meshStage) := by
    unfold arctanIntegralRectangleMeshBoxes
    exact ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input
      (unitMeshPath_nonnegative meshStage (min meshStage meshStage)) evalStage
  calc
    arctanIntegralRectangleMeshSamples meshStage evalStage meshStage <=
        (arctanIntegralRectangleMeshBoxes meshStage evalStage meshStage).hi :=
      hmem.2
    _ <= unitMeshPath meshStage (min meshStage meshStage) := hupper
    _ <= 1 := unitMeshPath_le_one meshStage (min meshStage meshStage)
      (Nat.min_le_right _ _)

/-- The sampled arctangent endpoint variation is bounded by one. -/
theorem arctanIntegralRectangleMeshSamples_endpointDifference_le_one
    (meshStage evalStage : Nat) :
    arctanIntegralRectangleMeshSamples meshStage evalStage meshStage -
      arctanIntegralRectangleMeshSamples meshStage evalStage 0 <= 1 := by
  rw [arctanIntegralRectangleMeshSamples_zero meshStage evalStage]
  have h := arctanIntegralRectangleMeshSamples_endpoint_le_one
    meshStage evalStage
  grind [Rat.sub_eq_add_neg]

/-- The finite integration-by-parts corner correction now applies directly
to the canonical sampled arctangent path on every unit mesh. -/
theorem arctanIntegralRectangleMeshSamples_cornerBound
    (meshStage evalStage : Nat) :
    quadraticVariationSum (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage <=
      (1 / (meshStage : Rat)) *
        (arctanIntegralRectangleMeshSamples meshStage evalStage meshStage -
          arctanIntegralRectangleMeshSamples meshStage evalStage 0) :=
  unitMeshPath_quadraticVariation_le_one_div_mul_endpointDifference
    meshStage (arctanIntegralRectangleMeshSamples meshStage evalStage)
    (arctanIntegralRectangleMeshSamples_step_nonnegative meshStage evalStage)

/-- The arctangent corner correction is bounded by the reciprocal mesh size:
the sampled endpoint variation is at most one. -/
theorem arctanIntegralRectangleMeshSamples_cornerBound_le_one_div
    (meshStage evalStage : Nat) :
    quadraticVariationSum (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage <=
      1 / (meshStage : Rat) := by
  have hvariation :=
    arctanIntegralRectangleMeshSamples_endpointDifference_le_one
      meshStage evalStage
  have hfactor : 0 <= 1 / (meshStage : Rat) := by
    simpa [unitMeshPath] using unitMeshPath_nonnegative meshStage 1
  calc
    quadraticVariationSum (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage <=
        (1 / (meshStage : Rat)) *
          (arctanIntegralRectangleMeshSamples meshStage evalStage meshStage -
            arctanIntegralRectangleMeshSamples meshStage evalStage 0) :=
      arctanIntegralRectangleMeshSamples_cornerBound meshStage evalStage
    _ <= (1 / (meshStage : Rat)) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hvariation hfactor
    _ = 1 / (meshStage : Rat) := by
      rw [Rat.mul_one]

/-- The explicit unit-mesh stage `eps.den + 1` makes the arctangent corner
correction at most the requested positive rational epsilon. -/
theorem arctanIntegralRectangleMeshSamples_cornerBound_le_eps
    (evalStage : Nat) (eps : QPos) :
    quadraticVariationSum (unitMeshPath (eps.val.den + 1))
        (arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage)
        (eps.val.den + 1) <= eps.val := by
  calc
    quadraticVariationSum (unitMeshPath (eps.val.den + 1))
        (arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage)
        (eps.val.den + 1) <= 1 / (((eps.val.den + 1 : Nat) : Rat)) :=
      arctanIntegralRectangleMeshSamples_cornerBound_le_one_div
        (eps.val.den + 1) evalStage
    _ <= eps.val := FTC.one_div_den_succ_le_of_pos eps.property

/-- The two left-endpoint strip sums in the concrete unit-branch
integration-by-parts calculation.  The first is the finite approximation to
\(\int x\,d(\arctan x)\); the second is the complementary approximation to
\(\int\arctan x\,dx\). -/
def arctanIntegralRectangleMeshIntegrationByPartsSum
    (meshStage evalStage : Nat) : Rat :=
  leftStieltjesSum (unitMeshPath meshStage)
      (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage +
    leftStieltjesSum
      (arctanIntegralRectangleMeshSamples meshStage evalStage)
      (unitMeshPath meshStage) meshStage

/-- The certified unit-mesh arctangent samples satisfy the exact finite
integration-by-parts identity.  The only remaining term is the explicitly
named corner correction; this is a rational equality, not a limiting
argument or an invocation of FTC. -/
theorem arctanIntegralRectangleMeshIntegrationByParts_finite_identity
    (meshStage evalStage : Nat) (hmesh : 0 < meshStage) :
    arctanIntegralRectangleMeshIntegrationByPartsSum meshStage evalStage +
        quadraticVariationSum (unitMeshPath meshStage)
          (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage =
      arctanIntegralRectangleMeshSamples meshStage evalStage meshStage := by
  calc
    arctanIntegralRectangleMeshIntegrationByPartsSum meshStage evalStage +
        quadraticVariationSum (unitMeshPath meshStage)
          (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage =
        unitMeshPath meshStage meshStage *
            arctanIntegralRectangleMeshSamples meshStage evalStage meshStage -
          unitMeshPath meshStage 0 *
            arctanIntegralRectangleMeshSamples meshStage evalStage 0 :=
      finiteIntegrationByParts_withVariation
        (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage
    _ = arctanIntegralRectangleMeshSamples meshStage evalStage meshStage := by
      rw [unitMeshPath_endpoint hmesh, unitMeshPath_zero,
        arctanIntegralRectangleMeshSamples_zero]
      grind [Rat.sub_eq_add_neg]

/-- The concrete finite integration-by-parts sum is trapped between the
sampled arctangent endpoint and that endpoint minus the explicit mesh error
\(1/n\).  This is the exact error bridge needed before the two strip sums
are independently promoted to definite integrals. -/
theorem arctanIntegralRectangleMeshIntegrationByParts_endpoint_bracket
    (meshStage evalStage : Nat) (hmesh : 0 < meshStage) :
    arctanIntegralRectangleMeshSamples meshStage evalStage meshStage -
        1 / (meshStage : Rat) <=
      arctanIntegralRectangleMeshIntegrationByPartsSum meshStage evalStage /\
    arctanIntegralRectangleMeshIntegrationByPartsSum meshStage evalStage <=
      arctanIntegralRectangleMeshSamples meshStage evalStage meshStage := by
  have hidentity :=
    arctanIntegralRectangleMeshIntegrationByParts_finite_identity
      meshStage evalStage hmesh
  have hcorner_nonneg :
      0 <= quadraticVariationSum (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage :=
    quadraticVariationSum_nonneg_of_step_nonnegative
      (unitMeshPath meshStage)
      (arctanIntegralRectangleMeshSamples meshStage evalStage)
      (fun i => by
        rw [unitMeshPath_step, Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2
          ((Rat.natCast_pos).2 hmesh)))
      (arctanIntegralRectangleMeshSamples_step_nonnegative meshStage evalStage)
      meshStage
  have hcorner_le :
      quadraticVariationSum (unitMeshPath meshStage)
        (arctanIntegralRectangleMeshSamples meshStage evalStage) meshStage <=
        1 / (meshStage : Rat) :=
    arctanIntegralRectangleMeshSamples_cornerBound_le_one_div
      meshStage evalStage
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Choosing the denominator-plus-one mesh makes the same finite
integration-by-parts bracket fit any requested positive rational tolerance.
This supplies the mesh part of the later three-budget pi route. -/
theorem arctanIntegralRectangleMeshIntegrationByParts_endpoint_bracket_le_eps
    (evalStage : Nat) (eps : QPos) :
    arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage
        (eps.val.den + 1) - eps.val <=
      arctanIntegralRectangleMeshIntegrationByPartsSum
        (eps.val.den + 1) evalStage /\
    arctanIntegralRectangleMeshIntegrationByPartsSum
        (eps.val.den + 1) evalStage <=
      arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage
        (eps.val.den + 1) := by
  have hidentity :=
    arctanIntegralRectangleMeshIntegrationByParts_finite_identity
      (eps.val.den + 1) evalStage (Nat.succ_pos _)
  have hcorner_nonneg :
      0 <= quadraticVariationSum (unitMeshPath (eps.val.den + 1))
        (arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage)
        (eps.val.den + 1) :=
    quadraticVariationSum_nonneg_of_step_nonnegative
      (unitMeshPath (eps.val.den + 1))
      (arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage)
      (fun i => by
        rw [unitMeshPath_step, Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2
          ((Rat.natCast_pos).2 (Nat.succ_pos _))))
      (arctanIntegralRectangleMeshSamples_step_nonnegative
        (eps.val.den + 1) evalStage)
      (eps.val.den + 1)
  have hcorner_le :
      quadraticVariationSum (unitMeshPath (eps.val.den + 1))
        (arctanIntegralRectangleMeshSamples (eps.val.den + 1) evalStage)
        (eps.val.den + 1) <= eps.val :=
    arctanIntegralRectangleMeshSamples_cornerBound_le_eps evalStage eps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The direct interval emitted by the finite unit-mesh integration-by-parts
calculation.  Stage `n` uses an `(n + 1)`-cell mesh and arctangent rectangle
samples evaluated at stage `n`; the explicit `1 / (n + 1)` enlargement is
exactly the finite corner-error budget. -/
def arctanIntegrationByPartsMeshCandidateCompute (n : Nat) : QInterval :=
  let sum := arctanIntegralRectangleMeshIntegrationByPartsSum (n + 1) n
  QInterval.expand { lo := sum, hi := sum }
    (1 / (((n + 1 : Nat) : Rat)))

/-- The unnormalised direct raw evaluator behind the finite
integration-by-parts calculation.  It evaluates only rational mesh sums and
arctangent rectangle samples. -/
def arctanIntegrationByPartsMeshCandidate : RealCompute where
  compute := arctanIntegrationByPartsMeshCandidateCompute

theorem arctanIntegrationByPartsMeshCandidateCompute_width_eq (n : Nat) :
    (arctanIntegrationByPartsMeshCandidateCompute n).width =
      2 / (((n + 1 : Nat) : Rat)) := by
  unfold arctanIntegrationByPartsMeshCandidateCompute
  rw [QInterval.expand_width]
  simp only [QInterval.width]
  change (arctanIntegralRectangleMeshIntegrationByPartsSum (n + 1) n -
      arctanIntegralRectangleMeshIntegrationByPartsSum (n + 1) n) +
      2 * (1 / ((n + 1 : Nat) : Rat)) = _
  have hzero : arctanIntegralRectangleMeshIntegrationByPartsSum (n + 1) n -
      arctanIntegralRectangleMeshIntegrationByPartsSum (n + 1) n = 0 := by
    grind [Rat.sub_eq_add_neg]
  rw [hzero]
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The direct mesh interval has the public rational width modulus `2/(n+1)`.
No convergence principle is used: the proof is the denominator schedule from
`ShrinksToZero`. -/
theorem arctanIntegrationByPartsMeshCandidate_widthsShrink :
    RealCompute.WidthsShrinkToZero arctanIntegrationByPartsMeshCandidate.compute := by
  apply shrinksToZero_of_natOverSuccBound (C := 2)
  intro n
  rw [show arctanIntegrationByPartsMeshCandidate.compute n =
      arctanIntegrationByPartsMeshCandidateCompute n by rfl,
    arctanIntegrationByPartsMeshCandidateCompute_width_eq]
  change (2 : Rat) / (((n + 1 : Nat) : Rat)) <=
    (2 : Rat) / (((n + 1 : Nat) : Rat))
  exact Rat.le_refl

/-- At each common stage, the finite integration-by-parts candidate interval
overlaps the verified rectangle interval for arctangent at one.  The proof
uses the actual final mesh sample as the witness; it does not identify either
strip sum with a definite integral. -/
theorem arctanIntegrationByPartsMeshCandidate_overlaps_rectangleAtOne
    (n : Nat) :
    QInterval.Overlaps
      (arctanIntegrationByPartsMeshCandidate.compute n)
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n) := by
  have hbracket := arctanIntegralRectangleMeshIntegrationByParts_endpoint_bracket
    (n + 1) n (Nat.succ_pos _)
  have hsample := arctanIntegralRectangleMeshSamples_mem (n + 1) n (n + 1)
  have hendpoint : unitMeshPath (n + 1) (n + 1) = 1 :=
    unitMeshPath_endpoint (Nat.succ_pos _)
  have hsampleAtOne :
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n).lo <=
          arctanIntegralRectangleMeshSamples (n + 1) n (n + 1) /\
      arctanIntegralRectangleMeshSamples (n + 1) n (n + 1) <=
        (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n).hi := by
    simpa [ArctanGeometry.arctanIntegralRectangleRawAtOne,
      ArctanGeometry.arctanIntegralRectangleCompute,
      ArctanGeometry.arctanIntegralRectangleComputeAtOne,
      arctanIntegralRectangleMeshBoxes, Nat.min_self, hendpoint] using hsample
  unfold arctanIntegrationByPartsMeshCandidate
    arctanIntegrationByPartsMeshCandidateCompute
  dsimp only
  unfold QInterval.expand
  have hrecip_nonneg : 0 <= 1 / (((n + 1 : Nat) : Rat)) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (Nat.succ_pos n)))
  constructor
  · exact Rat.le_trans
      (Rat.le_trans (by grind [Rat.sub_eq_add_neg]) hbracket.2)
      hsampleAtOne.2
  · exact Rat.le_trans hsampleAtOne.1 (by
      grind [Rat.sub_eq_add_neg])

theorem arctanIntegrationByPartsMeshCandidate_equiv_rectangleAtOne :
    arctanIntegrationByPartsMeshCandidate.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    arctanIntegrationByPartsMeshCandidate
    ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  exact arctanIntegrationByPartsMeshCandidate_overlaps_rectangleAtOne n

/-- The public rational radius that stabilizes the direct finite-mesh
integration-by-parts evaluator.  Its proof-side cover comes from the existing
arctangent rectangle width theorem; evaluating the stabilized raw never reads
the rectangle evaluator. -/
def arctanIntegrationByPartsMeshStabilizationRadius (n : Nat) : Rat :=
  4 / (((n + 1 : Nat) : Rat))

theorem arctanIntegrationByPartsMeshStabilizationRadius_covers_rectangleAtOne
    (n : Nat) :
    (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n).width <=
      arctanIntegrationByPartsMeshStabilizationRadius n := by
  change (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).width <= _
  simpa [arctanIntegrationByPartsMeshStabilizationRadius] using
    ArctanGeometry.arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n

theorem arctanIntegrationByPartsMeshStabilizationRadius_shrinks :
    ShrinksToZero arctanIntegrationByPartsMeshStabilizationRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 4)
  intro n
  exact Rat.le_refl

/-- A valid direct-only representative of the finite arctangent
integration-by-parts calculation.  It intersects a finite prefix of widened
mesh intervals, using only the rational radius schedule at runtime.  The
rectangle computation is an anchor used solely in its correctness proof. -/
def arctanIntegrationByPartsMesh : RealCompute :=
  RealCompute.prefixStabilize arctanIntegrationByPartsMeshCandidate
    arctanIntegrationByPartsMeshStabilizationRadius

theorem arctanIntegrationByPartsMesh_valid :
    arctanIntegrationByPartsMesh.Valid := by
  unfold arctanIntegrationByPartsMesh
  exact RealCompute.prefixStabilize_valid
    arctanIntegrationByPartsMeshCandidate_widthsShrink
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    arctanIntegrationByPartsMeshCandidate_equiv_rectangleAtOne
    arctanIntegrationByPartsMeshStabilizationRadius_covers_rectangleAtOne
    arctanIntegrationByPartsMeshStabilizationRadius_shrinks

theorem arctanIntegrationByPartsMesh_equiv_rectangleAtOne :
    arctanIntegrationByPartsMesh.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  unfold arctanIntegrationByPartsMesh
  exact RealCompute.prefixStabilize_equiv_anchor
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    arctanIntegrationByPartsMeshCandidate_equiv_rectangleAtOne
    arctanIntegrationByPartsMeshStabilizationRadius_covers_rectangleAtOne

/-- Four times the stabilized finite integration-by-parts mesh evaluator.
This is a supplementary direct pi computation: it is deliberately not named
as the arctangent--logarithm integral formula, whose separate FTC and
canonical-logarithm bridges remain future work. -/
def piFromArctanIntegrationByPartsMesh : RealCompute :=
  (4 : Nat) * arctanIntegrationByPartsMesh

theorem piFromArctanIntegrationByPartsMesh_valid :
    piFromArctanIntegrationByPartsMesh.Valid := by
  unfold piFromArctanIntegrationByPartsMesh
  exact RealCompute.natScale_valid 4 arctanIntegrationByPartsMesh_valid

theorem arctanIntegralRectangleFunctionAgreement :
    Elementary.Arctan.Equivalent
      arctanIntegralRectangleRepresentation
      ArctanGeometry.representation := by
  intro x hx _hgeom
  change (arctanIntegralRectangleFor x hx.1 hx.2).Equiv
    (ArctanGeometry.arctanGeom x)
  exact arctanIntegralRectangleFor_equiv_arctanGeom x hx.1 hx.2

/-- The rectangle-integral arctangent as a monotone-integral partial function
on the rational unit branch. -/
def arctanIntegralRectangleMonotoneFunctionRaw : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx =>
    (arctanIntegralRectangleMonotoneFor x hx.1 hx.2).compute
  rate := fun x hx =>
    (arctanIntegralRectangleMonotoneFor x hx.1 hx.2).rate

def arctanIntegralRectangleMonotoneRepresentation :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.rectangle.monotone"
  raw := arctanIntegralRectangleMonotoneFunctionRaw

theorem arctanIntegralRectangleMonotoneFunctionRaw_valid :
    forall x h, RealCompute.ValidCompute
      (arctanIntegralRectangleMonotoneFunctionRaw.compute x h) := by
  intro x hx
  change RealCompute.ValidCompute
    ((arctanIntegralRectangleMonotoneFor x hx.1 hx.2).compute)
  exact arctanIntegralRectangleMonotoneFor_valid x hx.1 hx.2

theorem arctanIntegralRectangleMonotoneFunctionAgreement :
    Elementary.Arctan.Equivalent
      arctanIntegralRectangleMonotoneRepresentation
      ArctanGeometry.representation := by
  intro x hx _hgeom
  change (arctanIntegralRectangleMonotoneFor x hx.1 hx.2).Equiv
    (ArctanGeometry.arctanGeom x)
  exact arctanIntegralRectangleMonotoneFor_equiv_arctanGeom x hx.1 hx.2

/-- A unit-branch integral arctangent construction.  This is the domain-aware
version of the integral route currently proved by rectangle sums: it only asks
for integral constructions on inputs `0 <= x <= 1`. -/
def arctanIntegralUnit
    (x : Rat) (c : Integral.CandidateConstructionFor (arctanKernelInterval x)) :
    RealCompute :=
  Integral.candidateValueFor (arctanKernelInterval x) c

def ArctanIntegralUnitComputes
    (x : Rat) (_hx0 : 0 <= x) (_hx1 : x <= 1)
    (arctanBranch : RealCompute) : Prop :=
  Exists fun c : Integral.CandidateConstructionFor (arctanKernelInterval x) =>
    (arctanIntegralUnit x c).Equiv arctanBranch

structure ArctanIntegralUnitData where
  constructionAt :
    forall x, 0 <= x -> x <= 1 ->
      Integral.CandidateConstructionFor (arctanKernelInterval x)

def arctanIntegralUnitFunctionRaw
    (data : ArctanIntegralUnitData) : PartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x hx =>
    (arctanIntegralUnit x
      (data.constructionAt x hx.1 hx.2)).compute
  rate := fun x hx =>
    (arctanIntegralUnit x
      (data.constructionAt x hx.1 hx.2)).rate

def arctanIntegralUnitRepresentation
    (data : ArctanIntegralUnitData) :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral.unit"
  raw := arctanIntegralUnitFunctionRaw data

theorem arctanIntegralUnitFunctionRaw_valid
    (data : ArctanIntegralUnitData) :
    forall x h, RealCompute.ValidCompute
      ((arctanIntegralUnitFunctionRaw data).compute x h) := by
  intro x hx
  change RealCompute.ValidCompute
    ((arctanIntegralUnit x (data.constructionAt x hx.1 hx.2)).compute)
  exact Integral.candidateValueFor_valid (arctanKernelInterval x)
    (data.constructionAt x hx.1 hx.2)

def ArctanIntegralUnitGeomFunctionAgreement
    (data : ArctanIntegralUnitData) : Prop :=
  Elementary.Arctan.Equivalent
    (arctanIntegralUnitRepresentation data)
    ArctanGeometry.representation

theorem arctanIntegralUnit_equiv_arctanGeom_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data)
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (data.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  have hgeom : ArctanGeometry.representation.raw.definedAt x := by
    simp [ArctanGeometry.representation, ArctanGeometry.functionRaw]
  have h' := h x ⟨hx0, hx1⟩ hgeom
  change (arctanIntegralUnit x (data.constructionAt x hx0 hx1)).Equiv
    (ArctanGeometry.arctanGeom x) at h'
  exact h'

theorem arctanIntegralUnitComputes_arctanGeom_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data)
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨data.constructionAt x hx0 hx1,
    arctanIntegralUnit_equiv_arctanGeom_of_functionAgreement
      data h hx0 hx1⟩

theorem arctanIntegralUnitGeomAgreement_one_of_functionAgreement
    (data : ArctanIntegralUnitData)
    (h : ArctanIntegralUnitGeomFunctionAgreement data) :
    ArctanIntegralUnitComputes (1 : Rat)
      (by decide +kernel) (by decide +kernel)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralUnitComputes_arctanGeom_of_functionAgreement
    data h (1 : Rat) (by decide +kernel) (by decide +kernel)

/-- The rectangle construction supplies the verified unit-branch integral
arctangent data. -/
def arctanIntegralRectangleUnitData : ArctanIntegralUnitData where
  constructionAt := arctanIntegralRectangleConstruction

theorem arctanIntegralRectangleUnit_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralRectangleUnitData.constructionAt x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  change (arctanIntegralUnit x
      (arctanIntegralRectangleUnitData.constructionAt x hx0 hx1)).Equiv
    (ArctanGeometry.arctanGeom x)
  exact arctanIntegralRectangleFor_equiv_arctanGeom x hx0 hx1

theorem arctanIntegralRectangleUnitFunctionAgreement :
    ArctanIntegralUnitGeomFunctionAgreement
      arctanIntegralRectangleUnitData := by
  intro x hx _hgeom
  change (arctanIntegralUnit x
      (arctanIntegralRectangleUnitData.constructionAt x hx.1 hx.2)).Equiv
    (ArctanGeometry.arctanGeom x)
  exact arctanIntegralRectangleUnit_equiv_arctanGeom x hx.1 hx.2

theorem arctanIntegralRectangleUnitComputes
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨arctanIntegralRectangleUnitData.constructionAt x hx0 hx1,
    arctanIntegralRectangleUnit_equiv_arctanGeom x hx0 hx1⟩

theorem arctanIntegralRectangleUnitComputes_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by decide +kernel) (by decide +kernel)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralRectangleUnitComputes
    (1 : Rat) (by decide +kernel) (by decide +kernel)

/-- The rectangle construction supplies the same unit-branch integral
arctangent data through the monotone-integral interface. -/
def arctanIntegralRectangleMonotoneUnitData : ArctanIntegralUnitData where
  constructionAt := fun x hx0 hx1 =>
    (arctanIntegralRectangleMonotoneConstruction x hx0 hx1).construction

theorem arctanIntegralRectangleMonotoneUnit_equiv_arctanGeom
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralUnit x
      (arctanIntegralRectangleMonotoneUnitData.constructionAt
        x hx0 hx1)).Equiv
        (ArctanGeometry.arctanGeom x) := by
  simpa [arctanIntegralUnit, arctanIntegralRectangleMonotoneUnitData,
    arctanIntegralRectangleMonotoneFor,
    Integral.monotoneCandidateValueFor] using
    arctanIntegralRectangleMonotoneFor_equiv_arctanGeom x hx0 hx1

theorem arctanIntegralRectangleMonotoneUnitFunctionAgreement :
    ArctanIntegralUnitGeomFunctionAgreement
      arctanIntegralRectangleMonotoneUnitData := by
  intro x hx _hgeom
  change (arctanIntegralUnit x
      (arctanIntegralRectangleMonotoneUnitData.constructionAt x hx.1 hx.2)).Equiv
    (ArctanGeometry.arctanGeom x)
  exact arctanIntegralRectangleMonotoneUnit_equiv_arctanGeom x hx.1 hx.2

theorem arctanIntegralRectangleMonotoneUnitComputes
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    ArctanIntegralUnitComputes x hx0 hx1
      (ArctanGeometry.arctanGeom x) :=
  ⟨arctanIntegralRectangleMonotoneUnitData.constructionAt x hx0 hx1,
    arctanIntegralRectangleMonotoneUnit_equiv_arctanGeom x hx0 hx1⟩

theorem arctanIntegralRectangleMonotoneUnitComputes_one :
    ArctanIntegralUnitComputes (1 : Rat)
      (by decide +kernel) (by decide +kernel)
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  arctanIntegralRectangleMonotoneUnitComputes
    (1 : Rat) (by decide +kernel) (by decide +kernel)

def arctanGeomOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx => (ArctanGeometry.arctanGeom x).compute
    rate := fun x _hx => (ArctanGeometry.arctanGeom x).rate
  }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact ArctanGeometry.arctanGeom_valid_on_unit hx.1 hx.2

/-- Checked data for the first-quadrant inverse-arctangent step.

The forward branch is required to be the actual geometric arctangent on the
unit slope interval, and every normalized quarter-turn target is required to
be a valid, explicitly range-enclosed target for that branch.  The bisection
field is consequently an `InverseBisectionSearch`, not a pair of opaque
inverse-law propositions.  A concrete inhabitant still requires the pending
interval-regularity and effective-separation proofs for `arctanGeomOnUnit`.
-/
structure ArctanInverseBisection where
  branch : InvertibleFunctionOnInterval
  /-- The inverse branch may use a different stage schedule from the
  geometric arctangent.  Pointwise `FunctionOnInterval.Equivalent` is the
  intended link: the abstract branch stores the representation actually used
  by bisection, while the geometric raw remains the semantic anchor. -/
  branch_is_geometric :
    FunctionOnInterval.Equivalent branch.function arctanGeomOnUnit
  targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
    RationalCircle.GeometricTrig.firstQuadrantBranch t -> InRangeRaw branch
  targetAt_equiv_halfQuarterTurn :
    forall t ht, (targetAt t ht).value.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw t)
  bisectionAt : forall y : InRangeRaw branch,
    InverseBisectionSearch branch y

namespace ArctanInverseBisection

/-- The inverse evaluator obtained from the supplied certified bisection
searches. -/
def inverseRaw (B : ArctanInverseBisection) : InverseRaw B.branch :=
  inverseRawOfSearch B.bisectionAt

/-- The half-angle slope raw real at a normalized first-quadrant angle. -/
def tangentAt (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) : RealCompute :=
  (B.inverseRaw).apply (B.targetAt t ht)

/-- The first-quadrant half-angle slope function produced by the constructive
inverse theorem.  Its outputs are rational boxes for the slope in `[0,1]`;
the circle coordinates can therefore be evaluated from the rational
parametrization. -/
def tangentRaw (B : ArctanInverseBisection) : PartialRealFunRaw where
  definedAt := RationalCircle.GeometricTrig.firstQuadrantBranch
  compute := fun t ht => (B.tangentAt t ht).compute

theorem tangentAt_valid (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    (B.tangentAt t ht).Valid :=
  (B.inverseRaw).apply_valid (B.targetAt t ht)

theorem tangentRaw_valid (B : ArctanInverseBisection) :
    forall t ht, RealCompute.ValidCompute (B.tangentRaw.compute t ht) := by
  intro t ht
  change RealCompute.ValidCompute ((B.tangentAt t ht).compute)
  exact B.tangentAt_valid t ht

theorem tangentAt_stays_in_source (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    forall n, subintervalOf ((B.tangentAt t ht).compute n)
      B.branch.function.lower B.branch.function.upper :=
  (B.inverseRaw).apply_stays_in_source (B.targetAt t ht)

/-- The first-quadrant inverse output lies in the actual unit slope interval,
because its forward branch is certified equivalent to `arctanGeomOnUnit`. -/
theorem tangentAt_stays_in_unitSlope (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    forall n, subintervalOf ((B.tangentAt t ht).compute n) 0 1 := by
  have hsource := B.tangentAt_stays_in_source t ht
  have hlo : B.branch.function.lower = arctanGeomOnUnit.lower :=
    B.branch_is_geometric.1
  have hhi : B.branch.function.upper = arctanGeomOnUnit.upper :=
    B.branch_is_geometric.2.1
  simpa [arctanGeomOnUnit, hlo, hhi] using hsource

/-- The forward interval evaluator overlaps the certified target box at each
stage.  Together with `targetAt_equiv_halfQuarterTurn`, this is the computable
inverse law relating the recovered slope to the unit-sector area of the
requested quarter-turn angle. -/
theorem tangentAt_forward_overlaps_target
    (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    forall n, QInterval.Overlaps
      (B.branch.continuous.regular.evalInterval
        ((B.tangentAt t ht).compute n)
        (B.tangentAt_stays_in_source t ht n) n)
      ((B.targetAt t ht).value.compute n) :=
  (B.inverseRaw).apply_value_overlaps_target (B.targetAt t ht)

theorem targetAt_halfQuarterTurn_equiv
    (B : ArctanInverseBisection)
    (t : RationalCircle.GeometricTrig.QuarterTurn)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    (B.targetAt t ht).value.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw t) :=
  B.targetAt_equiv_halfQuarterTurn t ht

/-- Differences of inverse targets retain their geometric sector meaning.
This is the finite angle-increment interface used by the computable sine
secant estimates; it keeps the angle as a sector-area `RealCompute`, rather than
introducing an ambient real argument. -/
theorem targetAt_difference_equiv_halfQuarterTurn_difference
    (B : ArctanInverseBisection)
    {s t : RationalCircle.GeometricTrig.QuarterTurn}
    (hs : RationalCircle.GeometricTrig.firstQuadrantBranch s)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t) :
    ((B.targetAt s hs).value - (B.targetAt t ht).value).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw s -
        RationalCircle.GeometricTrig.halfQuarterTurnRaw t) := by
  have hpi : piCircleArea.Valid := by
    change RealCompute.ValidCompute piCircleArea.compute
    have hcompute : piCircleArea.compute =
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealCompute).compute := by
      funext n
      exact (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm
    rw [hcompute]
    exact ArctanGeometry.four_arctanGeom_one_valid
  have hsvalid :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw s).Valid := by
    apply RealCompute.scaleRat_valid_of_nonneg
    · change 0 <= s / 4
      rw [Rat.div_def]
      exact Rat.mul_nonneg hs.1 (by decide +kernel)
    · exact hpi
  have htvalid :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw t).Valid := by
    apply RealCompute.scaleRat_valid_of_nonneg
    · change 0 <= t / 4
      rw [Rat.div_def]
      exact Rat.mul_nonneg ht.1 (by decide +kernel)
    · exact hpi
  exact RealCompute.sub_equiv
    (B.targetAt s hs).value_valid hsvalid
    (B.targetAt t ht).value_valid htvalid
    (B.targetAt_halfQuarterTurn_equiv s hs)
    (B.targetAt_halfQuarterTurn_equiv t ht)

end ArctanInverseBisection

/-- Expose the inverse tangent evaluator on its normalized quarter-turn
interval.  This is the function-level interface consumed by the project's
effective-modulus and interval-regularity APIs; it does not assert continuity
by itself. -/
def tangentOnUnit (B : ArctanInverseBisection) : FunctionOnInterval where
  raw := {
    definedAt := RationalCircle.GeometricTrig.unitIntervalBranch
    compute := fun t ht => B.tangentRaw.compute t ht
  }
  lower := 0
  upper := 1
  defined_on := by
    intro _ ht
    exact ht
  valid_on := by
    intro t ht
    exact B.tangentRaw_valid t ht

theorem tangentOnUnit_valid (B : ArctanInverseBisection) :
    forall t ht,
      RealCompute.ValidCompute ((tangentOnUnit B).compute t ht) := by
  intro t ht
  exact B.tangentRaw_valid t ht

theorem arctanGeomOnUnit_toRealFunRaw_compute_zero (n : Nat) :
    arctanGeomOnUnit.toRealFunRaw.compute 0 n =
      (ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    arctanGeomOnUnit (x := 0)
      (hx := ⟨by decide +kernel, by decide +kernel⟩) n]
  rfl

theorem arctanGeomOnUnit_toRealFunRaw_compute_one (n : Nat) :
    arctanGeomOnUnit.toRealFunRaw.compute 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat)).compute n := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    arctanGeomOnUnit (x := 1)
      (hx := ⟨by decide +kernel, by decide +kernel⟩) n]
  rfl

theorem arctanGeomOnUnit_endpointDifference_compute_eq (n : Nat) :
    endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  unfold endpointDifferenceCompute endpointDifferenceInterval
  rw [arctanGeomOnUnit_toRealFunRaw_compute_one n,
    arctanGeomOnUnit_toRealFunRaw_compute_zero n]
  rfl

theorem arctanGeomOnUnit_endpointDifference_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1) := by
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealCompute.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by decide +kernel) (by decide +kernel))
  have hcompute :
      endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 =
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)).compute := by
    funext n
    exact arctanGeomOnUnit_endpointDifference_compute_eq n
  rw [hcompute]
  exact hsub

theorem arctanGeomOnUnit_endpointDifference_equiv_sub :
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid)
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) n n).2
  change QInterval.Overlaps
    (endpointDifferenceCompute arctanGeomOnUnit.toRealFunRaw 0 1 n)
    ((ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).compute n)
  rw [arctanGeomOnUnit_endpointDifference_compute_eq n]
  have hvalid :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealCompute.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by decide +kernel) (by decide +kernel))
  have horder := RealCompute.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) hvalid n
  exact ⟨horder, horder⟩

theorem arctanGeom_one_sub_zero_equiv :
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
  rw [ArctanGeometry.arctanGeom_zero]
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (ArctanGeometry.arctanGeom (1 : Rat) - RealCompute.ofRat 0)
    (ArctanGeometry.arctanGeom (1 : Rat)) n n).2
  change QInterval.Overlaps
    { lo := ((ArctanGeometry.arctanGeom (1 : Rat)).compute n).lo - 0,
      hi := ((ArctanGeometry.arctanGeom (1 : Rat)).compute n).hi - 0 }
    ((ArctanGeometry.arctanGeom (1 : Rat)).compute n)
  have horder := RealCompute.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat))
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel)) n
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one :
    (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
      arctanGeomOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
  have hendpoint :
      (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
        arctanGeomOnUnit_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using
      arctanGeomOnUnit_endpointDifference_valid
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealCompute.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by decide +kernel) (by decide +kernel))
  exact RealCompute.equiv_trans
    hendpoint
    hsub
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel))
    arctanGeomOnUnit_endpointDifference_equiv_sub
    arctanGeom_one_sub_zero_equiv

/-- The verified rectangle-sum construction for
`∫_0^1 dt / (1 + t^2)`, packaged as a `CandidateConstructionFor` on the arctangent
kernel interval. -/
def arctanIntegralRectangleConstructionAtOne :
    Integral.CandidateConstructionFor arctanKernelIntervalAtOne where
  compute := ArctanGeometry.arctanIntegralRectangleComputeAtOne
  certificate := by
    change RealCompute.ValidCompute
      ArctanGeometry.arctanIntegralRectangleComputeAtOne
    exact ArctanGeometry.arctanIntegralRectangleRawAtOne_valid

/-- The domain-aware integral raw real supplied by the rectangle construction
for the arctangent kernel on `[0, 1]`. -/
def arctanIntegralRectangleForAtOne : RealCompute :=
  Integral.candidateValueFor arctanKernelIntervalAtOne
    arctanIntegralRectangleConstructionAtOne

theorem arctanIntegralRectangleForAtOne_valid :
    arctanIntegralRectangleForAtOne.Valid :=
  Integral.candidateValueFor_valid arctanKernelIntervalAtOne
    arctanIntegralRectangleConstructionAtOne

theorem arctanIntegralRectangleForAtOne_compute_eq (n : Nat) :
    arctanIntegralRectangleForAtOne.compute n =
      ArctanGeometry.arctanIntegralRectangleComputeAtOne n := rfl

/-- The unit-branch rectangle evaluator has the explicit rational mesh
width bound used by the pi-level integral and Cauchy presentations. -/
theorem arctanIntegralRectangleForAtOne_width_le_four_div_succ (n : Nat) :
    (arctanIntegralRectangleForAtOne.compute n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) := by
  rw [arctanIntegralRectangleForAtOne_compute_eq]
  exact ArctanGeometry.arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n

theorem arctanIntegralRectangleForAtOne_equiv_raw :
    arctanIntegralRectangleForAtOne.Equiv
      ArctanGeometry.arctanIntegralRectangleRawAtOne := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    arctanIntegralRectangleForAtOne
    ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleComputeAtOne_ordered n
  have hle :
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo <=
        (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
  exact ⟨hle, hle⟩

/-- The arctangent kernel is nonincreasing on the unit interval. -/
def arctanKernelIntervalAtOne_monotone :
    MonotoneOnInterval arctanKernelIntervalAtOne :=
  arctanKernelInterval_monotone 1

/-- The rectangle construction for `∫_0^1 dx/(1+x^2)` as a monotone integral. -/
def arctanIntegralRectangleMonotoneConstructionAtOne :
    Integral.MonotoneCandidateConstructionFor arctanKernelIntervalAtOne where
  monotone := arctanKernelIntervalAtOne_monotone
  construction := arctanIntegralRectangleConstructionAtOne

/-- The monotone-integral packaging of the rectangle arctangent computation. -/
def arctanIntegralRectangleMonotoneForAtOne : RealCompute :=
  Integral.monotoneCandidateValueFor arctanKernelIntervalAtOne
    arctanIntegralRectangleMonotoneConstructionAtOne

theorem arctanIntegralRectangleMonotoneForAtOne_valid :
    arctanIntegralRectangleMonotoneForAtOne.Valid :=
  Integral.monotoneCandidateValueFor_valid arctanKernelIntervalAtOne
    arctanIntegralRectangleMonotoneConstructionAtOne

theorem arctanIntegralRectangleMonotoneForAtOne_compute_eq (n : Nat) :
    arctanIntegralRectangleMonotoneForAtOne.compute n =
      arctanIntegralRectangleForAtOne.compute n := by
  change arctanIntegralRectangleForAtOne.compute n =
    arctanIntegralRectangleForAtOne.compute n
  rfl

theorem arctanIntegralRectangleMonotoneForAtOne_equiv_rectangleForAtOne :
    arctanIntegralRectangleMonotoneForAtOne.Equiv
      arctanIntegralRectangleForAtOne :=
  by
    change arctanIntegralRectangleForAtOne.Equiv
      arctanIntegralRectangleForAtOne
    exact RealCompute.equiv_refl arctanIntegralRectangleForAtOne
      arctanIntegralRectangleForAtOne_valid

theorem arctanIntegralRectangleForAtOne_equiv_arctanGeom_one :
    arctanIntegralRectangleForAtOne.Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
  by
    intro n
    apply (RealCompute.compareAt_overlap_iff
      arctanIntegralRectangleForAtOne
      (ArctanGeometry.arctanGeom (1 : Rat)) n n).2
    have hover := (RealCompute.compareAt_overlap_iff
      ArctanGeometry.arctanIntegralRectangleRawAtOne
      (ArctanGeometry.arctanGeom (1 : Rat)) n n).1
        (ArctanGeometry.arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one n)
    simpa [arctanIntegralRectangleForAtOne, Integral.candidateValueFor,
      arctanIntegralRectangleConstructionAtOne,
      ArctanGeometry.arctanIntegralRectangleRawAtOne] using hover

/-- Rectangle-sum unit arctangent as a definite-integral identity: the
verified midpoint construction of `∫_0^1 dx/(1+x^2)` computes the endpoint
difference of the geometric arctangent primitive. -/
def arctanGeomUnitRectangleCandidateEndpointAgreement :
    Integral.CandidateEndpointAgreementFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := arctanIntegralRectangleConstructionAtOne
  endpoint_valid := arctanGeomOnUnit_endpointDifference_valid
  equivalent := by
    have hleft : arctanIntegralRectangleForAtOne.Valid :=
      arctanIntegralRectangleForAtOne_valid
    have hmid : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
      ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel)
    have hright :
        (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
          arctanGeomOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealCompute.Valid] using
        arctanGeomOnUnit_endpointDifference_valid
    change (Integral.candidateValueFor arctanKernelIntervalAtOne
      arctanIntegralRectangleConstructionAtOne).Equiv
      (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
        arctanGeomOnUnit_endpointDifference_valid)
    exact RealCompute.equiv_trans hleft hmid hright
      arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
      (RealCompute.equiv_symm
        arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one)

/-- The same unit arctangent endpoint identity, but with the integral side
explicitly packaged as a monotone integral for the decreasing kernel. -/
def arctanGeomUnitRectangleMonotoneCandidateEndpointAgreement :
    Integral.MonotoneCandidateEndpointAgreementFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit where
  same_lower := rfl
  same_upper := rfl
  construction := arctanIntegralRectangleMonotoneConstructionAtOne
  endpoint_valid := arctanGeomOnUnit_endpointDifference_valid
  equivalent := by
    have hleft : arctanIntegralRectangleMonotoneForAtOne.Valid :=
      arctanIntegralRectangleMonotoneForAtOne_valid
    have hrect : arctanIntegralRectangleForAtOne.Valid :=
      arctanIntegralRectangleForAtOne_valid
    have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
      ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel)
    have hendpoint :
        (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
          arctanGeomOnUnit_endpointDifference_valid).Valid := by
      simpa [endpointDifferenceRaw, RealCompute.Valid] using
        arctanGeomOnUnit_endpointDifference_valid
    have hmonoGeom :
        arctanIntegralRectangleMonotoneForAtOne.Equiv
          (ArctanGeometry.arctanGeom (1 : Rat)) :=
      RealCompute.equiv_trans hleft hrect hgeom
        arctanIntegralRectangleMonotoneForAtOne_equiv_rectangleForAtOne
        arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
    change (Integral.candidateValueFor arctanKernelIntervalAtOne
      arctanIntegralRectangleMonotoneConstructionAtOne.construction).Equiv
      (endpointDifferenceRaw arctanGeomOnUnit.toRealFunRaw 0 1
        arctanGeomOnUnit_endpointDifference_valid)
    exact RealCompute.equiv_trans hleft hgeom hendpoint
      hmonoGeom
      (RealCompute.equiv_symm
        arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one)

/-- The monotone rectangle endpoint identity, forgetting the monotonicity
certificate and viewed through the ordinary `CandidateEndpointAgreementFor` interface. -/
def arctanGeomUnitRectangleMonotoneCandidateEndpointAgreementFor :
    Integral.CandidateEndpointAgreementFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  arctanGeomUnitRectangleMonotoneCandidateEndpointAgreement.toCandidateEndpointAgreementFor

/-- The same unit arctangent endpoint identity, now viewed through the public
piecewise-monotone/general integral interface. -/
noncomputable def arctanGeomUnitRectangleGeneralCandidateEndpointAgreement :
    Integral.GeneralCandidateEndpointAgreementFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  Integral.GeneralCandidateEndpointAgreementFor.ofMonotone
    arctanGeomUnitRectangleMonotoneCandidateEndpointAgreement
    (by decide +kernel)

/-- The construction-transport version of the monotone rectangle endpoint
identity.  This is a small sanity check for the generic transport lemma:
changing the construction by an equivalent integral preserves the endpoint
identity. -/
def arctanGeomUnitRectangleMonotoneTransportedCandidateEndpointAgreement :
    Integral.CandidateEndpointAgreementFor
      (oneOverOnePlusSquareOnInterval 0 1) arctanGeomOnUnit :=
  Integral.CandidateEndpointAgreementFor.transportConstruction
    arctanGeomUnitRectangleCandidateEndpointAgreement
    arctanIntegralRectangleMonotoneConstructionAtOne.construction
    (by
      change arctanIntegralRectangleForAtOne.Equiv
        arctanIntegralRectangleForAtOne
      exact RealCompute.equiv_refl arctanIntegralRectangleForAtOne
        arctanIntegralRectangleForAtOne_valid)

/-- The ordinary and monotone rectangle endpoint identities have equivalent
integral raw reals. -/
theorem arctanGeomUnitRectangleMonotoneCandidateEndpointAgreement_equiv_rectangle :
    (Integral.candidateValueFor
      (oneOverOnePlusSquareOnInterval 0 1)
      arctanGeomUnitRectangleMonotoneCandidateEndpointAgreementFor.construction).Equiv
      (Integral.candidateValueFor
        (oneOverOnePlusSquareOnInterval 0 1)
        arctanGeomUnitRectangleCandidateEndpointAgreement.construction) :=
  Integral.CandidateEndpointAgreementFor.integral_equiv_integral
    arctanGeomUnitRectangleMonotoneCandidateEndpointAgreementFor
    arctanGeomUnitRectangleCandidateEndpointAgreement

/-- The theorem target for the integral arctangent comparison on `[0, x]`.
It says that the integral of `1 / (1 + t^2)` computes the chosen arctangent
branch. -/
abbrev ArctanIntegralConstruction (x : Rat) :=
  Integral.SampleConstruction
    (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw 0 x

def arctanIntegral (x : Rat)
    (c : ArctanIntegralConstruction x) : RealCompute :=
  Integral.sampleValue
    (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw 0 x c

theorem arctanIntegral_valid (x : Rat)
    (c : ArctanIntegralConstruction x) :
    (arctanIntegral x c).Valid :=
  by
    simpa [arctanIntegral] using FTC.integral_valid_of_construction c

/-- The legacy `Integral.SampleConstruction` wrapper uses exact point evaluations of
`1/(1+x^2)`.  Hence every scheduled left-Riemann sum is a point interval. -/
theorem arctanIntegral_compute_width_zero (x : Rat)
    (c : ArctanIntegralConstruction x) (n : Nat) :
    ((arctanIntegral x c).compute n).width = 0 := by
  simpa [arctanIntegral, Integral.sampleValue, Integral.Certificate.realCompute,
    Integral.Raw.toRealCompute, Integral.Raw.compute, Integral.algorithm] using
    riemannLeftInterval_point_width_zero
      (oneOverOnePlusSquareOnInterval 0 x).toRealFunRaw
      0 x (c.plan n).subdivisions (c.plan n).evalPrecision
      (fun y =>
        oneOverOnePlusSquareOnInterval_toRealFunRaw_point
          0 x y (c.plan n).evalPrecision)

/-- Consequently, a valid old-style `arctanIntegral` construction has no
stage-to-stage refinement: all of its intervals are equal.  This records why
the newer `CandidateConstructionFor` interface is the meaningful arctangent-integral
route in the scoreboard. -/
theorem arctanIntegral_stages_constant (x : Rat)
    (c : ArctanIntegralConstruction x) (n m : Nat) :
    (arctanIntegral x c).compute n =
      (arctanIntegral x c).compute m :=
  RealCompute.stage_eq_of_valid_zero_width
    (arctanIntegral x c)
    (arctanIntegral_valid x c)
    (arctanIntegral_compute_width_zero x c)
    n m

def ArctanIntegralComputes (x : Rat) (arctanBranch : RealCompute) : Prop :=
  Exists fun c : ArctanIntegralConstruction x =>
    (arctanIntegral x c).Equiv arctanBranch

/-- Pointwise version of the integral/geometric arctangent comparison.  The
function-level statement below is the preferred interface; this pointwise form
is useful for pi at `x = 1`. -/
def ArctanIntegralGeomAgreement (x : Rat) : Prop :=
  ArctanIntegralComputes x (ArctanGeometry.arctanGeom x)

/-- A choice of integral construction for each nonnegative rational input.

The current definite-integral wrapper is oriented from `0` to `x`, so this
first integral-arctangent representation is naturally defined on `0 <= x`.
The overlap convention then compares it with total geometric arctangent exactly
on the nonnegative rationals. -/
structure ArctanIntegralData where
  constructionAt : forall x, 0 <= x -> ArctanIntegralConstruction x

def arctanIntegralFunctionRaw
    (data : ArctanIntegralData) : PartialRealFunRaw where
  definedAt := fun x => 0 <= x
  compute := fun x hx => (arctanIntegral x (data.constructionAt x hx)).compute
  rate := fun x hx => (arctanIntegral x (data.constructionAt x hx)).rate

def arctanIntegralRepresentation
    (data : ArctanIntegralData) :
    Elementary.Arctan.FunctionRepresentation where
  name := "arctan.integral"
  raw := arctanIntegralFunctionRaw data

def ArctanIntegralGeomFunctionAgreement
    (data : ArctanIntegralData) : Prop :=
  Elementary.Arctan.Equivalent
    (arctanIntegralRepresentation data)
    ArctanGeometry.representation

theorem arctanIntegral_equiv_arctanGeom_of_functionAgreement
    (data : ArctanIntegralData)
    (h : ArctanIntegralGeomFunctionAgreement data)
    {x : Rat} (hx : 0 <= x) :
    (arctanIntegral x (data.constructionAt x hx)).Equiv
      (ArctanGeometry.arctanGeom x) := by
  have hgeom : ArctanGeometry.representation.raw.definedAt x := by
    simp [ArctanGeometry.representation, ArctanGeometry.functionRaw]
  have h' := h x hx hgeom
  change (arctanIntegral x (data.constructionAt x hx)).Equiv
    (ArctanGeometry.arctanGeom x) at h'
  exact h'

theorem arctanIntegralGeomAgreement_one_of_functionAgreement
    (data : ArctanIntegralData)
    (h : ArctanIntegralGeomFunctionAgreement data) :
    ArctanIntegralGeomAgreement (1 : Rat) := by
  exact ⟨data.constructionAt (1 : Rat) (by decide +kernel),
    arctanIntegral_equiv_arctanGeom_of_functionAgreement
      data h (by decide +kernel)⟩

/-- A resulting pi computation from the integral arctangent at `1`. -/
def PiFromArctanIntegral (arctanAtOne : RealCompute) : RealCompute :=
  RealCompute.scaleRat 4 arctanAtOne

/-- The geometric-pi comparison target for the integral arctangent computation. -/
def PiFromArctanIntegralAgrees (arctanAtOne : RealCompute) : Prop :=
  (PiFromArctanIntegral arctanAtOne).Equiv piCircleArea

/-- The integral-arctangent route to geometric pi, isolated into the two
mathematical bridges that still need estimates: first show the integral kernel
computes the geometric arctangent at `1`, then identify `4 * arctanGeom 1`
with the geometric area definition of pi. -/
structure ArctanIntegralPiRoute where
  integral_computes_geom_at_one :
    ArctanIntegralComputes 1 (ArctanGeometry.arctanGeom 1)
  four_geom_arctan_one_eq_pi :
    PiFromArctanIntegralAgrees (ArctanGeometry.arctanGeom 1)

namespace ArctanIntegralPiRoute

theorem pi_agrees (R : ArctanIntegralPiRoute) :
    PiFromArctanIntegralAgrees (ArctanGeometry.arctanGeom 1) :=
  R.four_geom_arctan_one_eq_pi

end ArctanIntegralPiRoute

/-- The compactified positive-half-line density for the Cauchy kernel.  The
second summand is the reciprocal tail after the change of variables
`x ↦ 1 / x`. -/
def cauchyProjectiveFoldDensity (x : Rat) : Rat :=
  ArctanGeometry.integralKernel x +
    (1 / (x * x)) * ArctanGeometry.integralKernel (1 / x)

/-- Reciprocal compactification of the Cauchy kernel is exact on nonzero
rational inputs.  Together with evenness, this is the finite rational algebra
behind the full-line Cauchy integral being represented by four copies of the
unit-interval integral. -/
theorem cauchyProjectiveFoldDensity_eq_two_integralKernel
    (x : Rat) (hx : x ≠ 0) :
    cauchyProjectiveFoldDensity x =
      2 * ArctanGeometry.integralKernel x := by
  have hx2 : x * x ≠ 0 := by
    exact Rat.ne_of_gt
      (RationalCircle.Trigonometry.ratSquare_pos_of_ne_zero hx)
  have hden : 1 + (1 / x) * (1 / x) = (1 + x * x) / (x * x) := by
    rw [Rat.div_def]
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold cauchyProjectiveFoldDensity ArctanGeometry.integralKernel
  rw [hden]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The reciprocal Cauchy pullback, isolated from the two-tail folding
identity for use in finite rectangle transports. -/
theorem cauchyIntegralKernel_reciprocal_pullback
    (x : Rat) (hx : x ≠ 0) :
    (1 / (x * x)) * ArctanGeometry.integralKernel (1 / x) =
      ArctanGeometry.integralKernel x := by
  have h := cauchyProjectiveFoldDensity_eq_two_integralKernel x hx
  unfold cauchyProjectiveFoldDensity at h
  grind [Rat.add_assoc]

/-- Reversing a positive Cauchy rectangle cell through reciprocal inversion
places its lower rectangle below the original cell's upper rectangle. -/
theorem cauchyReciprocal_lowerStep_le_upperStep
    {p r : Rat} (hp : 0 < p) (hpr : p <= r) :
    ArctanGeometry.integralLowerStep (1 / r) (1 / p) <=
      ArctanGeometry.integralUpperStep p r := by
  have hr : 0 < r := by grind
  have hpne : p ≠ 0 := Rat.ne_of_gt hp
  have hrne : r ≠ 0 := Rat.ne_of_gt hr
  have hkernel := cauchyIntegralKernel_reciprocal_pullback p hpne
  have hlength : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hratio : p / r <= 1 := by
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := r)
    · calc
        (p * r⁻¹) * r = p := by
          rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hrne, Rat.mul_one]
        _ <= 1 * r := by simpa using hpr
    · exact hr
  have hfactor : (r - p) * (p / r) <= r - p := by
    calc
      (r - p) * (p / r) <= (r - p) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hratio hlength
      _ = r - p := by grind
  have hpullback :
      (1 / p - 1 / r) * ArctanGeometry.integralKernel (1 / p) =
        ((r - p) * (p / r)) *
          ((1 / (p * p)) * ArctanGeometry.integralKernel (1 / p)) := by
    repeat rw [Rat.div_def]
    rw [Rat.inv_mul_rev]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralUpperStep
  rw [hpullback, hkernel]
  exact Rat.mul_le_mul_of_nonneg_right hfactor
    (Rat.le_of_lt (ArctanGeometry.integralKernel_pos p))

/-- The upper rectangle of the same reciprocal cell lies above the original
positive cell's lower rectangle. -/
theorem cauchyReciprocal_lowerStep_le_upperStep_reverse
    {p r : Rat} (hp : 0 < p) (hpr : p <= r) :
    ArctanGeometry.integralLowerStep p r <=
      ArctanGeometry.integralUpperStep (1 / r) (1 / p) := by
  have hr : 0 < r := by grind
  have hpne : p ≠ 0 := Rat.ne_of_gt hp
  have hrne : r ≠ 0 := Rat.ne_of_gt hr
  have hkernel := cauchyIntegralKernel_reciprocal_pullback r hrne
  have hlength : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hratio : 1 <= r / p := by
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := p)
    · calc
        1 * p = p := by grind
        _ <= r := hpr
        _ = (r * p⁻¹) * p := by
          rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hpne, Rat.mul_one]
    · exact hp
  have hfactor : r - p <= (r - p) * (r / p) := by
    calc
      r - p = (r - p) * 1 := by grind
      _ <= (r - p) * (r / p) :=
        Rat.mul_le_mul_of_nonneg_left hratio hlength
  have hpullback :
      (1 / p - 1 / r) * ArctanGeometry.integralKernel (1 / r) =
        ((r - p) * (r / p)) *
          ((1 / (r * r)) * ArctanGeometry.integralKernel (1 / r)) := by
    repeat rw [Rat.div_def]
    rw [Rat.inv_mul_rev]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralUpperStep
  rw [hpullback, hkernel]
  exact Rat.mul_le_mul_of_nonneg_right hfactor
    (Rat.le_of_lt (ArctanGeometry.integralKernel_pos r))

/-- Apply reciprocal inversion to each positive Cauchy cell.  The list order
is retained here because finite rectangle sums are commutative; the ordered
cover reversal is supplied separately when the cells are used as a partition.
-/
def cauchyReciprocalIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (1 / r, 1 / p) :: cauchyReciprocalIntervals rest

/-- Finite Cauchy rectangle sums survive reciprocal inversion on every
strictly positive source cell. -/
theorem cauchyReciprocalIntegralSum_overlaps
    (intervals : List (Rat × Rat))
    (hpositive : forall p r, (p, r) ∈ intervals -> 0 < p /\ p <= r) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval (cauchyReciprocalIntervals intervals))
      (ArctanGeometry.integralSumInterval intervals) := by
  induction intervals with
  | nil =>
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      have hhead : 0 < p /\ p <= r := hpositive p r (by simp)
      have hrest : forall p r, (p, r) ∈ rest -> 0 < p /\ p <= r := by
        intro p' r' hmem
        exact hpositive p' r' (by simp [hmem])
      have htail := ih hrest
      unfold QInterval.Overlaps ArctanGeometry.integralSumInterval
      simp only [cauchyReciprocalIntervals, ArctanGeometry.integralLowerSum,
        ArctanGeometry.integralUpperSum]
      exact ⟨rat_add_le_add
          (cauchyReciprocal_lowerStep_le_upperStep hhead.1 hhead.2) htail.1,
        rat_add_le_add
          (cauchyReciprocal_lowerStep_le_upperStep_reverse hhead.1 hhead.2)
          htail.2⟩

private theorem cauchy_one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

/-- Reverse a positive finite partition while sending each endpoint through
reciprocal inversion, producing the natural increasing cover on the far side
of `1`. -/
def cauchyReciprocalReversedIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      cauchyReciprocalReversedIntervals rest ++ [(1 / r, 1 / p)]

/-- Reciprocal inversion sends an ordered positive rational cover of `[a,b]`
to an ordered cover of `[1/b,1/a]`. -/
theorem cauchyReciprocalReversedIntervals_covers
    (a b : Rat) (intervals : List (Rat × Rat)) (ha : 0 < a)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval (1 / b) (1 / a)
      (cauchyReciprocalReversedIntervals intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp only [cauchyReciprocalReversedIntervals,
        ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr : 0 < r := by grind
      have hrec := ih r b hr hrest
      have horder : 1 / r <= 1 / a :=
        cauchy_one_div_le_one_div_of_pos_of_le ha hpr
      exact ArctanGeometry.CoversInterval.append hrec
        ⟨rfl, horder, rfl⟩

/-- Reversing the reciprocal cells changes their cover order but not either
finite Cauchy rectangle sum. -/
theorem cauchyReciprocalReversedIntegralSum_eq
    (intervals : List (Rat × Rat)) :
    ArctanGeometry.integralSumInterval
        (cauchyReciprocalReversedIntervals intervals) =
      ArctanGeometry.integralSumInterval (cauchyReciprocalIntervals intervals) := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      have ihlo := congrArg QInterval.lo ih
      have ihhi := congrArg QInterval.hi ih
      change ArctanGeometry.integralLowerSum
          (cauchyReciprocalReversedIntervals rest) =
        ArctanGeometry.integralLowerSum (cauchyReciprocalIntervals rest) at ihlo
      change ArctanGeometry.integralUpperSum
          (cauchyReciprocalReversedIntervals rest) =
        ArctanGeometry.integralUpperSum (cauchyReciprocalIntervals rest) at ihhi
      apply (QInterval.mk.injEq _ _ _ _).mpr
      constructor
      · change ArctanGeometry.integralLowerSum
            (cauchyReciprocalReversedIntervals rest ++ [(1 / r, 1 / p)]) =
          ArctanGeometry.integralLowerSum
            ((1 / r, 1 / p) :: cauchyReciprocalIntervals rest)
        rw [ArctanGeometry.integralLowerSum_append, ihlo]
        simp [ArctanGeometry.integralLowerSum, Rat.add_comm]
        rw [Rat.zero_add]
      · change ArctanGeometry.integralUpperSum
            (cauchyReciprocalReversedIntervals rest ++ [(1 / r, 1 / p)]) =
          ArctanGeometry.integralUpperSum
            ((1 / r, 1 / p) :: cauchyReciprocalIntervals rest)
        rw [ArctanGeometry.integralUpperSum_append, ihhi]
        simp [ArctanGeometry.integralUpperSum, Rat.add_comm]
        rw [Rat.zero_add]

/-- The ordered reciprocal cover has the same finite Cauchy overlap as the
unreversed cell list. -/
theorem cauchyReciprocalReversedIntegralSum_overlaps
    (intervals : List (Rat × Rat))
    (hpositive : forall p r, (p, r) ∈ intervals -> 0 < p /\ p <= r) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (cauchyReciprocalReversedIntervals intervals))
      (ArctanGeometry.integralSumInterval intervals) := by
  rw [cauchyReciprocalReversedIntegralSum_eq]
  exact cauchyReciprocalIntegralSum_overlaps intervals hpositive

/-- Affinely transport every cell of a finite rational partition. -/
def cauchyAffineIntervals (offset scale : Rat) :
    List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (offset + scale * p, offset + scale * r) ::
        cauchyAffineIntervals offset scale rest

/-- Nonnegative affine endpoint maps preserve finite ordered covers. -/
theorem cauchyAffineIntervals_covers
    (offset scale a b : Rat) (intervals : List (Rat × Rat))
    (hscale : 0 <= scale)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval (offset + scale * a)
      (offset + scale * b) (cauchyAffineIntervals offset scale intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp only [cauchyAffineIntervals, ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      simp only [cauchyAffineIntervals, ArctanGeometry.CoversInterval]
      refine ⟨trivial, ?_, ih r b hrest⟩
      exact (Rat.add_le_add_left (c := offset)).2
        (Rat.mul_le_mul_of_nonneg_left hpr hscale)

private theorem cauchyAffineIntervals_squareSum
    (offset scale : Rat) (intervals : List (Rat × Rat)) :
    ArctanGeometry.intervalSquareSum
        (cauchyAffineIntervals offset scale intervals) =
      scale * scale * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [cauchyAffineIntervals, ArctanGeometry.intervalSquareSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [cauchyAffineIntervals, ArctanGeometry.intervalSquareSum]
      rw [ih]
      have hdiff : offset + scale * r - (offset + scale * p) =
          scale * (r - p) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
      rw [hdiff]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The dyadic midpoint partition of a rational tail interval `[a,1]`. -/
def cauchyTailDyadicIntervals (a : Rat) (n : Nat) : List (Rat × Rat) :=
  cauchyAffineIntervals a (1 - a)
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals

theorem cauchyTailDyadicIntervals_squareSum (a : Rat) (n : Nat) :
    ArctanGeometry.intervalSquareSum (cauchyTailDyadicIntervals a n) =
      (1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat)) := by
  unfold cauchyTailDyadicIntervals
  rw [cauchyAffineIntervals_squareSum,
    ArctanGeometry.arctanAreaLoopState_squareSum]
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

/-- The explicit tail mesh covers exactly its intended rational interval. -/
theorem cauchyTailDyadicIntervals_covers
    {a : Rat} (_ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.CoversInterval a 1 (cauchyTailDyadicIntervals a n) := by
  have hsource := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (x := (1 : Rat)) (by decide +kernel) n
  have hscale : 0 <= 1 - a := by grind [Rat.sub_eq_add_neg]
  have h := cauchyAffineIntervals_covers a (1 - a) 0 1
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals hscale hsource
  have hleft : a + (1 - a) * 0 = a := by grind
  have hright : a + (1 - a) * 1 = 1 := by grind [Rat.sub_eq_add_neg]
  rw [hleft, hright] at h
  exact h

private theorem cauchyAffineIntervals_positive
    (offset scale : Rat) (intervals : List (Rat × Rat))
    (hoffset : 0 < offset) (hscale : 0 <= scale)
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    forall p r, (p, r) ∈ cauchyAffineIntervals offset scale intervals ->
      0 < p /\ p <= r := by
  induction intervals with
  | nil =>
      intro p r hmem
      simp [cauchyAffineIntervals] at hmem
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, _hr1, hrest⟩
      intro p' r' hmem
      simp only [cauchyAffineIntervals, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        constructor
        · have hnonneg : 0 <= scale * p := Rat.mul_nonneg hscale hp0
          grind
        · exact (Rat.add_le_add_left (c := offset)).2
            (Rat.mul_le_mul_of_nonneg_left hpr hscale)
      · exact ih hrest p' r' htail

/-- Every cell of the tail mesh is strictly positive whenever its left
endpoint is; this is the side condition for reciprocal inversion. -/
theorem cauchyTailDyadicIntervals_positive
    {a : Rat} (ha0 : 0 < a) (ha1 : a <= 1) (n : Nat) :
    forall p r, (p, r) ∈ cauchyTailDyadicIntervals a n -> 0 < p /\ p <= r := by
  have hscale : 0 <= 1 - a := by grind [Rat.sub_eq_add_neg]
  exact cauchyAffineIntervals_positive a (1 - a)
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals ha0 hscale
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel) n)

/-- Reciprocal inversion turns the explicit dyadic tail partition of
`[a,1]` into an ordered partition of `[1,1/a]`. -/
theorem cauchyReciprocalTailDyadicIntervals_covers
    {a : Rat} (ha0 : 0 < a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.CoversInterval 1 (1 / a)
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals a n)) := by
  have hsource := cauchyTailDyadicIntervals_covers (Rat.le_of_lt ha0) ha1 n
  have h := cauchyReciprocalReversedIntervals_covers a 1
    (cauchyTailDyadicIntervals a n) ha0 hsource
  have hone : (1 : Rat) / 1 = 1 := by decide +kernel
  rw [hone] at h
  exact h

/-- The far-side reciprocal tail and its compact-side dyadic source have
overlapping finite Cauchy rectangle brackets. -/
theorem cauchyReciprocalTailDyadicIntervals_overlaps
    {a : Rat} (ha0 : 0 < a) (ha1 : a <= 1) (n : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (cauchyReciprocalReversedIntervals
          (cauchyTailDyadicIntervals a n)))
      (ArctanGeometry.integralSumInterval
        (cauchyTailDyadicIntervals a n)) := by
  exact cauchyReciprocalReversedIntegralSum_overlaps _
    (cauchyTailDyadicIntervals_positive ha0 ha1 n)

private theorem cauchyKernel_ratio_le_two
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    (p + r) / ((1 + p * p) * (1 + r * r)) <= 2 := by
  let D : Rat := (1 + p * p) * (1 + r * r)
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hp2 : 0 <= p * p := Rat.mul_nonneg hp0 hp0
  have hr2 : 0 <= r * r := Rat.mul_nonneg hr0 hr0
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (RationalCircle.Stage.one_add_square_pos p)
      (RationalCircle.Stage.one_add_square_pos r)
  have hpbound : p <= 1 + p * p := by
    by_cases hp1 : p <= 1
    · exact Rat.le_trans hp1 (by grind)
    · have hpge : 1 <= p := by grind
      have hpsq : p <= p * p := by
        calc
          p = p * 1 := by grind
          _ <= p * p := Rat.mul_le_mul_of_nonneg_left hpge hp0
      exact Rat.le_trans hpsq (by grind)
  have hrbound : r <= 1 + r * r := by
    by_cases hr1 : r <= 1
    · exact Rat.le_trans hr1 (by grind)
    · have hrge : 1 <= r := by grind
      have hrsq : r <= r * r := by
        calc
          r = r * 1 := by grind
          _ <= r * r := Rat.mul_le_mul_of_nonneg_left hrge hr0
      exact Rat.le_trans hrsq (by grind)
  have hsum : p + r <= 2 * D := by
    have hleft : p + r <= (1 + p * p) + (1 + r * r) :=
      rat_add_le_add hpbound hrbound
    have hrest : 0 <= p * p + r * r + 2 * (p * p) * (r * r) := by
      exact Rat.add_nonneg (Rat.add_nonneg hp2 hr2)
        (Rat.mul_nonneg
          (Rat.mul_nonneg (by decide +kernel) hp2) hr2)
    calc
      p + r <= (1 + p * p) + (1 + r * r) := hleft
      _ <= (1 + p * p) + (1 + r * r) +
          (p * p + r * r + 2 * (p * p) * (r * r)) := by grind
      _ = 2 * D := by
        dsimp [D]
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      ((p + r) / D) * D = p + r := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 * D := hsum
  · exact hDpos

private theorem cauchyKernel_diff_le_two_len
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    ArctanGeometry.integralKernel p - ArctanGeometry.integralKernel r <=
      2 * (r - p) := by
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let D : Rat := A * B
  have hDpos : 0 < D := by
    dsimp [D, A, B]
    exact Rat.mul_pos (RationalCircle.Stage.one_add_square_pos p)
      (RationalCircle.Stage.one_add_square_pos r)
  have hratio : (p + r) / D <= 2 := by
    simpa [D, A, B] using cauchyKernel_ratio_le_two hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      (ArctanGeometry.integralKernel p -
          ArctanGeometry.integralKernel r) * D =
          (r - p) * (p + r) := by
        dsimp [D, A, B]
        unfold ArctanGeometry.integralKernel
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
          Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ = (r - p) * ((p + r) / D) * D := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (r - p) * 2 * D := by
        exact Rat.mul_le_mul_of_nonneg_right
          (Rat.mul_le_mul_of_nonneg_left hratio hlen)
          (Rat.le_of_lt hDpos)
      _ = (2 * (r - p)) * D := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hDpos

/-- The Cauchy rectangle width has the same elementary squared-cell bound on
the entire nonnegative rational half-line, not just on the unit interval. -/
theorem cauchyIntegralCellWidth_le_two_square
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    ArctanGeometry.integralUpperStep p r -
        ArctanGeometry.integralLowerStep p r <=
      2 * ((r - p) * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hdiff := cauchyKernel_diff_le_two_len hp0 hpr
  unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralLowerStep
  calc
    (r - p) * ArctanGeometry.integralKernel p -
          (r - p) * ArctanGeometry.integralKernel r =
        (r - p) * (ArctanGeometry.integralKernel p -
          ArctanGeometry.integralKernel r) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add]
    _ <= (r - p) * (2 * (r - p)) :=
      Rat.mul_le_mul_of_nonneg_left hdiff hlen
    _ = 2 * ((r - p) * (r - p)) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem cauchyIntegralSumInterval_width_le_two_squareSum
    (intervals : List (Rat × Rat))
    (hwf : ArctanGeometry.NonnegativeIntervals intervals) :
    (ArctanGeometry.integralSumInterval intervals).width <=
      2 * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      change (0 : Rat) - 0 <= 2 * 0
      decide +kernel
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      have hcell := cauchyIntegralCellWidth_le_two_square hp0 hpr
      have htail := ih hrest
      unfold ArctanGeometry.integralSumInterval QInterval.width
      simp [ArctanGeometry.integralLowerSum,
        ArctanGeometry.integralUpperSum,
        ArctanGeometry.intervalSquareSum]
      calc
        ArctanGeometry.integralUpperStep p r +
              ArctanGeometry.integralUpperSum rest -
            (ArctanGeometry.integralLowerStep p r +
              ArctanGeometry.integralLowerSum rest) =
            (ArctanGeometry.integralUpperStep p r -
              ArctanGeometry.integralLowerStep p r) +
              (ArctanGeometry.integralUpperSum rest -
                ArctanGeometry.integralLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ <= 2 * ((r - p) * (r - p)) +
              2 * ArctanGeometry.intervalSquareSum rest :=
              rat_add_le_add hcell htail
        _ = 2 * ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- The Cauchy rectangle bracket on a dyadic mesh of a compact tail has the
usual unit-mesh width bound, uniformly in its rational left endpoint. -/
theorem cauchyTailDyadicIntervals_integral_width_le_dyadic
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchyTailDyadicIntervals a n)).width <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
  have hcover := cauchyTailDyadicIntervals_covers ha0 ha1 n
  have hnonnegative : ArctanGeometry.NonnegativeIntervals
      (cauchyTailDyadicIntervals a n) :=
    ArctanGeometry.CoversInterval.nonnegative ha0 hcover
  have hgap0 : 0 <= 1 - a := by grind [Rat.sub_eq_add_neg]
  have hgap1 : 1 - a <= 1 := by grind [Rat.sub_eq_add_neg]
  have hsq : (1 - a) * (1 - a) <= 1 := by
    calc
      (1 - a) * (1 - a) <= 1 * (1 - a) :=
        Rat.mul_le_mul_of_nonneg_right hgap1 hgap0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hgap1 (by decide +kernel)
      _ = 1 := by decide +kernel
  have hDpos : 0 < (((2 ^ n : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hmesh : (1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hsq
      (Rat.le_of_lt ((Rat.inv_pos).2 hDpos))
  calc
    (ArctanGeometry.integralSumInterval
      (cauchyTailDyadicIntervals a n)).width <=
        2 * ArctanGeometry.intervalSquareSum
          (cauchyTailDyadicIntervals a n) :=
      cauchyIntegralSumInterval_width_le_two_squareSum _ hnonnegative
    _ = 2 * ((1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat))) := by
      rw [cauchyTailDyadicIntervals_squareSum]
    _ <= 2 * (1 / (((2 ^ n : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hmesh (by decide +kernel)

theorem cauchyIntegralSumInterval_width_append
    (left right : List (Rat × Rat)) :
    (ArctanGeometry.integralSumInterval (left ++ right)).width =
      (ArctanGeometry.integralSumInterval left).width +
        (ArctanGeometry.integralSumInterval right).width := by
  unfold ArctanGeometry.integralSumInterval QInterval.width
  rw [ArctanGeometry.integralLowerSum_append,
    ArctanGeometry.integralUpperSum_append]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- On any ordered nonnegative Cauchy partition, the sum of upper rectangles
is bounded by the rational length of the covered interval. -/
private theorem cauchyIntegralUpperSum_le_span
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.integralUpperSum intervals <= b - a := by
  induction intervals generalizing a with
  | nil =>
      simp only [ArctanGeometry.CoversInterval] at hcover
      rw [hcover]
      simp only [ArctanGeometry.integralUpperSum]
      grind [Rat.sub_eq_add_neg]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have htail := ih r hrest
      simp only [ArctanGeometry.integralUpperSum]
      calc
        ArctanGeometry.integralUpperStep a r +
            ArctanGeometry.integralUpperSum rest <=
          (r - a) + (b - r) :=
            rat_add_le_add
              (ArctanGeometry.integralUpperStep_le_width hpr) htail
        _ = b - a := by grind [Rat.sub_eq_add_neg]

private theorem cauchyCoversInterval_left_bound
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    forall p r, (p, r) ∈ intervals -> a <= p := by
  induction intervals generalizing a with
  | nil =>
      intro p r hmem
      simp at hmem
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      intro p' r' hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        exact Rat.le_refl
      · exact Rat.le_trans hpr (ih r hrest p' r' htail)

private theorem cauchyReciprocalCell_square_le
    {a p r : Rat} (ha : 0 < a) (hap : a <= p) (hpr : p <= r) :
    (1 / p - 1 / r) * (1 / p - 1 / r) <=
      (1 / (a * a)) * (1 / (a * a)) * ((r - p) * (r - p)) := by
  have hp : 0 < p := by grind
  have hr : 0 < r := by grind
  have ha0 : 0 <= a := Rat.le_of_lt ha
  have hp0 : 0 <= p := Rat.le_of_lt hp
  have hwidth : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have har : a <= r := Rat.le_trans hap hpr
  have hprod : a * a <= p * r := by
    calc
      a * a <= p * a := Rat.mul_le_mul_of_nonneg_right hap ha0
      _ <= p * r := Rat.mul_le_mul_of_nonneg_left har hp0
  have ha2pos : 0 < a * a := Rat.mul_pos ha ha
  have hinv : 1 / (p * r) <= 1 / (a * a) :=
    cauchy_one_div_le_one_div_of_pos_of_le ha2pos hprod
  have hleft : 1 / p - 1 / r = (r - p) * (1 / (p * r)) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hpne : p ≠ 0 := Rat.ne_of_gt hp
    have hrne : r ≠ 0 := Rat.ne_of_gt hr
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.mul_inv_cancel]
  have hu0 : 0 <= 1 / (p * r) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hp hr)))
  have hv0 : 0 <= 1 / (a * a) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 ha2pos))
  have hsqinv : (1 / (p * r)) * (1 / (p * r)) <=
      (1 / (a * a)) * (1 / (a * a)) := by
    calc
      (1 / (p * r)) * (1 / (p * r)) <=
          (1 / (a * a)) * (1 / (p * r)) :=
            Rat.mul_le_mul_of_nonneg_right hinv hu0
      _ <= (1 / (a * a)) * (1 / (a * a)) :=
            Rat.mul_le_mul_of_nonneg_left hinv hv0
  rw [hleft]
  calc
    ((r - p) * (1 / (p * r))) * ((r - p) * (1 / (p * r))) =
        ((1 / (p * r)) * (1 / (p * r))) * ((r - p) * (r - p)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= ((1 / (a * a)) * (1 / (a * a))) *
          ((r - p) * (r - p)) :=
          Rat.mul_le_mul_of_nonneg_right hsqinv (Rat.mul_nonneg hwidth hwidth)

private theorem cauchyReversedIntervalSquareSum_append
    (left right : List (Rat × Rat)) :
    ArctanGeometry.intervalSquareSum (left ++ right) =
      ArctanGeometry.intervalSquareSum left +
        ArctanGeometry.intervalSquareSum right := by
  induction left with
  | nil =>
      simp only [List.nil_append, ArctanGeometry.intervalSquareSum]
      rw [Rat.zero_add]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, ArctanGeometry.intervalSquareSum]
      rw [ih]
      grind [Rat.add_assoc]

private theorem cauchyReciprocalReversedIntervals_squareSum_le
    (a : Rat) (intervals : List (Rat × Rat)) (ha : 0 < a)
    (hbound : forall p r, (p, r) ∈ intervals -> a <= p /\ p <= r) :
    ArctanGeometry.intervalSquareSum
        (cauchyReciprocalReversedIntervals intervals) <=
      (1 / (a * a)) * (1 / (a * a)) *
        ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp only [cauchyReciprocalReversedIntervals,
        ArctanGeometry.intervalSquareSum]
      grind
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      have hhead := hbound p r (by simp)
      have hrest : forall p' r', (p', r') ∈ rest -> a <= p' /\ p' <= r' := by
        intro p' r' hmem
        exact hbound p' r' (by simp [hmem])
      have htail := ih hrest
      have hcell := cauchyReciprocalCell_square_le ha hhead.1 hhead.2
      simp only [cauchyReciprocalReversedIntervals]
      rw [cauchyReversedIntervalSquareSum_append]
      simp only [ArctanGeometry.intervalSquareSum, Rat.add_zero]
      calc
        ArctanGeometry.intervalSquareSum
              (cauchyReciprocalReversedIntervals rest) +
            (1 / p - 1 / r) * (1 / p - 1 / r) <=
            ((1 / (a * a)) * (1 / (a * a)) *
              ArctanGeometry.intervalSquareSum rest) +
            ((1 / (a * a)) * (1 / (a * a)) * ((r - p) * (r - p))) :=
              rat_add_le_add htail hcell
        _ = (1 / (a * a)) * (1 / (a * a)) *
            ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- Squared widths of the reversed reciprocal dyadic tail are controlled by
the source mesh and the explicit rational tail start. -/
theorem cauchyReciprocalTailDyadicIntervals_squareSum_le
    {a : Rat} (ha : 0 < a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.intervalSquareSum
        (cauchyReciprocalReversedIntervals
          (cauchyTailDyadicIntervals a n)) <=
      (1 / (a * a)) * (1 / (a * a)) *
        ((1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat))) := by
  have hcover := cauchyTailDyadicIntervals_covers (Rat.le_of_lt ha) ha1 n
  have hleft := cauchyCoversInterval_left_bound a 1
    (cauchyTailDyadicIntervals a n) hcover
  have hpositive := cauchyTailDyadicIntervals_positive ha ha1 n
  calc
    ArctanGeometry.intervalSquareSum
        (cauchyReciprocalReversedIntervals
          (cauchyTailDyadicIntervals a n)) <=
        (1 / (a * a)) * (1 / (a * a)) *
          ArctanGeometry.intervalSquareSum (cauchyTailDyadicIntervals a n) :=
      cauchyReciprocalReversedIntervals_squareSum_le a _ ha
        (fun p r hmem => ⟨hleft p r hmem, (hpositive p r hmem).2⟩)
    _ = (1 / (a * a)) * (1 / (a * a)) *
        ((1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat))) := by
        rw [cauchyTailDyadicIntervals_squareSum]

/-- The finite Cauchy rectangle width of the reciprocal tail is bounded by
the squared reciprocal mesh.  The bound is entirely rational and remains
valid beyond the unit interval. -/
theorem cauchyReciprocalTailDyadicIntervals_integral_width_le
    {a : Rat} (ha : 0 < a) (ha1 : a <= 1) (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals a n))).width <=
      2 * ((1 / (a * a)) * (1 / (a * a)) *
        ((1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat)))) := by
  have hcover := cauchyReciprocalTailDyadicIntervals_covers ha ha1 n
  have hnonnegative : ArctanGeometry.NonnegativeIntervals
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals a n)) :=
    ArctanGeometry.CoversInterval.nonnegative (by decide +kernel) hcover
  calc
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals a n))).width <=
        2 * ArctanGeometry.intervalSquareSum
          (cauchyReciprocalReversedIntervals
            (cauchyTailDyadicIntervals a n)) :=
      cauchyIntegralSumInterval_width_le_two_squareSum _ hnonnegative
    _ <= 2 * ((1 / (a * a)) * (1 / (a * a)) *
        ((1 - a) * (1 - a) / (((2 ^ n : Nat) : Rat)))) :=
      Rat.mul_le_mul_of_nonneg_left
        (cauchyReciprocalTailDyadicIntervals_squareSum_le ha ha1 n)
        (by decide +kernel)

/-- A split dyadic mesh of the unit interval: a midpoint mesh on `[0,a]`
followed by the affine midpoint mesh on `[a,1]`. -/
def cauchySplitDyadicIntervals (a : Rat) (n : Nat) : List (Rat × Rat) :=
  (ArctanGeometry.arctanAreaLoopState a n).intervals ++
    cauchyTailDyadicIntervals a n

private theorem cauchyIntervalSquareSum_append
    (left right : List (Rat × Rat)) :
    ArctanGeometry.intervalSquareSum (left ++ right) =
      ArctanGeometry.intervalSquareSum left +
        ArctanGeometry.intervalSquareSum right := by
  induction left with
  | nil =>
      simp only [List.nil_append, ArctanGeometry.intervalSquareSum]
      rw [Rat.zero_add]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, ArctanGeometry.intervalSquareSum]
      rw [ih]
      grind [Rat.add_assoc]

/-- The split unit mesh retains the usual dyadic squared-mesh bound, uniformly
in the rational split point. -/
theorem cauchySplitDyadicIntervals_squareSum
    (a : Rat) (n : Nat) :
    ArctanGeometry.intervalSquareSum (cauchySplitDyadicIntervals a n) =
      (a * a + (1 - a) * (1 - a)) / (((2 ^ n : Nat) : Rat)) := by
  unfold cauchySplitDyadicIntervals
  rw [cauchyIntervalSquareSum_append,
    ArctanGeometry.arctanAreaLoopState_squareSum,
    cauchyTailDyadicIntervals_squareSum]
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem cauchySplitDyadicIntervals_squareSum_le
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.intervalSquareSum (cauchySplitDyadicIntervals a n) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  have hprod : 0 <= a * (1 - a) := by
    apply Rat.mul_nonneg ha0
    grind [Rat.sub_eq_add_neg]
  have hsum : a * a + (1 - a) * (1 - a) <= 1 := by
    calc
      a * a + (1 - a) * (1 - a) = 1 - 2 * (a * (1 - a)) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
          Rat.mul_comm]
      _ <= 1 := by grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < (((2 ^ n : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  rw [cauchySplitDyadicIntervals_squareSum, Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hsum
    (Rat.le_of_lt ((Rat.inv_pos).2 hDpos))

/-- The split mesh is an ordered rational cover of the full unit interval. -/
theorem cauchySplitDyadicIntervals_covers
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.CoversInterval 0 1 (cauchySplitDyadicIntervals a n) := by
  exact ArctanGeometry.CoversInterval.append
    (ArctanGeometry.arctanAreaLoopState_intervals_covers ha0 n)
    (cauchyTailDyadicIntervals_covers ha0 ha1 n)

theorem cauchySplitDyadicIntervals_unit
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.UnitIntervals (cauchySplitDyadicIntervals a n) := by
  exact ArctanGeometry.CoversInterval.unit
    (a := (0 : Rat)) (b := 1) (by decide +kernel) (by decide +kernel)
    (cauchySplitDyadicIntervals_covers ha0 ha1 n)

theorem cauchySplitDyadicIntervals_integral_width_le
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchySplitDyadicIntervals a n)).width <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
  calc
    (ArctanGeometry.integralSumInterval
      (cauchySplitDyadicIntervals a n)).width <=
        2 * ArctanGeometry.intervalSquareSum
          (cauchySplitDyadicIntervals a n) :=
      ArctanGeometry.integralSumInterval_width_le_two_squareSum _
        (cauchySplitDyadicIntervals_unit ha0 ha1 n)
    _ <= 2 * (1 / (((2 ^ n : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left
        (cauchySplitDyadicIntervals_squareSum_le ha0 ha1 n)
        (by decide +kernel)

/-- Any split unit mesh has an overlapping Cauchy rectangle bracket with the
standard midpoint mesh.  This is a finite cover comparison, not an appeal to
an integral uniqueness principle. -/
theorem cauchySplitDyadicIntervals_overlaps_standard
    {a : Rat} (ha0 : 0 <= a) (ha1 : a <= 1) (splitStage standardStage : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (cauchySplitDyadicIntervals a splitStage))
      (ArctanGeometry.integralSumInterval
        (ArctanGeometry.arctanAreaLoopState 1 standardStage).intervals) := by
  exact ArctanGeometry.integralSumInterval_overlaps_of_covers
    (by decide +kernel) _ _
    (cauchySplitDyadicIntervals_covers ha0 ha1 splitStage)
    (ArctanGeometry.arctanAreaLoopState_intervals_covers
      (x := (1 : Rat)) (by decide +kernel) standardStage)

/-- The standard unit mesh followed by the reversed reciprocal tail mesh. -/
def cauchyUnitReciprocalTailDyadicIntervals (a : Rat) (n : Nat) :
    List (Rat × Rat) :=
  (ArctanGeometry.arctanAreaLoopState 1 n).intervals ++
    cauchyReciprocalReversedIntervals (cauchyTailDyadicIntervals a n)

/-- This concatenated mesh reaches from `0` to the reciprocal tail endpoint. -/
theorem cauchyUnitReciprocalTailDyadicIntervals_covers
    {a : Rat} (ha0 : 0 < a) (ha1 : a <= 1) (n : Nat) :
    ArctanGeometry.CoversInterval 0 (1 / a)
      (cauchyUnitReciprocalTailDyadicIntervals a n) := by
  exact ArctanGeometry.CoversInterval.append
    (ArctanGeometry.arctanAreaLoopState_intervals_covers
      (x := (1 : Rat)) (by decide +kernel) n)
    (cauchyReciprocalTailDyadicIntervals_covers ha0 ha1 n)

private theorem cauchyAssembly_overlaps_twoUnitEnvelope
    (U V T R : QInterval) (a : Rat)
    (hU : U.lo <= U.hi)
    (hR : QInterval.Overlaps R T)
    (hsplit : V.lo + T.lo <= U.hi /\ U.lo <= V.hi + T.hi)
    (hVlo : 0 <= V.lo) (hVhi : V.hi <= a) :
    QInterval.Overlaps
      { lo := U.lo + R.lo, hi := U.hi + R.hi }
      { lo := 2 * U.lo - (a + T.width),
        hi := 2 * U.hi + T.width } := by
  unfold QInterval.Overlaps QInterval.width at *
  grind [Rat.sub_eq_add_neg]

/-- The finite unit-plus-reciprocal-tail Cauchy mesh is enclosed by two
standard unit meshes, with only the omitted `[0,a]` contribution and the
compact tail-mesh width as explicit rational errors. -/
def cauchyUnitReciprocalTailDyadicUnitEnvelope (a : Rat) (n : Nat) : QInterval :=
  let unit := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals
  let tail := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a n)
  { lo := 2 * unit.lo - (a + tail.width),
    hi := 2 * unit.hi + tail.width }

theorem cauchyUnitReciprocalTailDyadicIntervals_overlaps_twoUnitEnvelope
    {a : Rat} (ha : 0 < a) (ha1 : a <= 1) (n : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (cauchyUnitReciprocalTailDyadicIntervals a n))
      (cauchyUnitReciprocalTailDyadicUnitEnvelope a n) := by
  let unit : QInterval := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals
  let near : QInterval := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState a n).intervals
  let tail : QInterval := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a n)
  let reciprocalTail : QInterval := ArctanGeometry.integralSumInterval
    (cauchyReciprocalReversedIntervals (cauchyTailDyadicIntervals a n))
  let split : QInterval := ArctanGeometry.integralSumInterval
    (cauchySplitDyadicIntervals a n)
  have hunit : unit.lo <= unit.hi := by
    dsimp [unit]
    exact ArctanGeometry.integralLowerSum_le_integralUpperSum _
      (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative
        (by decide +kernel) n)
  have hreciprocal : QInterval.Overlaps reciprocalTail tail := by
    dsimp [reciprocalTail, tail]
    exact cauchyReciprocalTailDyadicIntervals_overlaps ha ha1 n
  have hsplit : QInterval.Overlaps split unit := by
    dsimp [split, unit]
    exact cauchySplitDyadicIntervals_overlaps_standard
      (Rat.le_of_lt ha) ha1 n n
  have hsplit' : near.lo + tail.lo <= unit.hi /\
      unit.lo <= near.hi + tail.hi := by
    unfold QInterval.Overlaps at hsplit
    simpa [split, near, tail, ArctanGeometry.integralSumInterval,
      cauchySplitDyadicIntervals, ArctanGeometry.integralLowerSum_append,
      ArctanGeometry.integralUpperSum_append] using hsplit
  have hnearLower : 0 <= near.lo := by
    dsimp [near]
    exact ArctanGeometry.integralLowerSum_nonneg _
      (ArctanGeometry.CoversInterval.nonnegative (by decide +kernel)
        (ArctanGeometry.arctanAreaLoopState_intervals_covers
          (Rat.le_of_lt ha) n))
  have hnearUpper : near.hi <= a := by
    dsimp [near]
    change ArctanGeometry.integralUpperSum
      (ArctanGeometry.arctanAreaLoopState a n).intervals <= a
    calc
      ArctanGeometry.integralUpperSum
          (ArctanGeometry.arctanAreaLoopState a n).intervals <= a - 0 :=
        cauchyIntegralUpperSum_le_span 0 a _
          (ArctanGeometry.arctanAreaLoopState_intervals_covers
            (Rat.le_of_lt ha) n)
      _ = a := by grind [Rat.sub_eq_add_neg]
  have hassembly :
      ArctanGeometry.integralSumInterval
          (cauchyUnitReciprocalTailDyadicIntervals a n) =
        { lo := unit.lo + reciprocalTail.lo,
          hi := unit.hi + reciprocalTail.hi } := by
    apply (QInterval.mk.injEq _ _ _ _).mpr
    constructor <;>
      simp [unit, reciprocalTail, cauchyUnitReciprocalTailDyadicIntervals,
        ArctanGeometry.integralSumInterval,
        ArctanGeometry.integralLowerSum_append,
        ArctanGeometry.integralUpperSum_append]
  have h := cauchyAssembly_overlaps_twoUnitEnvelope
    unit near tail reciprocalTail a hunit hreciprocal hsplit'
    hnearLower hnearUpper
  rw [hassembly]
  simpa [cauchyUnitReciprocalTailDyadicUnitEnvelope, unit, tail] using h

/-- A rational compactification of an even full-line integral by folding the
positive reciprocal tail back onto the unit interval.

For an even kernel `kernel`, the intended value is
\[
  2\int_0^1\left(k(x)+x^{-2}k(1/x)\right)\,dx.
\]
The compact density includes its removable value at zero, so the construction
is an ordinary finite interval integral.  The `fold_agrees` field is the
finite rational identity on the punctured unit interval; no improper limit or
completed-real endpoint is built into this definition. -/
structure ReciprocalTailCompactification
    (kernel compactDensity : Rat -> Rat) where
  even : forall x, kernel (-x) = kernel x
  fold_agrees : forall x, 0 < x -> x <= 1 ->
    compactDensity x = kernel x +
      (1 / (x * x)) * kernel (1 / x)
  construction : Integral.CandidateConstructionFor
    (FunctionOnInterval.exactRat compactDensity 0 1)

namespace ReciprocalTailCompactification

/-- The finite compact integral representing the folded positive half of the
even full-line integral. -/
def compactIntegral
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) : RealCompute :=
  Integral.candidateValueFor (FunctionOnInterval.exactRat compactDensity 0 1)
    C.construction

theorem compactIntegral_valid
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) :
    C.compactIntegral.Valid :=
  Integral.candidateValueFor_valid _ C.construction

/-- The projective full-line integral defined by reciprocal-tail folding. -/
def fullLineIntegral
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) : RealCompute :=
  RealCompute.scaleRat 2 C.compactIntegral

theorem fullLineIntegral_valid
    {kernel compactDensity : Rat -> Rat}
    (C : ReciprocalTailCompactification kernel compactDensity) :
    C.fullLineIntegral.Valid :=
  RealCompute.scaleRat_valid C.compactIntegral_valid

end ReciprocalTailCompactification

/-- The removable compact density for the Cauchy kernel.  On the punctured
unit interval it is exactly the kernel plus its reciprocal tail. -/
def cauchyReciprocalTailDensity (x : Rat) : Rat :=
  2 * ArctanGeometry.integralKernel x

theorem cauchyReciprocalTailDensity_even (x : Rat) :
    cauchyReciprocalTailDensity (-x) = cauchyReciprocalTailDensity x := by
  unfold cauchyReciprocalTailDensity ArctanGeometry.integralKernel
  congr 2
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem integralKernel_even (x : Rat) :
    ArctanGeometry.integralKernel (-x) = ArctanGeometry.integralKernel x := by
  unfold ArctanGeometry.integralKernel
  congr 1
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem cauchyReciprocalTailDensity_fold_agrees
    (x : Rat) (hx : 0 < x) (_hx1 : x <= 1) :
    cauchyReciprocalTailDensity x = ArctanGeometry.integralKernel x +
      (1 / (x * x)) * ArctanGeometry.integralKernel (1 / x) := by
  have hxne : x ≠ 0 := Rat.ne_of_gt hx
  unfold cauchyReciprocalTailDensity
  exact (cauchyProjectiveFoldDensity_eq_two_integralKernel x hxne).symm

/-- The Cauchy compact density is computed by exactly twice the verified
rectangle bracket for `1 / (1+x^2)`.  This is a cellwise rational scaling,
not a new arctangent representation. -/
def cauchyReciprocalTailConstruction :
    Integral.CandidateConstructionFor
      (FunctionOnInterval.exactRat cauchyReciprocalTailDensity 0 1) where
  compute := RealCompute.scaleRatCompute 2 arctanIntegralRectangleForAtOne
  certificate := by
    have hvalid := RealCompute.scaleRat_valid (r := (2 : Rat))
      arctanIntegralRectangleForAtOne_valid
    change RealCompute.ValidCompute
      (RealCompute.scaleRatCompute 2 arctanIntegralRectangleForAtOne)
    exact hvalid

/-- The completed rational compactification of the Cauchy full-line integral.
Its outer factor accounts for the negative half-line, and its density's inner
factor accounts for the reciprocal positive tail. -/
def cauchyReciprocalTailCompactification :
    ReciprocalTailCompactification
      ArctanGeometry.integralKernel cauchyReciprocalTailDensity where
  even := integralKernel_even
  fold_agrees := cauchyReciprocalTailDensity_fold_agrees
  construction := cauchyReciprocalTailConstruction

/-- The full-line Cauchy integral, defined entirely by the rational
reciprocal-tail compactification. -/
def cauchyFullLineIntegral : RealCompute :=
  cauchyReciprocalTailCompactification.fullLineIntegral

theorem cauchyFullLineIntegral_valid : cauchyFullLineIntegral.Valid :=
  cauchyReciprocalTailCompactification.fullLineIntegral_valid

theorem cauchyFullLineIntegral_compute_eq_four_rectangle (n : Nat) :
    cauchyFullLineIntegral.compute n =
      (RealCompute.scaleRat 4 arctanIntegralRectangleForAtOne).compute n := by
  simp [cauchyFullLineIntegral,
    ReciprocalTailCompactification.fullLineIntegral,
    ReciprocalTailCompactification.compactIntegral,
    cauchyReciprocalTailCompactification,
    cauchyReciprocalTailConstruction, Integral.candidateValueFor,
    RealCompute.scaleRat, RealCompute.scaleRatCompute]
  grind [Rat.mul_assoc]

/-- The certified full-line Cauchy evaluator is four times the unit
rectangle evaluator, so its own interval width has a direct linear bound.
The dyadic `224 / 2^n` bound used elsewhere is a bridge-envelope bound, not
the convergence rate of this public raw evaluator. -/
theorem cauchyFullLineIntegral_width_le_sixteen_div_succ (n : Nat) :
    (cauchyFullLineIntegral.compute n).width <=
      (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
  rw [cauchyFullLineIntegral_compute_eq_four_rectangle]
  rw [RealCompute.scaleRat_width_of_nonneg (by decide +kernel : (0 : Rat) <= 4)]
  calc
    4 * (arctanIntegralRectangleForAtOne.compute n).width <=
        4 * ((4 : Rat) / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left
        (arctanIntegralRectangleForAtOne_width_le_four_div_succ n)
        (by decide +kernel)
    _ = (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]

/-- The bounded symmetric Cauchy kernel on `[-1,1]`.  Its natural
piecewise-monotone decomposition breaks at zero: it is nondecreasing on the
negative half and nonincreasing on the positive half. -/
def symmetricCauchyKernelInterval : FunctionOnInterval :=
  oneOverOnePlusSquareOnInterval (-1) 1

/-- The negative half of the symmetric Cauchy kernel, evaluated by reflecting
the certified positive unit-branch rectangle computation.  The monotonicity
certificate is genuinely increasing: `x ↦ 1 / (1 + x^2)` rises on `[-1,0]`. -/
private def symmetricCauchyNegativePiece :
    Integral.MonotoneCandidateConstructionFor
      (symmetricCauchyKernelInterval.restrict (-1) 0 (by decide +kernel)
        (by decide +kernel) (by decide +kernel)) where
  monotone := MonotoneOnInterval.ofNondecreasing (by
    intro p q hp hq hpq n
    have hqbounds : (-1 : Rat) <= q /\ q <= 0 := by
      simpa [symmetricCauchyKernelInterval, FunctionOnInterval.restrict,
        inDomainInterval] using hq
    have hq0 : 0 <= -q := by grind
    have hneg : -q <= -p := by grind
    have h := ArctanGeometry.integralKernel_antitone_nonneg hq0 hneg
    change 1 / (1 + p * p) <= 1 / (1 + q * q)
    unfold ArctanGeometry.integralKernel at h
    rw [show -p * -p = p * p by grind [Rat.neg_mul, Rat.mul_neg],
      show -q * -q = q * q by grind [Rat.neg_mul, Rat.mul_neg]] at h
    simpa only [ArctanGeometry.integralKernel] using h)
  construction :=
    { compute := arctanIntegralRectangleForAtOne.compute
      certificate := by
        exact arctanIntegralRectangleForAtOne_valid }

/-- The positive half of the symmetric Cauchy kernel, using the usual
decreasing unit-branch rectangle computation. -/
private def symmetricCauchyPositivePiece :
    Integral.MonotoneCandidateConstructionFor
      (symmetricCauchyKernelInterval.restrict 0 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel)) where
  monotone := MonotoneOnInterval.ofNonincreasing (by
    intro p q hp hq hpq n
    have hpbounds : (0 : Rat) <= p /\ p <= 1 := by
      simpa [symmetricCauchyKernelInterval, FunctionOnInterval.restrict,
        inDomainInterval] using hp
    have hp0 : 0 <= p := hpbounds.1
    have h := ArctanGeometry.integralKernel_antitone_nonneg hp0 hpq
    change 1 / (1 + q * q) <= 1 / (1 + p * p)
    simpa only [ArctanGeometry.integralKernel] using h)
  construction :=
    { compute := arctanIntegralRectangleForAtOne.compute
      certificate := by
        exact arctanIntegralRectangleForAtOne_valid }

/-- An executable two-piece construction for the bounded symmetric Cauchy
integral.  The partition `[-1,0,1]` makes the increasing/decreasing split
explicit instead of hiding it in an evenness argument. -/
def symmetricCauchyTwoPieceConstruction :
    Integral.GeneralCandidateConstructionFor symmetricCauchyKernelInterval where
  pieces := 2
  positive := by decide
  point
    | 0 => -1
    | 1 => 0
    | _ + 2 => 1
  left_endpoint := rfl
  right_endpoint := rfl
  point_mem := by
    intro i hi
    have hcases : i = 0 \/ i = 1 \/ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · change (-1 : Rat) <= -1 /\ -1 <= 1
      decide +kernel
    · change (-1 : Rat) <= 0 /\ 0 <= 1
      decide +kernel
    · change (-1 : Rat) <= 1 /\ 1 <= 1
      decide +kernel
  point_mono := by
    intro i j hij hj
    have hicases : i = 0 \/ i = 1 \/ i = 2 := by omega
    have hjcases : j = 0 \/ j = 1 \/ j = 2 := by omega
    rcases hicases with rfl | rfl | rfl <;>
      rcases hjcases with rfl | rfl | rfl <;>
      first | omega | decide +kernel
  construction := by
    intro k hk
    cases k with
    | zero => exact symmetricCauchyNegativePiece
    | succ k =>
      cases k with
      | zero => exact symmetricCauchyPositivePiece
      | succ k => exact False.elim (by omega)

/-- The bounded Cauchy integral assembled by the public finite
piecewise-monotone integral operator. -/
def symmetricCauchyPiecewiseIntegral : RealCompute :=
  Integral.generalCandidateValueFor symmetricCauchyKernelInterval
    symmetricCauchyTwoPieceConstruction

theorem symmetricCauchyPiecewiseIntegral_valid :
    symmetricCauchyPiecewiseIntegral.Valid :=
  Integral.generalCandidateValueFor_valid symmetricCauchyKernelInterval
    symmetricCauchyTwoPieceConstruction

/-- The two monotone pieces are both the reflected unit-branch rectangle
evaluator.  Their finite sum is therefore equivalent to two copies of that
evaluator, without invoking a limit-level evenness principle. -/
theorem symmetricCauchyPiecewiseIntegral_equiv_two_rectangle :
    symmetricCauchyPiecewiseIntegral.Equiv
      ((2 : Nat) * arctanIntegralRectangleForAtOne : RealCompute) := by
  change
    (RealCompute.ofRat 0 + arctanIntegralRectangleForAtOne +
      arctanIntegralRectangleForAtOne).Equiv
      ((2 : Nat) * arctanIntegralRectangleForAtOne : RealCompute)
  have hA : arctanIntegralRectangleForAtOne.Valid :=
    arctanIntegralRectangleForAtOne_valid
  have hzeroA : (RealCompute.ofRat 0 + arctanIntegralRectangleForAtOne).Valid :=
    RealCompute.add_valid (RealCompute.ofRat_valid 0) hA
  have hsum :
      (RealCompute.ofRat 0 + arctanIntegralRectangleForAtOne +
        arctanIntegralRectangleForAtOne).Valid :=
    RealCompute.add_valid hzeroA hA
  have hdouble :
      (arctanIntegralRectangleForAtOne +
        arctanIntegralRectangleForAtOne).Valid :=
    RealCompute.add_valid hA hA
  have hscale :
      ((2 : Nat) * arctanIntegralRectangleForAtOne : RealCompute).Valid :=
    RealCompute.natScale_valid 2 hA
  have hsum_double :
      (RealCompute.ofRat 0 + arctanIntegralRectangleForAtOne +
        arctanIntegralRectangleForAtOne).Equiv
      (arctanIntegralRectangleForAtOne +
        arctanIntegralRectangleForAtOne) :=
    RealCompute.add_equiv hzeroA hA hA hA
      (RealCompute.zero_add_equiv hA)
      (RealCompute.equiv_refl arctanIntegralRectangleForAtOne hA)
  exact RealCompute.equiv_trans hsum hdouble hscale hsum_double
    (RealCompute.equiv_symm
      (RealCompute.two_natscale_equiv_add_self
        arctanIntegralRectangleForAtOne hA))

/-- Direct width bound for the two-piece bounded Cauchy integral. -/
theorem symmetricCauchyPiecewiseIntegral_compute_width_le_eight_div_succ
    (n : Nat) :
    (symmetricCauchyPiecewiseIntegral.compute n).width <=
      (8 : Rat) / (((n + 1 : Nat) : Rat)) := by
  change
    ((RealCompute.ofRat 0 + arctanIntegralRectangleForAtOne +
      arctanIntegralRectangleForAtOne).compute n).width <=
      (8 : Rat) / (((n + 1 : Nat) : Rat))
  rw [RealCompute.add_width, RealCompute.add_width]
  have hA := arctanIntegralRectangleForAtOne_width_le_four_div_succ n
  have hdouble :
      (arctanIntegralRectangleForAtOne.compute n).width +
        (arctanIntegralRectangleForAtOne.compute n).width <=
      (8 : Rat) / (((n + 1 : Nat) : Rat)) := by
    calc
      (arctanIntegralRectangleForAtOne.compute n).width +
          (arctanIntegralRectangleForAtOne.compute n).width <=
        (4 : Rat) / (((n + 1 : Nat) : Rat)) +
          (arctanIntegralRectangleForAtOne.compute n).width :=
        (Rat.add_le_add_right).2 hA
      _ <= (4 : Rat) / (((n + 1 : Nat) : Rat)) +
          (4 : Rat) / (((n + 1 : Nat) : Rat)) :=
        (Rat.add_le_add_left).2 hA
      _ = (8 : Rat) / (((n + 1 : Nat) : Rat)) := by
        rw [Rat.div_def]
        grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hzero : (RealCompute.ofRat 0).compute n = { lo := 0, hi := 0 } := rfl
  rw [hzero]
  change 0 - 0 +
      ((arctanIntegralRectangleForAtOne.compute n).hi -
        (arctanIntegralRectangleForAtOne.compute n).lo) +
      ((arctanIntegralRectangleForAtOne.compute n).hi -
        (arctanIntegralRectangleForAtOne.compute n).lo) <=
      (8 : Rat) / (((n + 1 : Nat) : Rat))
  have hzero_sub : (0 : Rat) - 0 = 0 := by decide +kernel
  rw [hzero_sub]
  change
    ((arctanIntegralRectangleForAtOne.compute n).hi -
        (arctanIntegralRectangleForAtOne.compute n).lo) +
      ((arctanIntegralRectangleForAtOne.compute n).hi -
        (arctanIntegralRectangleForAtOne.compute n).lo) <=
      (8 : Rat) / (((n + 1 : Nat) : Rat)) at hdouble
  have hzero_add :
      (0 : Rat) +
        ((arctanIntegralRectangleForAtOne.compute n).hi -
          (arctanIntegralRectangleForAtOne.compute n).lo) +
        ((arctanIntegralRectangleForAtOne.compute n).hi -
          (arctanIntegralRectangleForAtOne.compute n).lo) =
      ((arctanIntegralRectangleForAtOne.compute n).hi -
        (arctanIntegralRectangleForAtOne.compute n).lo) +
        ((arctanIntegralRectangleForAtOne.compute n).hi -
          (arctanIntegralRectangleForAtOne.compute n).lo) := by
        grind [Rat.add_assoc]
  rw [hzero_add]
  exact hdouble

/-- The bounded symmetric Cauchy formula for pi:
`pi = 2 * (∫_{-1}^0 dx/(1+x^2) + ∫_0^1 dx/(1+x^2))`.
The outer factor accounts for the two half-turns represented by this bounded
chart integral. -/
def piSymmetricCauchyPiecewiseIntegral : RealCompute :=
  (2 : Nat) * symmetricCauchyPiecewiseIntegral

theorem piSymmetricCauchyPiecewiseIntegral_valid :
    piSymmetricCauchyPiecewiseIntegral.Valid := by
  unfold piSymmetricCauchyPiecewiseIntegral
  exact RealCompute.natScale_valid 2 symmetricCauchyPiecewiseIntegral_valid

theorem piSymmetricCauchyPiecewiseIntegral_compute_width_le_sixteen_div_succ
    (n : Nat) :
    (piSymmetricCauchyPiecewiseIntegral.compute n).width <=
      (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
  unfold piSymmetricCauchyPiecewiseIntegral
  rw [RealCompute.natScale_width]
  have h := symmetricCauchyPiecewiseIntegral_compute_width_le_eight_div_succ n
  calc
    (2 : Rat) * (symmetricCauchyPiecewiseIntegral.compute n).width <=
        2 * ((8 : Rat) / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left h (by decide +kernel)
    _ = (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The denominator of the reciprocal quartic test integrand. -/
def reciprocalQuarticDenominator (a x : Rat) : Rat :=
  x * x * x * x + a * (x * x) + 1

/-- The reciprocal quartic kernel
`x ↦ 1 / (x^4 + a*x^2 + 1)`, written without powers so the finite algebra is
transparent to Lean. -/
def reciprocalQuarticKernel (a x : Rat) : Rat :=
  1 / reciprocalQuarticDenominator a x

/-- The projective-line substitution used on the positive half-line. -/
def reciprocalDifference (x : Rat) : Rat :=
  x - 1 / x

/-- The formal derivative of `x - 1/x`, expressed as a rational function. -/
def reciprocalDifferenceJacobian (x : Rat) : Rat :=
  1 + 1 / (x * x)

/-- The denominator of the shifted Cauchy kernel obtained after the substitution
`u = x - 1/x`. -/
def shiftedCauchyDenominator (a u : Rat) : Rat :=
  u * u + a + 2

/-- The shifted Cauchy kernel `u ↦ 1 / (u^2 + a + 2)`. -/
def shiftedCauchyKernel (a u : Rat) : Rat :=
  1 / shiftedCauchyDenominator a u

/-- At `a = -1`, the shifted Cauchy denominator is exactly the arctangent
denominator. -/
theorem shiftedCauchyDenominator_minus_one_eq_one_plus_square (u : Rat) :
    shiftedCauchyDenominator (-1) u = 1 + u * u := by
  unfold shiftedCauchyDenominator
  grind [Rat.add_assoc, Rat.add_comm]

/-- At `a = -1`, the shifted Cauchy kernel is the arctangent kernel. -/
theorem shiftedCauchyKernel_minus_one_eq_integralKernel (u : Rat) :
    shiftedCauchyKernel (-1) u = ArctanGeometry.integralKernel u := by
  unfold shiftedCauchyKernel ArctanGeometry.integralKernel
  rw [shiftedCauchyDenominator_minus_one_eq_one_plus_square]

/-- The raw arctangent kernel computes the shifted Cauchy kernel in the
pi-producing case `a = -1`. -/
theorem oneOverOnePlusSquareRaw_compute_eq_shiftedCauchyKernel_minus_one
    (u : Rat) (h : oneOverOnePlusSquareRaw.definedAt u) (n : Nat) :
    oneOverOnePlusSquareRaw.compute u h n =
      { lo := shiftedCauchyKernel (-1) u,
        hi := shiftedCauchyKernel (-1) u } := by
  rw [shiftedCauchyKernel_minus_one_eq_integralKernel]
  simp [oneOverOnePlusSquareRaw, ArctanGeometry.integralKernel]

/-- The symmetrized quartic density that appears after pairing `x` with
`1/x` on the positive half-line. -/
def reciprocalQuarticSymmetricDensity (a x : Rat) : Rat :=
  (1 + x * x) * reciprocalQuarticKernel a x

/-- The folded positive-half-line density obtained by sending the tail
`[1, infinity)` back to `[0,1]` by `x ↦ 1/x`. -/
def reciprocalQuarticUnitFoldDensity (a x : Rat) : Rat :=
  reciprocalQuarticKernel a x +
    (1 / (x * x)) * reciprocalQuarticKernel a (1 / x)

/-- Expected value of the full-line reciprocal quartic test integral when
`a + 2 = b^2` and `0 < b`: it should be `pi / b`. -/
def reciprocalQuarticExpectedPiMultiple (b : Rat) : RealCompute :=
  RealCompute.scaleRat (1 / b) piCircleArea

/-- Expected raw value of the clean projective test
`∫_(-∞)^∞ dx/(x^4 - x^2 + 1)`, namely `pi`.  This is only the expected value;
the projective integral construction still has to be supplied separately. -/
def reciprocalQuarticMinusOneExpectedPi : RealCompute :=
  reciprocalQuarticExpectedPiMultiple 1

/-- The rational parameter condition under which the reciprocal quartic integral
is expected to reduce to a rational multiple of pi. -/
def ReciprocalQuarticPiParameter (a b : Rat) : Prop :=
  0 < b ∧ a + 2 = b * b

theorem reciprocalQuarticPiParameter_minus_one :
    ReciprocalQuarticPiParameter (-1) 1 := by
  unfold ReciprocalQuarticPiParameter
  constructor <;> decide +kernel

private theorem rat_square_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) :
    0 < x * x := by
  by_cases hxpos : 0 < x
  · exact Rat.mul_pos hxpos hxpos
  · have hxneg : x < 0 := by grind
    have hnegpos : 0 < -x := by grind
    have hsq : 0 < (-x) * (-x) := Rat.mul_pos hnegpos hnegpos
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

private theorem rat_square_nonneg (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem rat_eq_of_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Clearing denominators in the projective substitution:
\[
  x^2\left((x-1/x)^2+a+2\right)=x^4+a x^2+1.
\]
This is the finite rational identity behind the quartic test integral. -/
theorem reciprocalDifference_quartic_denominator
    (a x : Rat) (hx : x ≠ 0) :
    x * x * shiftedCauchyDenominator a (reciprocalDifference x) =
      reciprocalQuarticDenominator a x := by
  unfold shiftedCauchyDenominator reciprocalDifference
    reciprocalQuarticDenominator
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The quartic denominator is reciprocal after clearing the expected
projective factor \(x^4\). -/
theorem reciprocalQuarticDenominator_reciprocal_cleared
    (a x : Rat) (hx : x ≠ 0) :
    x * x * x * x * reciprocalQuarticDenominator a (1 / x) =
      reciprocalQuarticDenominator a x := by
  unfold reciprocalQuarticDenominator
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Clearing the denominator in the formal derivative of `x - 1/x`. -/
theorem reciprocalDifferenceJacobian_square_cleared
    (x : Rat) (hx : x ≠ 0) :
    reciprocalDifferenceJacobian x * (x * x) = 1 + x * x := by
  have hx2 : x * x ≠ 0 := Rat.ne_of_gt (rat_square_pos_of_ne_zero hx)
  unfold reciprocalDifferenceJacobian
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The two denominator-cleared identities that convert the reciprocal quartic
kernel into the shifted Cauchy kernel under `u = x - 1/x`.  This is the algebraic
core of the test integral over the projective line; the later integral theorem
will supply the improper-integral bookkeeping. -/
theorem reciprocalQuartic_projective_substitution_data
    (a x : Rat) (hx : x ≠ 0) :
    x * x * shiftedCauchyDenominator a (reciprocalDifference x) =
        reciprocalQuarticDenominator a x ∧
      reciprocalDifferenceJacobian x * (x * x) = 1 + x * x :=
  ⟨reciprocalDifference_quartic_denominator a x hx,
    reciprocalDifferenceJacobian_square_cleared x hx⟩

/-- In the clean pi case \(a=-1\), the shifted Cauchy denominator is
`u^2 + 1`, hence strictly positive on rational inputs. -/
theorem shiftedCauchyDenominator_minus_one_pos (u : Rat) :
    0 < shiftedCauchyDenominator (-1) u := by
  unfold shiftedCauchyDenominator
  have hs : 0 <= u * u := rat_square_nonneg u
  grind

/-- In the clean pi case \(a=-1\), the reciprocal quartic denominator is
strictly positive on rational inputs. -/
theorem reciprocalQuarticDenominator_minus_one_pos (x : Rat) :
    0 < reciprocalQuarticDenominator (-1) x := by
  by_cases hxzero : x = 0
  · subst x
    unfold reciprocalQuarticDenominator
    decide +kernel
  · have hden := reciprocalDifference_quartic_denominator (-1) x hxzero
    have hx2pos : 0 < x * x := rat_square_pos_of_ne_zero hxzero
    have hEpos :
        0 < shiftedCauchyDenominator (-1) (reciprocalDifference x) :=
      shiftedCauchyDenominator_minus_one_pos (reciprocalDifference x)
    have hprod :
        0 < x * x *
          shiftedCauchyDenominator (-1) (reciprocalDifference x) :=
      Rat.mul_pos hx2pos hEpos
    rw [hden] at hprod
    exact hprod

/-- The clean reciprocal-quartic denominator is uniformly separated from
zero by a rational constant.  This is the denominator estimate needed for a
future compact-interval regularity certificate. -/
theorem reciprocalQuarticDenominator_minus_one_ge_three_quarters (x : Rat) :
    (3 : Rat) / 4 <= reciprocalQuarticDenominator (-1) x := by
  have hsq : 0 <= (2 * x * x - 1) * (2 * x * x - 1) :=
    rat_square_nonneg (2 * x * x - 1)
  have hid :
      4 * reciprocalQuarticDenominator (-1) x - 3 =
        (2 * x * x - 1) * (2 * x * x - 1) := by
    unfold reciprocalQuarticDenominator
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hfour : 3 <= 4 * reciprocalQuarticDenominator (-1) x := by
    have hnonneg : 0 <= 4 * reciprocalQuarticDenominator (-1) x - 3 := by
      rw [hid]
      exact hsq
    grind [Rat.sub_eq_add_neg]
  have hscaled := Rat.mul_le_mul_of_nonneg_right hfour
    (by decide +kernel : (0 : Rat) <= 1 / 4)
  calc
    (3 : Rat) / 4 = 3 * (1 / 4) := by
      rw [Rat.div_def, Rat.div_def, Rat.one_mul]
    _ <= (4 * reciprocalQuarticDenominator (-1) x) * (1 / 4) := hscaled
    _ = reciprocalQuarticDenominator (-1) x := by
      rw [Rat.div_def]
      have hcancel : (4 : Rat) * (4 : Rat)⁻¹ = 1 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density is nonnegative at every rational
point.  Together with the uniform denominator bound, this supplies the basic
range information for its forthcoming interval-regularity certificate. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_nonneg (x : Rat) :
    0 <= reciprocalQuarticSymmetricDensity (-1) x := by
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
  apply Rat.mul_nonneg
  · have hsq : 0 <= x * x := rat_square_nonneg x
    grind
  · rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (reciprocalQuarticDenominator_minus_one_pos x))

/-- A uniform rational upper bound for the clean compact density on its
closed chart interval.  It supplies the explicit removable-endpoint tail
budget for the projective quadrature schedule. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
    {x : Rat} (hxlo : -1 <= x) (hxhi : x <= 1) :
    reciprocalQuarticSymmetricDensity (-1) x <= (8 : Rat) / 3 := by
  let q : Rat := reciprocalQuarticDenominator (-1) x
  have hx0sq : 0 <= x * x := rat_square_nonneg x
  have hx2le : x * x <= 1 := by
    by_cases hx0 : 0 <= x
    · calc
        x * x <= 1 * x := Rat.mul_le_mul_of_nonneg_right hxhi hx0
        _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hxhi (by decide +kernel)
        _ = 1 := by decide +kernel
    · have hxneg : x < 0 := by grind
      have hxneg0 : 0 <= -x := by grind
      have hnegx : -x <= 1 := by grind
      have hsq : (-x) * (-x) <= 1 * 1 := by
        calc
          (-x) * (-x) <= 1 * (-x) :=
            Rat.mul_le_mul_of_nonneg_right hnegx hxneg0
          _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hnegx (by decide +kernel)
      calc
        x * x = (-x) * (-x) := by
          grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
        _ <= 1 * 1 := hsq
        _ = 1 := by decide +kernel
  have hnum : 1 + x * x <= 2 := by grind
  have hq : (3 : Rat) / 4 <= q := by
    simpa [q] using reciprocalQuarticDenominator_minus_one_ge_three_quarters x
  have hqpos : 0 < q := by grind
  have hqinv0 : 0 <= q⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hqpos)
  have hscale : 1 <= ((4 : Rat) / 3) * q := by
    have h := Rat.mul_le_mul_of_nonneg_left hq
      (by decide +kernel : (0 : Rat) <= (4 : Rat) / 3)
    have hconst : ((4 : Rat) / 3) * ((3 : Rat) / 4) = 1 := by
      decide +kernel
    rw [hconst] at h
    exact h
  have hqinv : q⁻¹ <= (4 : Rat) / 3 := by
    calc
      q⁻¹ = 1 * q⁻¹ := by grind
      _ <= (((4 : Rat) / 3) * q) * q⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hscale hqinv0
      _ = (4 : Rat) / 3 := by
        have hcancel : q * q⁻¹ = 1 := Rat.mul_inv_cancel q (Rat.ne_of_gt hqpos)
        grind [Rat.mul_assoc, Rat.mul_comm]
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
  change (1 + x * x) * (1 / q) <= (8 : Rat) / 3
  rw [Rat.div_def]
  simp only [Rat.one_mul]
  calc
    (1 + x * x) * q⁻¹ <= 2 * q⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hnum hqinv0
    _ <= 2 * ((4 : Rat) / 3) :=
      Rat.mul_le_mul_of_nonneg_left hqinv (by decide +kernel)
    _ = (8 : Rat) / 3 := by decide +kernel

/-- The one-cell Lipschitz upper enclosure of the compact density on the
remaining interval from s to 1. -/
def projectiveCompactTailUpperCell (s : Rat) : Rat :=
  (1 - s) *
    (reciprocalQuarticSymmetricDensity (-1) s + 8 * (1 - s))

/-- The endpoint cell of the compact projective schedule has a rational tail
budget that is linear in its distance to the chart endpoint. -/
theorem projectiveCompactTailUpperCell_le
    {s : Rat} (hs0 : 0 <= s) (hs1 : s <= 1) :
    projectiveCompactTailUpperCell s <= ((32 : Rat) / 3) * (1 - s) := by
  have hwidth : 0 <= 1 - s := by grind
  have hwidth_le_one : 1 - s <= 1 := by grind
  have hvalue : reciprocalQuarticSymmetricDensity (-1) s <= (8 : Rat) / 3 :=
    reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
      (by grind) hs1
  unfold projectiveCompactTailUpperCell
  calc
    (1 - s) * (reciprocalQuarticSymmetricDensity (-1) s + 8 * (1 - s)) <=
        (1 - s) * ((8 : Rat) / 3 + 8 * (1 - s)) :=
      Rat.mul_le_mul_of_nonneg_left ((Rat.add_le_add_right).2 hvalue) hwidth
    _ <= (1 - s) * ((8 : Rat) / 3 + 8 * 1) :=
      Rat.mul_le_mul_of_nonneg_left
        ((Rat.add_le_add_left).2
          (Rat.mul_le_mul_of_nonneg_left hwidth_le_one (by decide +kernel))) hwidth
    _ = ((32 : Rat) / 3) * (1 - s) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite-difference factorization for the compact reciprocal-quartic
density.  It exposes the denominator and polynomial factors from which a
finite-interval Lipschitz modulus will be derived. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_sub (x y : Rat) :
    reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y =
      ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
        (reciprocalQuarticDenominator (-1) x *
          reciprocalQuarticDenominator (-1) y) := by
  let qx := reciprocalQuarticDenominator (-1) x
  let qy := reciprocalQuarticDenominator (-1) y
  have hqx : qx ≠ 0 := by
    simpa [qx] using Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos x)
  have hqy : qy ≠ 0 := by
    simpa [qy] using Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos y)
  have hprod : qx * qy ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hqx hzero
    · exact hqy hzero
  apply rat_eq_of_mul_eq_mul_ne (c := qx * qy) hprod
  calc
    (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) * (qx * qy) =
        (1 + x * x) * qy - (1 + y * y) * qx := by
      change
        ((1 + x * x) * (1 / qx) - (1 + y * y) * (1 / qy)) * (qx * qy) =
          (1 + x * x) * qy - (1 + y * y) * qx
      rw [Rat.div_def, Rat.div_def]
      have hix : qx⁻¹ * qx = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel qx hqx
      have hiy : qy⁻¹ * qy = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel qy hqy
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) := by
      dsimp [qx, qy]
      unfold reciprocalQuarticDenominator
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
        (qx * qy)) * (qx * qy) := by
      rw [Rat.div_def]
      symm
      calc
        (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) * (qx * qy)⁻¹) *
            (qx * qy) =
            ((y * y - x * x) *
              (x * x + y * y + (x * x) * (y * y) - 2)) *
                ((qx * qy)⁻¹ * (qx * qy)) := by
              rw [Rat.mul_assoc]
        _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) * 1 := by
            rw [Rat.inv_mul_cancel (qx * qy) hprod]
        _ = ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) := by
            rw [Rat.mul_one]

private theorem square_le_one_of_between {x : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1) : x * x <= 1 := by
  by_cases hx : 0 <= x
  · calc
      x * x <= 1 * x := Rat.mul_le_mul_of_nonneg_right hxhi hx
      _ = x := by rw [Rat.one_mul]
      _ <= 1 := hxhi
  · have hxl : x <= 0 := by grind
    have hnx : 0 <= -x := by grind
    have hnhi : -x <= 1 := by grind
    have hs : (-x) * (-x) <= 1 := by
      calc
        (-x) * (-x) <= 1 * (-x) := Rat.mul_le_mul_of_nonneg_right hnhi hnx
        _ = -x := by rw [Rat.one_mul]
        _ <= 1 := hnhi
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

private theorem sum_abs_le_two {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) : qabs (y + x) <= 2 := by
  apply qabs_le_of_neg_le_le
  · grind
  · grind

private theorem reciprocalQuarticLipschitzFactor_abs_le_two {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (x * x + y * y + (x * x) * (y * y) - 2) <= 2 := by
  have hxx0 := rat_square_nonneg x
  have hyy0 := rat_square_nonneg y
  have hxx1 := square_le_one_of_between hxlo hxhi
  have hyy1 := square_le_one_of_between hylo hyhi
  have hprod0 : 0 <= (x * x) * (y * y) := Rat.mul_nonneg hxx0 hyy0
  have hprod1 : (x * x) * (y * y) <= 1 := by
    calc
      (x * x) * (y * y) <= 1 * (y * y) :=
        Rat.mul_le_mul_of_nonneg_right hxx1 hyy0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hyy1
        (by decide +kernel : (0 : Rat) <= 1)
      _ = 1 := by decide +kernel
  apply qabs_le_of_neg_le_le
  · grind [Rat.sub_eq_add_neg]
  · have hsum : x * x + y * y <= 2 := by
      calc
        x * x + y * y <= 1 + y * y :=
          (Rat.add_le_add_right).2 hxx1
        _ <= 1 + 1 := (Rat.add_le_add_left).2 hyy1
        _ = 2 := by decide +kernel
    have hall : x * x + y * y + (x * x) * (y * y) <= 3 := by
      calc
        x * x + y * y + (x * x) * (y * y) <= 2 + (x * x) * (y * y) :=
          (Rat.add_le_add_right).2 hsum
        _ <= 2 + 1 := (Rat.add_le_add_left).2 hprod1
        _ = 3 := by decide +kernel
    grind [Rat.sub_eq_add_neg]

private theorem reciprocalQuarticSquareDifference_abs_le_two_mul {x y : Rat}
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (y * y - x * x) <= 2 * qabs (y - x) := by
  have hsum := sum_abs_le_two hxlo hxhi hylo hyhi
  calc
    qabs (y * y - x * x) = qabs ((y - x) * (y + x)) := by
      congr 1
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = qabs (y - x) * qabs (y + x) := qabs_mul _ _
    _ <= qabs (y - x) * 2 := Rat.mul_le_mul_of_nonneg_left hsum
      (qabs_nonneg _)
    _ = 2 * qabs (y - x) := by rw [Rat.mul_comm]

/-- The reciprocal of the two compact denominator factors has a uniform
rational upper bound. -/
theorem reciprocalQuarticDenominatorProduct_minus_one_inv_le_sixteen_ninths
    (x y : Rat) :
    (reciprocalQuarticDenominator (-1) x *
      reciprocalQuarticDenominator (-1) y)⁻¹ <= (16 : Rat) / 9 := by
  let qx := reciprocalQuarticDenominator (-1) x
  let qy := reciprocalQuarticDenominator (-1) y
  change (qx * qy)⁻¹ <= (16 : Rat) / 9
  have hqx : (3 : Rat) / 4 <= qx := by
    simpa [qx] using reciprocalQuarticDenominator_minus_one_ge_three_quarters x
  have hqy : (3 : Rat) / 4 <= qy := by
    simpa [qy] using reciprocalQuarticDenominator_minus_one_ge_three_quarters y
  have hqx0 : 0 <= qx := Rat.le_trans (by decide +kernel) hqx
  have hqprod : (9 : Rat) / 16 <= qx * qy := by
    calc
      (9 : Rat) / 16 = ((3 : Rat) / 4) * ((3 : Rat) / 4) := by decide +kernel
      _ <= qx * ((3 : Rat) / 4) := Rat.mul_le_mul_of_nonneg_right hqx
        (by decide +kernel)
      _ <= qx * qy := Rat.mul_le_mul_of_nonneg_left hqy hqx0
  have hprodpos : 0 < qx * qy := Rat.mul_pos (by grind) (by grind)
  have hprodne : qx * qy ≠ 0 := Rat.ne_of_gt hprodpos
  have hinvnonneg : 0 <= (qx * qy)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hprodpos)
  have hscale : 1 <= ((16 : Rat) / 9) * (qx * qy) := by
    have h := Rat.mul_le_mul_of_nonneg_left hqprod
      (by decide +kernel : (0 : Rat) <= (16 : Rat) / 9)
    have hconst : ((16 : Rat) / 9) * ((9 : Rat) / 16) = 1 := by
      decide +kernel
    rw [hconst] at h
    exact h
  calc
    (qx * qy)⁻¹ = 1 * (qx * qy)⁻¹ := by rw [Rat.one_mul]
    _ <= (((16 : Rat) / 9) * (qx * qy)) * (qx * qy)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hscale hinvnonneg
    _ = (16 : Rat) / 9 := by
      have hcancel : (qx * qy) * (qx * qy)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ hprodne
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density has an explicit rational
Lipschitz bound on the closed unit interval. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit (x y : Rat)
    (hxlo : -1 <= x) (hxhi : x <= 1)
    (hylo : -1 <= y) (hyhi : y <= 1) :
    qabs (reciprocalQuarticSymmetricDensity (-1) x -
      reciprocalQuarticSymmetricDensity (-1) y) <= 8 * qabs (y - x) := by
  rw [reciprocalQuarticSymmetricDensity_minus_one_sub]
  have hsq := reciprocalQuarticSquareDifference_abs_le_two_mul hxlo hxhi hylo hyhi
  have hfactor := reciprocalQuarticLipschitzFactor_abs_le_two hxlo hxhi hylo hyhi
  have hnum :
      qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) <=
        4 * qabs (y - x) := by
    calc
      qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) =
          qabs (y * y - x * x) *
            qabs (x * x + y * y + (x * x) * (y * y) - 2) := qabs_mul _ _
      _ <= (2 * qabs (y - x)) *
          qabs (x * x + y * y + (x * x) * (y * y) - 2) :=
            Rat.mul_le_mul_of_nonneg_right hsq (qabs_nonneg _)
      _ <= (2 * qabs (y - x)) * 2 :=
            Rat.mul_le_mul_of_nonneg_left hfactor
              (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
      _ = 4 * qabs (y - x) := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hinv :=
    reciprocalQuarticDenominatorProduct_minus_one_inv_le_sixteen_ninths x y
  have hinv0 : 0 <=
      (reciprocalQuarticDenominator (-1) x *
        reciprocalQuarticDenominator (-1) y)⁻¹ := by
    apply Rat.le_of_lt
    apply (Rat.inv_pos).2
    exact Rat.mul_pos (reciprocalQuarticDenominator_minus_one_pos x)
      (reciprocalQuarticDenominator_minus_one_pos y)
  calc
    qabs
        (((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) /
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)) =
        qabs ((y * y - x * x) *
          (x * x + y * y + (x * x) * (y * y) - 2)) *
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)⁻¹ := by
          rw [Rat.div_def, qabs_mul, qabs_eq_self_of_nonneg hinv0]
    _ <= (4 * qabs (y - x)) *
          (reciprocalQuarticDenominator (-1) x *
            reciprocalQuarticDenominator (-1) y)⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hnum hinv0
    _ <= (4 * qabs (y - x)) * ((16 : Rat) / 9) :=
          Rat.mul_le_mul_of_nonneg_left hinv
            (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
    _ <= 8 * qabs (y - x) := by
          have h64 : (4 : Rat) * ((16 : Rat) / 9) <= 8 := by decide +kernel
          calc
            (4 * qabs (y - x)) * ((16 : Rat) / 9) =
                ((4 : Rat) * ((16 : Rat) / 9)) * qabs (y - x) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
            _ <= 8 * qabs (y - x) := Rat.mul_le_mul_of_nonneg_right h64
              (qabs_nonneg _)

/-- The projective coordinate compactifying the real line to the open interval
`(-1,1)`.  Its apparent poles at the endpoints disappear after multiplication
by the Cauchy kernel; the resulting density is the everywhere-defined reciprocal-quartic
kernel below. -/
def projectiveCompactCoordinate (x : Rat) : Rat :=
  x / (1 - x * x)

/-- The reciprocal of the compact projective coordinate is again a total
rational expression.  At the removable value `x = 0` both totalized rational
expressions are zero. -/
theorem projectiveCompactCoordinate_reciprocal (x : Rat) :
    1 / projectiveCompactCoordinate x = (1 - x * x) / x := by
  unfold projectiveCompactCoordinate
  repeat rw [Rat.div_def]
  simp only [Rat.one_mul, Rat.inv_mul_rev, Rat.inv_inv]

/-- Formal Jacobian of `projectiveCompactCoordinate`. -/
def projectiveCompactJacobian (x : Rat) : Rat :=
  (1 + x * x) / ((1 - x * x) * (1 - x * x))

/-- The compact projective coordinate is odd. -/
theorem projectiveCompactCoordinate_neg (x : Rat) :
    projectiveCompactCoordinate (-x) = -projectiveCompactCoordinate x := by
  unfold projectiveCompactCoordinate
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The rational Jacobian of the compact projective coordinate is even. -/
theorem projectiveCompactJacobian_neg (x : Rat) :
    projectiveCompactJacobian (-x) = projectiveCompactJacobian x := by
  unfold projectiveCompactJacobian
  congr 2 <;>
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The clean compact reciprocal-quartic density is even.  This is the
finite symmetry needed to assemble the two projective chart branches. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_even (x : Rat) :
    reciprocalQuarticSymmetricDensity (-1) (-x) =
      reciprocalQuarticSymmetricDensity (-1) x := by
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
    reciprocalQuarticDenominator
  congr 2 <;>
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The denominator of the compact projective chart is positive on its
open rational source interval. -/
theorem projectiveCompactDenominator_pos {x : Rat}
    (hxlo : -1 < x) (hxhi : x < 1) :
    0 < 1 - x * x := by
  have hleft : 0 < 1 - x := by grind
  have hright : 0 < 1 + x := by grind
  calc
    0 < (1 - x) * (1 + x) := Rat.mul_pos hleft hright
    _ = 1 - x * x := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The numerator controlling projective endpoint displacement is positive
when both rational endpoints lie in the open compact chart. -/
theorem projectiveCompactOneAddMul_pos {x y : Rat}
    (hxlo : -1 < x) (hxhi : x < 1)
    (hylo : -1 < y) (hyhi : y < 1) :
    0 < 1 + x * y := by
  by_cases hx0 : 0 <= x
  · by_cases hy0 : 0 <= y
    · have hxy : 0 <= x * y := Rat.mul_nonneg hx0 hy0
      grind
    · have hyneg : y < 0 := by grind
      have hypos : 0 < -y := by grind
      have hmul : x * (-y) < 1 * (-y) :=
        Rat.mul_lt_mul_of_pos_right hxhi hypos
      have hlt : y < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.mul_comm]
      grind
  · have hxneg : x < 0 := by grind
    by_cases hy0 : 0 <= y
    · have hxpos : 0 < -x := by grind
      have hmul : y * (-x) < 1 * (-x) :=
        Rat.mul_lt_mul_of_pos_right hyhi hxpos
      have hlt : x < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.mul_comm]
      grind
    · have hyneg : y < 0 := by grind
      have hxpos : 0 < -x := by grind
      have hypos : 0 < -y := by grind
      have hmul : 0 < (-x) * (-y) := Rat.mul_pos hxpos hypos
      have hxy : 0 < x * y := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      grind

/-- Denominator-cleared endpoint displacement for the compact projective
chart.  This is the finite rational identity used to transport an ordered
source partition through `x / (1 - x^2)`; the analytic change-of-variables
theorem still has to account for the removable chart endpoints. -/
theorem projectiveCompactCoordinate_sub_cleared
    (x y : Rat) (hx : 1 - x * x ≠ 0) (hy : 1 - y * y ≠ 0) :
    (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
        ((1 - y * y) * (1 - x * x)) =
      (y - x) * (1 + x * y) := by
  let dx : Rat := 1 - x * x
  let dy : Rat := 1 - y * y
  have hdx : dx ≠ 0 := by simpa [dx] using hx
  have hdy : dy ≠ 0 := by simpa [dy] using hy
  have hdx_cancel : dx * dx⁻¹ = 1 := Rat.mul_inv_cancel dx hdx
  have hdy_cancel : dy * dy⁻¹ = 1 := Rat.mul_inv_cancel dy hdy
  unfold projectiveCompactCoordinate
  change (y / dy - x / dx) * (dy * dx) = (y - x) * (1 + x * y)
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The compact projective chart preserves the order of rational endpoints
in `(-1,1)`.  This finite theorem is the partition-order half of the
projective substitution route. -/
theorem projectiveCompactCoordinate_strictMono {x y : Rat}
    (hxlo : -1 < x) (hxy : x < y) (hyhi : y < 1) :
    projectiveCompactCoordinate x < projectiveCompactCoordinate y := by
  have hxhi : x < 1 := by grind
  have hylo : -1 < y := by grind
  have hdx : 0 < 1 - x * x := projectiveCompactDenominator_pos hxlo hxhi
  have hdy : 0 < 1 - y * y := projectiveCompactDenominator_pos hylo hyhi
  have hfactor : 0 < 1 + x * y :=
    projectiveCompactOneAddMul_pos hxlo hxhi hylo hyhi
  have hcleared := projectiveCompactCoordinate_sub_cleared x y
    (Rat.ne_of_gt hdx) (Rat.ne_of_gt hdy)
  have hright : 0 <
      (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
        ((1 - y * y) * (1 - x * x)) := by
    rw [hcleared]
    exact Rat.mul_pos (by grind) hfactor
  have hden : 0 < (1 - y * y) * (1 - x * x) := Rat.mul_pos hdy hdx
  have hlt : 0 < projectiveCompactCoordinate y - projectiveCompactCoordinate x := by
    apply Rat.lt_of_mul_lt_mul_right (c := (1 - y * y) * (1 - x * x))
      (hc := Rat.le_of_lt hden)
    calc
      0 * ((1 - y * y) * (1 - x * x)) = 0 := by rw [Rat.zero_mul]
      _ < (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
          ((1 - y * y) * (1 - x * x)) := hright
  grind

/-- Transport every endpoint of a finite rational partition through the
compact projective chart. -/
def projectiveCompactIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (projectiveCompactCoordinate p, projectiveCompactCoordinate r) ::
        projectiveCompactIntervals rest

/-- The compact projective chart is nonnegative on its nonnegative rational
source branch. -/
theorem projectiveCompactCoordinate_nonnegative {x : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) :
    0 <= projectiveCompactCoordinate x := by
  have hxlo : -1 < x := by grind
  have hden : 0 < 1 - x * x := projectiveCompactDenominator_pos hxlo hx1
  unfold projectiveCompactCoordinate
  rw [Rat.div_def]
  exact Rat.mul_nonneg hx0 (Rat.le_of_lt ((Rat.inv_pos).2 hden))

/-- An ordered finite cover of a compact rational subinterval of `(-1,1)`
remains an ordered cover after applying the compact projective chart to every
endpoint.  This is the finite partition transport needed before comparing
quadrature sums. -/
theorem projectiveCompactIntervals_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (ha : -1 < a) (hb : b < 1)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval
      (projectiveCompactCoordinate a) (projectiveCompactCoordinate b)
      (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hrlo : -1 < r := by grind
      have hrle : r <= b := ArctanGeometry.CoversInterval.start_le_end hrest
      have hrhi : r < 1 := by grind
      have hmap : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono ha (by grind) hrhi)
      simp only [projectiveCompactIntervals, ArctanGeometry.CoversInterval]
      exact ⟨trivial, hmap, ih r b hrlo hb hrest⟩

/-- A nonnegative finite source partition transports to a nonnegative
partition on the positive branch of the compact projective chart.  This is
the admissibility condition for the existing Cauchy-kernel quadrature bounds.
-/
theorem projectiveCompactIntervals_nonnegative
    (a b : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hb : b < 1)
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.NonnegativeIntervals (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a b with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.NonnegativeIntervals]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrle : r <= b := ArctanGeometry.CoversInterval.start_le_end hrest
      have hrhi : r < 1 := by grind
      have hleft : 0 <= projectiveCompactCoordinate a :=
        projectiveCompactCoordinate_nonnegative ha (by grind)
      have horder : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · have halo : -1 < a := by grind
          exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono halo (by grind) hrhi)
      simp only [projectiveCompactIntervals, ArctanGeometry.NonnegativeIntervals]
      exact ⟨hleft, horder, ih r b hr0 hb hrest⟩

/-- On a nonnegative compact source branch, the projective chart has the
explicit rational Lipschitz bound
`2 / (1 - s^2)^2` up to a rational endpoint `s < 1`. -/
theorem projectiveCompactCoordinate_sub_le_lipschitz
    {x y s : Rat}
    (hx0 : 0 <= x) (hxy : x <= y) (hys : y <= s) (hs : s < 1) :
    projectiveCompactCoordinate y - projectiveCompactCoordinate x <=
      (2 * (y - x)) / ((1 - s * s) * (1 - s * s)) := by
  let dx : Rat := 1 - x * x
  let dy : Rat := 1 - y * y
  let ds : Rat := 1 - s * s
  have hs0 : 0 <= s := Rat.le_trans (Rat.le_trans hx0 hxy) hys
  have hx1 : x < 1 := by grind
  have hy1 : y < 1 := by grind
  have hxlo : -1 < x := by grind
  have hylo : -1 < y := by grind
  have hslo : -1 < s := by grind
  have hdx : 0 < dx := by
    simpa [dx] using projectiveCompactDenominator_pos hxlo hx1
  have hdy : 0 < dy := by
    simpa [dy] using projectiveCompactDenominator_pos hylo hy1
  have hds : 0 < ds := by
    simpa [ds] using projectiveCompactDenominator_pos hslo hs
  have hxle : x <= s := Rat.le_trans hxy hys
  have hxx : x * x <= s * s := by
    calc
      x * x <= s * x := Rat.mul_le_mul_of_nonneg_right hxle hx0
      _ <= s * s := Rat.mul_le_mul_of_nonneg_left hxle hs0
  have hyy : y * y <= s * s := by
    calc
      y * y <= s * y :=
        Rat.mul_le_mul_of_nonneg_right hys (Rat.le_trans hx0 hxy)
      _ <= s * s := Rat.mul_le_mul_of_nonneg_left hys hs0
  have hdsdx : ds <= dx := by
    dsimp [ds, dx]
    grind
  have hdsdy : ds <= dy := by
    dsimp [ds, dy]
    grind
  have hden : ds * ds <= dy * dx := by
    calc
      ds * ds <= dy * ds :=
        Rat.mul_le_mul_of_nonneg_right hdsdy (Rat.le_of_lt hds)
      _ <= dy * dx := Rat.mul_le_mul_of_nonneg_left hdsdx (Rat.le_of_lt hdy)
  have hfactor : 1 + x * y <= 2 := by
    have hxle1 : x <= 1 := by grind
    have hxy_le_y : x * y <= 1 * y :=
      Rat.mul_le_mul_of_nonneg_right hxle1 (Rat.le_trans hx0 hxy)
    have hy1le : y <= 1 := by grind
    grind
  have hdiff : 0 <= y - x := by grind
  have hclear := projectiveCompactCoordinate_sub_cleared x y
    (Rat.ne_of_gt hdx) (Rat.ne_of_gt hdy)
  have hdenpos : 0 < dy * dx := Rat.mul_pos hdy hdx
  have hdelta : projectiveCompactCoordinate y - projectiveCompactCoordinate x =
      ((y - x) * (1 + x * y)) / (dy * dx) := by
    apply rat_eq_of_mul_eq_mul_ne (c := dy * dx) (Rat.ne_of_gt hdenpos)
    rw [Rat.div_def]
    have hcancel : (dy * dx)⁻¹ * (dy * dx) = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
    calc
      (projectiveCompactCoordinate y - projectiveCompactCoordinate x) *
          (dy * dx) = (y - x) * (1 + x * y) := by
            simpa [dx, dy] using hclear
      _ = ((y - x) * (1 + x * y) * (dy * dx)⁻¹) * (dy * dx) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
  have hinv : (dy * dx)⁻¹ <= (ds * ds)⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := (ds * ds) * (dy * dx))
    · calc
        (dy * dx)⁻¹ * ((ds * ds) * (dy * dx)) = ds * ds := by
          have hcancel : (dy * dx)⁻¹ * (dy * dx) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= dy * dx := hden
        _ = (ds * ds)⁻¹ * ((ds * ds) * (dy * dx)) := by
          have hss : ds * ds ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hds hds)
          have hcancel : (ds * ds)⁻¹ * (ds * ds) = 1 :=
            Rat.inv_mul_cancel _ hss
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact Rat.mul_pos (Rat.mul_pos hds hds) hdenpos
  rw [hdelta]
  rw [Rat.div_def]
  calc
    (y - x) * (1 + x * y) * (dy * dx)⁻¹ <=
        (y - x) * 2 * (dy * dx)⁻¹ := by
      apply Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left hfactor hdiff)
      exact Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
    _ <= (y - x) * 2 * (ds * ds)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_left hinv
        (Rat.mul_nonneg hdiff (by decide +kernel))
    _ = 2 * (y - x) * (ds * ds)⁻¹ := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The projective image of a nonnegative finite partition has a controlled
squared mesh.  The explicit factor is the square of the compact-branch
Lipschitz bound and is the finite estimate needed for transported quadrature
errors. -/
theorem projectiveCompactIntervals_squareSum_le
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    ArctanGeometry.intervalSquareSum (projectiveCompactIntervals intervals) <=
      (2 / ((1 - s * s) * (1 - s * s))) *
        (2 / ((1 - s * s) * (1 - s * s))) *
          ArctanGeometry.intervalSquareSum intervals := by
  let L : Rat := 2 / ((1 - s * s) * (1 - s * s))
  have hs0 : 0 <= s :=
    Rat.le_trans ha (ArctanGeometry.CoversInterval.start_le_end hcover)
  have hslo : -1 < s := by grind
  have hds : 0 < 1 - s * s := projectiveCompactDenominator_pos hslo hs
  have hL : 0 <= L := by
    dsimp [L]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hds hds)))
  change ArctanGeometry.intervalSquareSum (projectiveCompactIntervals intervals) <=
    L * L * ArctanGeometry.intervalSquareSum intervals
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactIntervals, ArctanGeometry.intervalSquareSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hwidth :
          projectiveCompactCoordinate r - projectiveCompactCoordinate a <=
            L * (r - a) := by
        calc
          projectiveCompactCoordinate r - projectiveCompactCoordinate a <=
              (2 * (r - a)) / ((1 - s * s) * (1 - s * s)) :=
            projectiveCompactCoordinate_sub_le_lipschitz ha hpr hrs hs
          _ = L * (r - a) := by
            dsimp [L]
            rw [Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm]
      have hsource : 0 <= r - a := by grind
      have horder : projectiveCompactCoordinate a <= projectiveCompactCoordinate r := by
        by_cases har : a = r
        · subst r
          exact Rat.le_refl
        · have halo : -1 < a := by grind
          have hr1 : r < 1 := by grind
          exact Rat.le_of_lt
            (projectiveCompactCoordinate_strictMono halo (by grind) hr1)
      have himage : 0 <=
          projectiveCompactCoordinate r - projectiveCompactCoordinate a := by grind
      have hscaled : 0 <= L * (r - a) := Rat.mul_nonneg hL hsource
      have hcell :
          (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) <=
            L * L * ((r - a) * (r - a)) := by
        calc
          (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) <=
            (L * (r - a)) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) := by
              exact Rat.mul_le_mul_of_nonneg_right hwidth himage
          _ <= (L * (r - a)) * (L * (r - a)) := by
              exact Rat.mul_le_mul_of_nonneg_left hwidth hscaled
          _ = L * L * ((r - a) * (r - a)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      have htail := ih r hr0 hrest
      simp only [projectiveCompactIntervals, ArctanGeometry.intervalSquareSum]
      calc
        (projectiveCompactCoordinate r - projectiveCompactCoordinate a) *
              (projectiveCompactCoordinate r - projectiveCompactCoordinate a) +
            ArctanGeometry.intervalSquareSum (projectiveCompactIntervals rest) <=
          L * L * ((r - a) * (r - a)) +
            L * L * ArctanGeometry.intervalSquareSum rest := by grind
        _ = L * L * ((r - a) * (r - a) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.mul_assoc]

/-- The standard midpoint-dyadic partition of a compact positive source
branch has an explicit transported squared-mesh bound. -/
theorem projectiveCompactAreaLoop_squareSum_le
    {s : Rat} (hs0 : 0 <= s) (hs : s < 1) (n : Nat) :
    ArctanGeometry.intervalSquareSum
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState s n).intervals) <=
      (2 / ((1 - s * s) * (1 - s * s))) *
        (2 / ((1 - s * s) * (1 - s * s))) *
          (s * s / (((2 ^ n : Nat) : Rat))) := by
  calc
    ArctanGeometry.intervalSquareSum
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState s n).intervals) <=
        (2 / ((1 - s * s) * (1 - s * s))) *
          (2 / ((1 - s * s) * (1 - s * s))) *
            ArctanGeometry.intervalSquareSum
              (ArctanGeometry.arctanAreaLoopState s n).intervals :=
      projectiveCompactIntervals_squareSum_le 0 s
        (ArctanGeometry.arctanAreaLoopState s n).intervals (by decide +kernel) hs
        (ArctanGeometry.arctanAreaLoopState_intervals_covers hs0 n)
    _ = (2 / ((1 - s * s) * (1 - s * s))) *
          (2 / ((1 - s * s) * (1 - s * s))) *
            (s * s / (((2 ^ n : Nat) : Rat))) := by
      rw [ArctanGeometry.arctanAreaLoopState_squareSum]

/-- The compact source endpoint used by the projective quadrature schedule.
At stage `n` it stops one dyadic unit short of the chart pole. -/
def projectiveCompactDyadicEndpoint (n : Nat) : Rat :=
  1 - 1 / (((2 ^ n : Nat) : Rat))

/-- The dyadic projective schedule remains on the nonnegative compact branch. -/
theorem projectiveCompactDyadicEndpoint_nonnegative (n : Nat) :
    0 <= projectiveCompactDyadicEndpoint n := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hDge : 1 <= D := by
    dsimp [D]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
  have hinv : D⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := D)
    · calc
        D⁻¹ * D = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
        _ <= 1 * D := by simpa using hDge
    · exact hDpos
  unfold projectiveCompactDyadicEndpoint
  rw [Rat.div_def]
  dsimp [D] at hinv
  grind [Rat.sub_eq_add_neg]

/-- The dyadic projective schedule stays strictly below the chart pole. -/
theorem projectiveCompactDyadicEndpoint_lt_one (n : Nat) :
    projectiveCompactDyadicEndpoint n < 1 := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  unfold projectiveCompactDyadicEndpoint
  rw [Rat.div_def]
  have hinv : 0 < D⁻¹ := (Rat.inv_pos).2 hDpos
  dsimp [D] at hinv
  grind [Rat.sub_eq_add_neg]

/-- From the first positive dyadic stage onward, the compact projective
endpoint is at least one half. -/
theorem projectiveCompactDyadicEndpoint_succ_ge_half (n : Nat) :
    (1 : Rat) / 2 <= projectiveCompactDyadicEndpoint (n + 1) := by
  have hpow : 2 <= 2 ^ (n + 1) := by
    calc
      2 = 1 * 2 := by omega
      _ <= 2 ^ n * 2 :=
        Nat.mul_le_mul_right 2 (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
      _ = 2 ^ (n + 1) := by
        rw [Nat.pow_succ]
  have hinv : 1 / (((2 ^ (n + 1) : Nat) : Rat)) <= (1 : Rat) / 2 :=
    FTC.one_div_nat_antitone (by omega : 0 < 2)
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  unfold projectiveCompactDyadicEndpoint
  grind [Rat.sub_eq_add_neg]

/-- The projective denominator at a dyadic compact endpoint is at most twice
its remaining dyadic distance to the endpoint. -/
theorem projectiveCompactDyadicEndpoint_denominator_le (n : Nat) :
    1 - projectiveCompactDyadicEndpoint n * projectiveCompactDyadicEndpoint n <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
  have hs1 : projectiveCompactDyadicEndpoint n <= 1 :=
    Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n)
  have hwidth : 0 <= 1 - projectiveCompactDyadicEndpoint n := by
    grind [Rat.sub_eq_add_neg]
  have hfactor : 1 + projectiveCompactDyadicEndpoint n <= 2 := by
    grind [Rat.sub_eq_add_neg]
  calc
    1 - projectiveCompactDyadicEndpoint n * projectiveCompactDyadicEndpoint n =
        (1 - projectiveCompactDyadicEndpoint n) *
          (1 + projectiveCompactDyadicEndpoint n) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
    _ <= (1 - projectiveCompactDyadicEndpoint n) * 2 :=
        Rat.mul_le_mul_of_nonneg_left hfactor hwidth
    _ = 2 * (1 / (((2 ^ n : Nat) : Rat))) := by
        dsimp [projectiveCompactDyadicEndpoint]
        grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

/-- Beyond the first compact stage, the reciprocal projective endpoint is
dyadically small.  This is the rational radius that will bound the remaining
Cauchy tail after reciprocal folding. -/
theorem projectiveCompactDyadicCauchyTailRadius_le (n : Nat) :
    1 / projectiveCompactCoordinate
        (projectiveCompactDyadicEndpoint (n + 1)) <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
  let s : Rat := projectiveCompactDyadicEndpoint (n + 1)
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hs_half : (1 : Rat) / 2 <= s := by
    simpa [s] using projectiveCompactDyadicEndpoint_succ_ge_half n
  have hspos : 0 < s := by
    have hhalfpos : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hsinv : s⁻¹ <= 2 := by
    apply Rat.le_of_mul_le_mul_right (c := s)
    · calc
        s⁻¹ * s = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hspos)
        _ = 2 * ((1 : Rat) / 2) := by decide +kernel
        _ <= 2 * s :=
          Rat.mul_le_mul_of_nonneg_left hs_half (by decide +kernel)
    · exact hspos
  have hdenpos : 0 < 1 - s * s := by
    dsimp [s]
    exact projectiveCompactDenominator_pos (by grind)
      (projectiveCompactDyadicEndpoint_lt_one _)
  have hscale :
      2 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) = 1 / D := by
    have hpow : (((2 ^ (n + 1) : Nat) : Rat)) = D * 2 := by
      dsimp [D]
      exact_mod_cast (by simpa using (Nat.pow_succ 2 n))
    have hDpos : 0 < D := by
      dsimp [D]
      exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
    rw [hpow]
    repeat rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hden : 1 - s * s <= 1 / D := by
    have h := projectiveCompactDyadicEndpoint_denominator_le (n + 1)
    dsimp [s]
    rw [hscale] at h
    exact h
  rw [projectiveCompactCoordinate_reciprocal]
  change (1 - s * s) / s <= 2 * (1 / D)
  rw [Rat.div_def]
  calc
    (1 - s * s) * s⁻¹ <= (1 - s * s) * 2 :=
      Rat.mul_le_mul_of_nonneg_left hsinv (Rat.le_of_lt hdenpos)
    _ <= (1 / D) * 2 :=
      Rat.mul_le_mul_of_nonneg_right hden (by decide +kernel)
    _ = 2 * (1 / D) := by grind [Rat.mul_comm]

/-- The compact-side coordinate at stage `n+2`, inverted back to the unit
interval.  Starting two stages in makes this a genuine rational tail start in
`(0,1]`, while retaining the dyadic tail-radius estimate. -/
def projectiveCompactDyadicCauchyTailStart (n : Nat) : Rat :=
  1 / projectiveCompactCoordinate
    (projectiveCompactDyadicEndpoint (n + 2))

theorem projectiveCompactDyadicCauchyTailStart_pos (n : Nat) :
    0 < projectiveCompactDyadicCauchyTailStart n := by
  have hhalf : (1 : Rat) / 2 <= projectiveCompactDyadicEndpoint (n + 2) := by
    simpa [Nat.add_assoc] using
      projectiveCompactDyadicEndpoint_succ_ge_half (n + 1)
  have hs : 0 < projectiveCompactDyadicEndpoint (n + 2) := by
    have hhalfpos : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hden : 0 < 1 - projectiveCompactDyadicEndpoint (n + 2) *
      projectiveCompactDyadicEndpoint (n + 2) := by
    apply projectiveCompactDenominator_pos
    · grind
    · exact projectiveCompactDyadicEndpoint_lt_one _
  unfold projectiveCompactDyadicCauchyTailStart
  rw [projectiveCompactCoordinate_reciprocal]
  rw [Rat.div_def]
  exact Rat.mul_pos hden ((Rat.inv_pos).2 hs)

theorem projectiveCompactDyadicCauchyTailStart_le_one (n : Nat) :
    projectiveCompactDyadicCauchyTailStart n <= 1 := by
  have htail : projectiveCompactDyadicCauchyTailStart n <=
      2 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
    simpa [projectiveCompactDyadicCauchyTailStart, Nat.add_assoc] using
      projectiveCompactDyadicCauchyTailRadius_le (n + 1)
  have hpow : 2 <= 2 ^ (n + 1) := by
    calc
      2 = 1 * 2 := by omega
      _ <= 2 ^ n * 2 :=
        Nat.mul_le_mul_right 2 (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
      _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]
  have hinv : 1 / (((2 ^ (n + 1) : Nat) : Rat)) <= (1 : Rat) / 2 :=
    FTC.one_div_nat_antitone (by omega : 0 < 2)
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  calc
    projectiveCompactDyadicCauchyTailStart n <=
        2 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := htail
    _ <= 2 * ((1 : Rat) / 2) :=
      Rat.mul_le_mul_of_nonneg_left hinv (by decide +kernel)
    _ = 1 := by decide +kernel

/-- The compact tail start itself decays at the dyadic rate needed to recover
the omitted near-zero unit interval in the full Cauchy comparison. -/
theorem projectiveCompactDyadicCauchyTailStart_le_dyadic (n : Nat) :
    projectiveCompactDyadicCauchyTailStart n <=
      2 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
  simpa [projectiveCompactDyadicCauchyTailStart, Nat.add_assoc] using
    projectiveCompactDyadicCauchyTailRadius_le (n + 1)

/-- The refined reciprocal tail mesh reaches exactly from `1` to the finite
projective coordinate of the dyadic compact endpoint. -/
theorem projectiveCompactDyadicCauchyTailIntervals_covers
    (n mesh : Nat) :
    ArctanGeometry.CoversInterval 1
      (projectiveCompactCoordinate (projectiveCompactDyadicEndpoint (n + 2)))
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals (projectiveCompactDyadicCauchyTailStart n)
          mesh)) := by
  have h := cauchyReciprocalTailDyadicIntervals_covers
    (projectiveCompactDyadicCauchyTailStart_pos n)
    (projectiveCompactDyadicCauchyTailStart_le_one n) mesh
  have hrecip : 1 / projectiveCompactDyadicCauchyTailStart n =
      projectiveCompactCoordinate (projectiveCompactDyadicEndpoint (n + 2)) := by
    unfold projectiveCompactDyadicCauchyTailStart
    simp only [Rat.div_def, Rat.one_mul, Rat.inv_inv]
  rw [hrecip] at h
  exact h

/-- The projective dyadic reciprocal tail has the same finite Cauchy
rectangle value, up to its certified overlapping lower/upper brackets, as
its compact-side source tail. -/
theorem projectiveCompactDyadicCauchyTailIntervals_overlaps
    (n mesh : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (cauchyReciprocalReversedIntervals
          (cauchyTailDyadicIntervals
            (projectiveCompactDyadicCauchyTailStart n) mesh)))
      (ArctanGeometry.integralSumInterval
        (cauchyTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) mesh)) := by
  exact cauchyReciprocalTailDyadicIntervals_overlaps
    (projectiveCompactDyadicCauchyTailStart_pos n)
    (projectiveCompactDyadicCauchyTailStart_le_one n) mesh

/-- Appending the unit Cauchy mesh to the projective reciprocal tail gives a
single explicit positive-side Cauchy cover from `0` to the compact chart's
finite endpoint. -/
theorem projectiveCompactDyadicCauchyAssemblyIntervals_covers
    (n mesh : Nat) :
    ArctanGeometry.CoversInterval 0
      (projectiveCompactCoordinate (projectiveCompactDyadicEndpoint (n + 2)))
      (cauchyUnitReciprocalTailDyadicIntervals
        (projectiveCompactDyadicCauchyTailStart n) mesh) := by
  have h := cauchyUnitReciprocalTailDyadicIntervals_covers
    (projectiveCompactDyadicCauchyTailStart_pos n)
    (projectiveCompactDyadicCauchyTailStart_le_one n) mesh
  have hrecip : 1 / projectiveCompactDyadicCauchyTailStart n =
      projectiveCompactCoordinate (projectiveCompactDyadicEndpoint (n + 2)) := by
    unfold projectiveCompactDyadicCauchyTailStart
    simp only [Rat.div_def, Rat.one_mul, Rat.inv_inv]
  rw [hrecip] at h
  exact h

/-- At the dyadic endpoint, the projective denominator retains at least one
dyadic unit of clearance from zero. -/
theorem projectiveCompactDyadicEndpoint_denominator_ge (n : Nat) :
    1 / (((2 ^ n : Nat) : Rat)) <=
      1 - projectiveCompactDyadicEndpoint n * projectiveCompactDyadicEndpoint n := by
  let t : Rat := 1 / (((2 ^ n : Nat) : Rat))
  have htpos : 0 < t := by
    dsimp [t]
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))))
  have htone : t <= 1 := by
    change 1 / (((2 ^ n : Nat) : Rat)) <= 1
    let D : Rat := ((2 ^ n : Nat) : Rat)
    have hDpos : 0 < D := by
      dsimp [D]
      exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
    have hDge : 1 <= D := by
      dsimp [D]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))))
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := D)
    · calc
        (1 * D⁻¹) * D = 1 := by
          rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos), Rat.mul_one]
        _ <= 1 * D := by simpa using hDge
    · exact hDpos
  have hfactor : 1 <= 2 - t := by grind
  have hmul : t * 1 <= t * (2 - t) :=
    Rat.mul_le_mul_of_nonneg_left hfactor (Rat.le_of_lt htpos)
  change t <= 1 - (1 - t) * (1 - t)
  calc
    t = t * 1 := by grind
    _ <= t * (2 - t) := hmul
    _ = 1 - (1 - t) * (1 - t) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm]

/-- The reciprocal projective tail start is not merely positive: its dyadic
size is bounded below as well.  This makes it possible to refine the
reciprocal tail fast enough to control the large-coordinate cells. -/
theorem projectiveCompactDyadicCauchyTailStart_ge
    (n : Nat) :
    1 / (((2 ^ (n + 2) : Nat) : Rat)) <=
      projectiveCompactDyadicCauchyTailStart n := by
  let s : Rat := projectiveCompactDyadicEndpoint (n + 2)
  let d : Rat := 1 - s * s
  let t : Rat := 1 / (((2 ^ (n + 2) : Nat) : Rat))
  have hspos : 0 < s := by
    dsimp [s]
    have hhalf := projectiveCompactDyadicEndpoint_succ_ge_half (n + 1)
    have hhalfpos : (0 : Rat) < 1 / 2 := by decide +kernel
    simpa [Nat.add_assoc] using (by grind :
      (0 : Rat) < projectiveCompactDyadicEndpoint ((n + 1) + 1))
  have hsone : s <= 1 := by
    dsimp [s]
    exact Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one _)
  have hdin : t <= d := by
    simpa [t, d, s] using projectiveCompactDyadicEndpoint_denominator_ge (n + 2)
  have htpos : 0 < t := by
    dsimp [t]
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (Nat.pow_pos (by omega : 0 < 2))))
  have hdinv : 1 <= s⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := s)
    · calc
        1 * s = s := by grind
        _ <= 1 := hsone
        _ = s⁻¹ * s := by
          rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hspos)]
    · exact hspos
  unfold projectiveCompactDyadicCauchyTailStart
  rw [projectiveCompactCoordinate_reciprocal, Rat.div_def]
  change t <= d * s⁻¹
  calc
    t <= d := hdin
    _ = d * 1 := by grind
    _ <= d * s⁻¹ := Rat.mul_le_mul_of_nonneg_left hdinv
      (Rat.le_trans (Rat.le_of_lt htpos) hdin)

theorem projectiveCompactDyadicCauchyTailStart_inv_le
    (n : Nat) :
    1 / projectiveCompactDyadicCauchyTailStart n <=
      (((2 ^ (n + 2) : Nat) : Rat)) := by
  let D : Rat := ((2 ^ (n + 2) : Nat) : Rat)
  let t : Rat := 1 / D
  have htpos : 0 < t := by
    dsimp [t, D]
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (Nat.pow_pos (by omega : 0 < 2))))
  have h := cauchy_one_div_le_one_div_of_pos_of_le htpos
    (projectiveCompactDyadicCauchyTailStart_ge n)
  have hcancel : 1 / t = D := by
    dsimp [t]
    repeat rw [Rat.div_def]
    simp only [Rat.one_mul, Rat.inv_inv]
  rw [hcancel] at h
  simpa [D] using h

theorem projectiveCompactDyadicCauchyTailReciprocalFactor_le
    (n : Nat) :
    (1 / (projectiveCompactDyadicCauchyTailStart n *
      projectiveCompactDyadicCauchyTailStart n)) *
      (1 / (projectiveCompactDyadicCauchyTailStart n *
        projectiveCompactDyadicCauchyTailStart n)) <=
      (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) := by
  let a : Rat := projectiveCompactDyadicCauchyTailStart n
  let D : Rat := ((2 ^ (n + 2) : Nat) : Rat)
  have hinv : 1 / a <= D := by
    simpa [a, D] using projectiveCompactDyadicCauchyTailStart_inv_le n
  have hinv' : a⁻¹ <= D := by
    simpa [Rat.div_def] using hinv
  have ha : 0 < a := by
    dsimp [a]
    exact projectiveCompactDyadicCauchyTailStart_pos n
  have hinv0 : 0 <= 1 / a := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 ha))
  have hinv0' : 0 <= a⁻¹ := by
    simpa [Rat.div_def] using hinv0
  have hD0 : 0 <= D := by
    dsimp [D]
    exact (Rat.natCast_nonneg : 0 <= ((2 ^ (n + 2) : Nat) : Rat))
  have hfactor : 1 / (a * a) <= D * D := by
    rw [Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
    calc
      a⁻¹ * a⁻¹ <= D * a⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hinv' hinv0'
      _ <= D * D := Rat.mul_le_mul_of_nonneg_left hinv' hD0
  have hfactor0 : 0 <= 1 / (a * a) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos ha ha)))
  calc
    (1 / (a * a)) * (1 / (a * a)) <=
        (D * D) * (1 / (a * a)) :=
        Rat.mul_le_mul_of_nonneg_right hfactor hfactor0
    _ <= (D * D) * (D * D) :=
        Rat.mul_le_mul_of_nonneg_left hfactor
          (Rat.mul_nonneg hD0 hD0)
    _ = D * D * D * D := by
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- With a refinement stage growing faster than the inverse fourth power of
the tail start, the far-side reciprocal Cauchy bracket has an explicit
dyadically shrinking-width budget. -/
theorem projectiveCompactDyadicCauchyTail_integral_width_le
    (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8)))).width <=
      2 * ((((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat))) *
          (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) := by
  let a : Rat := projectiveCompactDyadicCauchyTailStart n
  let D : Rat := ((2 ^ (n + 2) : Nat) : Rat)
  let E : Rat := ((2 ^ (5 * n + 8) : Nat) : Rat)
  have ha : 0 < a := by
    dsimp [a]
    exact projectiveCompactDyadicCauchyTailStart_pos n
  have ha1 : a <= 1 := by
    dsimp [a]
    exact projectiveCompactDyadicCauchyTailStart_le_one n
  have hfactor : (1 / (a * a)) * (1 / (a * a)) <= D * D * D * D := by
    simpa [a, D] using projectiveCompactDyadicCauchyTailReciprocalFactor_le n
  have hfactor0 : 0 <= (1 / (a * a)) * (1 / (a * a)) := by
    rw [Rat.div_def]
    have ha2 : 0 < a * a := Rat.mul_pos ha ha
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt ((Rat.inv_pos).2 ha2)))
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt ((Rat.inv_pos).2 ha2)))
  have hgap0 : 0 <= 1 - a := by grind [Rat.sub_eq_add_neg]
  have hgap1 : 1 - a <= 1 := by grind [Rat.sub_eq_add_neg]
  have hgapsq : (1 - a) * (1 - a) <= 1 := by
    calc
      (1 - a) * (1 - a) <= (1 - a) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hgap1 hgap0
      _ = 1 - a := by grind
      _ <= 1 := hgap1
  have hEpos : 0 < E := by
    dsimp [E]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hterm : (1 - a) * (1 - a) / E <= 1 / E := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hgapsq
      (Rat.le_of_lt ((Rat.inv_pos).2 hEpos))
  have hterm0 : 0 <= (1 - a) * (1 - a) / E := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg hgap0 hgap0)
      (Rat.le_of_lt ((Rat.inv_pos).2 hEpos))
  have hD0 : 0 <= D := by
    dsimp [D]
    exact (Rat.natCast_nonneg : 0 <= ((2 ^ (n + 2) : Nat) : Rat))
  have hbase := cauchyReciprocalTailDyadicIntervals_integral_width_le
    ha ha1 (5 * n + 8)
  change (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
      (cauchyTailDyadicIntervals a (5 * n + 8)))).width <=
      2 * (D * D * D * D) * (1 / E)
  have hD4 : 0 <= D * D * D * D := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg hD0 hD0) hD0) hD0
  calc
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals a (5 * n + 8)))).width <=
        2 * ((1 / (a * a)) * (1 / (a * a)) *
          ((1 - a) * (1 - a) / E)) := by
          simpa [E] using hbase
    _ <= 2 * ((D * D * D * D) *
          ((1 - a) * (1 - a) / E)) :=
          Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_right hfactor
              hterm0)
            (by decide +kernel)
    _ <= 2 * ((D * D * D * D) * (1 / E)) :=
          Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_left hterm
              hD4)
            (by decide +kernel)
    _ = 2 * (D * D * D * D) * (1 / E) := by
          grind [Rat.mul_assoc]

private theorem projectiveCompactDyadicCauchyTail_schedule_algebra
    (n : Nat) :
    (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
        (((2 ^ (n + 2) : Nat) : Rat)) *
          (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) =
      1 / (((2 ^ n : Nat) : Rat)) := by
  let D : Rat := ((2 ^ (n + 2) : Nat) : Rat)
  let E : Rat := ((2 ^ (5 * n + 8) : Nat) : Rat)
  let Q : Rat := ((2 ^ n : Nat) : Rat)
  have hpowNat : 2 ^ (5 * n + 8) = (2 ^ (n + 2)) ^ 4 * 2 ^ n := by
    calc
      2 ^ (5 * n + 8) = 2 ^ ((n + 2) * 4 + n) := by
        congr 1
        omega
      _ = 2 ^ ((n + 2) * 4) * 2 ^ n := Nat.pow_add _ _ _
      _ = (2 ^ (n + 2)) ^ 4 * 2 ^ n := by
        rw [Nat.pow_mul]
  have hD4 : D ^ 4 = D * D * D * D := by
    dsimp [D]
    simp only [Rat.pow_succ, Rat.pow_zero]
    grind [Rat.mul_assoc]
  have hE : E = (D * D * D * D) * Q := by
    rw [← hD4]
    dsimp [E, D, Q]
    exact_mod_cast hpowNat
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hD4ne : D * D * D * D ≠ 0 := by
    exact Rat.ne_of_gt (Rat.mul_pos
      (Rat.mul_pos (Rat.mul_pos hDpos hDpos) hDpos) hDpos)
  change D * D * D * D * (1 / E) = 1 / Q
  rw [hE, Rat.div_def, Rat.div_def]
  simp only [Rat.one_mul]
  calc
    D * D * D * D * ((D * D * D * D * Q)⁻¹) =
        D * D * D * D * (Q⁻¹ * (D * D * D * D)⁻¹) := by
          rw [Rat.inv_mul_rev]
    _ = D * D * D * D * ((D * D * D * D)⁻¹ * Q⁻¹) := by
          grind [Rat.mul_comm]
    _ = (D * D * D * D * (D * D * D * D)⁻¹) * Q⁻¹ := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = 1 * Q⁻¹ := by
          rw [Rat.mul_inv_cancel _ hD4ne]
    _ = Q⁻¹ := by grind

/-- At the chosen `5*n+8` refinement schedule, the far reciprocal tail has
the simple dyadic width bound needed for the eventual raw construction. -/
theorem projectiveCompactDyadicCauchyTail_integral_width_le_dyadic
    (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8)))).width <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
  have h := projectiveCompactDyadicCauchyTail_integral_width_le n
  calc
    (ArctanGeometry.integralSumInterval
      (cauchyReciprocalReversedIntervals
        (cauchyTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8)))).width <=
        2 * ((((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat))) *
            (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) := h
    _ = 2 * (1 / (((2 ^ n : Nat) : Rat)) ) := by
      rw [show 2 * ((((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat)) *
          (((2 ^ (n + 2) : Nat) : Rat))) *
            (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) =
          2 * (((((2 ^ (n + 2) : Nat) : Rat)) *
            (((2 ^ (n + 2) : Nat) : Rat)) *
            (((2 ^ (n + 2) : Nat) : Rat)) *
            (((2 ^ (n + 2) : Nat) : Rat))) *
              (1 / (((2 ^ (5 * n + 8) : Nat) : Rat)))) by
          grind [Rat.mul_assoc]]
      rw [projectiveCompactDyadicCauchyTail_schedule_algebra]

/-- The remaining endpoint cell in the dyadic projective schedule has an
explicit vanishing compact-density tail budget. -/
theorem projectiveCompactDyadicTailUpperCell_le (n : Nat) :
    projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
      ((32 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
  have hs0 : 0 <= projectiveCompactDyadicEndpoint n :=
    projectiveCompactDyadicEndpoint_nonnegative n
  have hs1 : projectiveCompactDyadicEndpoint n <= 1 :=
    Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n)
  have htail := projectiveCompactTailUpperCell_le hs0 hs1
  calc
    projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
        ((32 : Rat) / 3) * (1 - projectiveCompactDyadicEndpoint n) := htail
    _ = ((32 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
      dsimp [projectiveCompactDyadicEndpoint]
      grind [Rat.sub_eq_add_neg]

/-- A nested rational zero enclosure at the dyadic rate.  It is used only as
an explicitly certified error budget for the two projective endpoint cells. -/
def projectiveCompactDyadicZero : RealCompute where
  compute := fun n => { lo := 0, hi := 1 / (((2 ^ n : Nat) : Rat)) }

private theorem projectiveCompactDyadic_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem projectiveCompactDyadicZero_valid :
    projectiveCompactDyadicZero.Valid := by
  constructor
  · intro n
    change 0 <= 1 / (((2 ^ n : Nat) : Rat)) - 0
    have hpos : 0 < 1 / (((2 ^ n : Nat) : Rat)) :=
      one_div_nat_pos (Nat.pow_pos (by omega : 0 < 2))
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      change 0 <= 0 /\ 0 <= 1 / (((2 ^ m : Nat) : Rat)) /\
        1 / (((2 ^ m : Nat) : Rat)) <= 1 / (((2 ^ n : Nat) : Rat))
      have hpow : 2 ^ n <= 2 ^ m :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hnm
      have hnpos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
      have hmpos : 0 < 2 ^ m := Nat.pow_pos (by omega : 0 < 2)
      constructor
      · exact Rat.le_refl
      constructor
      · exact Rat.le_of_lt (one_div_nat_pos hmpos)
      · exact FTC.one_div_nat_antitone hnpos hmpos hpow
    · intro eps
      refine ⟨eps.val.den, ?_⟩
      intro n hn
      change 1 / (((2 ^ n : Nat) : Rat)) - 0 <= eps.val
      have hpow : n + 1 <= 2 ^ n := projectiveCompactDyadic_succ_le_two_pow n
      have hpowpos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
      have hsmall :
          1 / (((2 ^ n : Nat) : Rat)) <=
            1 / (((n + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone (Nat.succ_pos n) hpowpos hpow
      have hstage : eps.val.den + 1 <= n + 1 := by omega
      have hdenpos : 0 < eps.val.den + 1 := Nat.succ_pos _
      have hnatpos : 0 < n + 1 := Nat.succ_pos _
      have hbound :
          1 / (((n + 1 : Nat) : Rat)) <=
            1 / (((eps.val.den + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone hdenpos hnatpos hstage
      calc
        1 / (((2 ^ n : Nat) : Rat)) - 0 =
            1 / (((2 ^ n : Nat) : Rat)) := by grind [Rat.sub_eq_add_neg]
        _ <= 1 / (((n + 1 : Nat) : Rat)) := hsmall
        _ <= 1 / (((eps.val.den + 1 : Nat) : Rat)) := hbound
        _ <= eps.val := FTC.one_div_den_succ_le_of_pos eps.property

/-- A certified vanishing error raw for the two symmetric endpoint cells of
the dyadic projective schedule. -/
def projectiveCompactDyadicSymmetricTailError : RealCompute :=
  RealCompute.scaleRat ((64 : Rat) / 3) projectiveCompactDyadicZero

theorem projectiveCompactDyadicSymmetricTailError_valid :
    projectiveCompactDyadicSymmetricTailError.Valid :=
  RealCompute.scaleRat_valid_of_nonneg (by decide +kernel)
    projectiveCompactDyadicZero_valid

theorem projectiveCompactDyadicSymmetricTailError_compute (n : Nat) :
    projectiveCompactDyadicSymmetricTailError.compute n =
      { lo := 0,
        hi := ((64 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) } := by
  have hnonneg : (0 : Rat) <= (64 : Rat) / 3 := by decide +kernel
  simp [projectiveCompactDyadicSymmetricTailError, projectiveCompactDyadicZero,
    RealCompute.scaleRat, RealCompute.scaleRatCompute, hnonneg]

/-- The two compact endpoint-cell budgets are absorbed by the certified
vanishing tail raw at every dyadic stage. -/
theorem projectiveCompactDyadicSymmetricTailUpper_le (n : Nat) :
    2 * projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
      (projectiveCompactDyadicSymmetricTailError.compute n).hi := by
  rw [projectiveCompactDyadicSymmetricTailError_compute]
  have htail := projectiveCompactDyadicTailUpperCell_le n
  calc
    2 * projectiveCompactTailUpperCell (projectiveCompactDyadicEndpoint n) <=
        2 * (((32 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat)))) :=
      Rat.mul_le_mul_of_nonneg_left htail (by decide +kernel)
    _ = ((64 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
      grind [Rat.mul_assoc]

private theorem projectiveCompact_one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

/-- The projective Lipschitz coefficient along the dyadic endpoint schedule
has a purely dyadic upper bound. -/
theorem projectiveCompactDyadic_lipschitzFactor_le (n : Nat) :
    2 / ((1 - projectiveCompactDyadicEndpoint n *
      projectiveCompactDyadicEndpoint n) *
        (1 - projectiveCompactDyadicEndpoint n *
          projectiveCompactDyadicEndpoint n)) <=
      2 * (((2 ^ n : Nat) : Rat)) * (((2 ^ n : Nat) : Rat)) := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  let t : Rat := 1 / D
  let d : Rat := 1 - projectiveCompactDyadicEndpoint n *
    projectiveCompactDyadicEndpoint n
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have htpos : 0 < t := by
    dsimp [t]
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel) ((Rat.inv_pos).2 hDpos)
  have htd : t <= d := by
    simpa [t, d, D] using projectiveCompactDyadicEndpoint_denominator_ge n
  have hdpos : 0 < d := by grind
  have hsq : t * t <= d * d := by
    calc
      t * t <= d * t := Rat.mul_le_mul_of_nonneg_right htd (Rat.le_of_lt htpos)
      _ <= d * d := Rat.mul_le_mul_of_nonneg_left htd (Rat.le_of_lt hdpos)
  have hsqpos : 0 < t * t := Rat.mul_pos htpos htpos
  have hinv : 1 / (d * d) <= 1 / (t * t) :=
    projectiveCompact_one_div_le_one_div_of_pos_of_le hsqpos hsq
  have htinv : 1 / (t * t) = D * D := by
    dsimp [t]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : D⁻¹ * D = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)
    grind [Rat.mul_assoc, Rat.mul_comm]
  change 2 / (d * d) <= 2 * D * D
  rw [Rat.div_def]
  calc
    2 * (d * d)⁻¹ = 2 * (1 / (d * d)) := by
      simp [Rat.div_def]
    _ <= 2 * (1 / (t * t)) :=
      Rat.mul_le_mul_of_nonneg_left hinv (by decide +kernel)
    _ = 2 * D * D := by
      rw [htinv]
      grind [Rat.mul_assoc]

private theorem projectiveCompact_dyadic_mesh_algebra
    (D : Rat) (hD : D ≠ 0) :
    (2 * D * D) * (2 * D * D) * (1 / (D ^ 6)) = 4 / (D ^ 2) := by
  have hcancel : D * D⁻¹ = 1 := Rat.mul_inv_cancel D hD
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- An explicit projective quadrature schedule whose transported squared mesh
shrinks at the dyadic rate `4 / 2^(2n)`.  The source endpoint is
`1 - 2^(-n)` and the source partition receives `6n` midpoint refinements,
which absorbs the fourth-order blowup of the chart derivative near its pole. -/
theorem projectiveCompactDyadic_schedule_squareSum_le (n : Nat) :
    ArctanGeometry.intervalSquareSum
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals) <=
      4 / (((2 ^ (n * 2) : Nat) : Rat)) := by
  let s : Rat := projectiveCompactDyadicEndpoint n
  let D : Rat := ((2 ^ n : Nat) : Rat)
  let d : Rat := 1 - s * s
  let L : Rat := 2 / (d * d)
  let R : Rat := 2 * D * D
  let Q : Rat := ((2 ^ (n * 6) : Nat) : Rat)
  have hs0 : 0 <= s := by
    simpa [s] using projectiveCompactDyadicEndpoint_nonnegative n
  have hslt : s < 1 := by
    simpa [s] using projectiveCompactDyadicEndpoint_lt_one n
  have hsone : s <= 1 := Rat.le_of_lt hslt
  have hd : 0 < d := by
    dsimp [d, s]
    exact projectiveCompactDenominator_pos (by grind) hslt
  have hL0 : 0 <= L := by
    dsimp [L]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hd hd)))
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hR0 : 0 <= R := by
    dsimp [R]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hDpos))
      (Rat.le_of_lt hDpos)
  have hLle : L <= R := by
    simpa [L, d, s, R, D] using projectiveCompactDyadic_lipschitzFactor_le n
  have hLL : L * L <= R * R := by
    calc
      L * L <= R * L := Rat.mul_le_mul_of_nonneg_right hLle hL0
      _ <= R * R := Rat.mul_le_mul_of_nonneg_left hLle hR0
  have hsq0 : 0 <= s * s := Rat.mul_nonneg hs0 hs0
  have hsqle : s * s <= 1 := by
    calc
      s * s <= 1 * s := Rat.mul_le_mul_of_nonneg_right hsone hs0
      _ <= 1 := by grind
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hsource : 0 <= s * s / Q := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hsq0 (Rat.le_of_lt ((Rat.inv_pos).2 hQpos))
  have hquot : s * s / Q <= 1 / Q := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hsqle
      (Rat.le_of_lt ((Rat.inv_pos).2 hQpos))
  have hpow6 : Q = D ^ 6 := by
    dsimp [Q, D]
    exact_mod_cast (Nat.pow_mul 2 n 6)
  have hpow2 : (((2 ^ (n * 2) : Nat) : Rat)) = D ^ 2 := by
    dsimp [D]
    exact_mod_cast (Nat.pow_mul 2 n 2)
  have hbase := projectiveCompactAreaLoop_squareSum_le hs0 hslt (n * 6)
  calc
    ArctanGeometry.intervalSquareSum
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals) =
        ArctanGeometry.intervalSquareSum
          (projectiveCompactIntervals
            (ArctanGeometry.arctanAreaLoopState s (n * 6)).intervals) := by
          rfl
    _ <= L * L * (s * s / Q) := by
      simpa [L, d, Q] using hbase
    _ <= R * R * (s * s / Q) :=
      Rat.mul_le_mul_of_nonneg_right hLL hsource
    _ <= R * R * (1 / Q) :=
      Rat.mul_le_mul_of_nonneg_left hquot (Rat.mul_nonneg hR0 hR0)
    _ = 4 / (((2 ^ (n * 2) : Nat) : Rat)) := by
      rw [hpow6, hpow2]
      exact projectiveCompact_dyadic_mesh_algebra D (Rat.ne_of_gt hDpos)

/-- The scheduled positive projective Cauchy core has a directly certified
shrinking Cauchy rectangle width.  Unlike the literal compact candidate mesh,
this schedule refines fast enough near the chart endpoint. -/
theorem projectiveCompactDyadicCauchyCore_integral_width_le (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals)).width <=
      8 / (((2 ^ (n * 2) : Nat) : Rat)) := by
  let s : Rat := projectiveCompactDyadicEndpoint n
  let intervals : List (Rat × Rat) :=
    (ArctanGeometry.arctanAreaLoopState s (n * 6)).intervals
  have hs0 : 0 <= s := by
    dsimp [s]
    exact projectiveCompactDyadicEndpoint_nonnegative n
  have hslt : s < 1 := by
    dsimp [s]
    exact projectiveCompactDyadicEndpoint_lt_one n
  have hcover : ArctanGeometry.CoversInterval 0 s intervals := by
    dsimp [intervals]
    exact ArctanGeometry.arctanAreaLoopState_intervals_covers hs0 (n * 6)
  have hnonnegative : ArctanGeometry.NonnegativeIntervals
      (projectiveCompactIntervals intervals) :=
    projectiveCompactIntervals_nonnegative 0 s intervals (by decide +kernel)
      hslt hcover
  calc
    (ArctanGeometry.integralSumInterval
      (projectiveCompactIntervals intervals)).width <=
        2 * ArctanGeometry.intervalSquareSum
          (projectiveCompactIntervals intervals) :=
      cauchyIntegralSumInterval_width_le_two_squareSum _ hnonnegative
    _ <= 2 * (4 / (((2 ^ (n * 2) : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left
        (by simpa [intervals, s] using
          projectiveCompactDyadic_schedule_squareSum_le n)
        (by decide +kernel)
    _ = 8 / (((2 ^ (n * 2) : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]

/-- The rapidly refined projective Cauchy core and the explicit unit-plus-
reciprocal-tail assembly cover the same finite positive Cauchy interval. -/
theorem projectiveCompactDyadicScheduledCore_overlaps_cauchyAssembly
    (n mesh : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals))
      (ArctanGeometry.integralSumInterval
        (cauchyUnitReciprocalTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) mesh)) := by
  have hsource := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (projectiveCompactDyadicEndpoint_nonnegative (n + 2)) ((n + 2) * 6)
  have hcore := projectiveCompactIntervals_covers 0
    (projectiveCompactDyadicEndpoint (n + 2))
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
    (by decide +kernel) (projectiveCompactDyadicEndpoint_lt_one _) hsource
  have hzero : projectiveCompactCoordinate (0 : Rat) = 0 := by
    decide +kernel
  rw [hzero] at hcore
  exact ArctanGeometry.integralSumInterval_overlaps_of_covers
    (by decide +kernel) _ _ hcore
    (projectiveCompactDyadicCauchyAssemblyIntervals_covers n mesh)

/-- The full positive Cauchy assembly (unit mesh plus reciprocal tail) is
itself a shrinking rectangle bracket when the tail is refined at `5*n+8`. -/
theorem projectiveCompactDyadicCauchyAssembly_integral_width_le
    (n : Nat) :
    (ArctanGeometry.integralSumInterval
      (cauchyUnitReciprocalTailDyadicIntervals
        (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8))).width <=
      4 * (1 / (((2 ^ n : Nat) : Rat))) := by
  let stage : Nat := 5 * n + 8
  let unit : List (Rat × Rat) :=
    (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  let tail : List (Rat × Rat) :=
    cauchyReciprocalReversedIntervals
      (cauchyTailDyadicIntervals
        (projectiveCompactDyadicCauchyTailStart n) stage)
  have hunit : ArctanGeometry.UnitIntervals unit := by
    dsimp [unit]
    exact ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by decide +kernel) (by decide +kernel) stage
  have hunitWidth : (ArctanGeometry.integralSumInterval unit).width <=
      2 * (1 / (((2 ^ stage : Nat) : Rat))) := by
    calc
      (ArctanGeometry.integralSumInterval unit).width <=
          2 * ArctanGeometry.intervalSquareSum unit :=
        ArctanGeometry.integralSumInterval_width_le_two_squareSum _ hunit
      _ = 2 * (1 / (((2 ^ stage : Nat) : Rat))) := by
        dsimp [unit]
        rw [ArctanGeometry.arctanAreaLoopState_squareSum]
        simp only [Rat.one_mul]
  have htailWidth : (ArctanGeometry.integralSumInterval tail).width <=
      2 * (1 / (((2 ^ n : Nat) : Rat))) := by
    dsimp [tail, stage]
    exact projectiveCompactDyadicCauchyTail_integral_width_le_dyadic n
  have hstage : n <= stage := by
    dsimp [stage]
    omega
  have hpow : 2 ^ n <= 2 ^ stage :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hstage
  have hsmall : 1 / (((2 ^ stage : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    FTC.one_div_nat_antitone (Nat.pow_pos (by omega : 0 < 2))
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  change (ArctanGeometry.integralSumInterval (unit ++ tail)).width <=
    4 * (1 / (((2 ^ n : Nat) : Rat)))
  rw [cauchyIntegralSumInterval_width_append]
  calc
    (ArctanGeometry.integralSumInterval unit).width +
          (ArctanGeometry.integralSumInterval tail).width <=
        2 * (1 / (((2 ^ stage : Nat) : Rat))) +
          2 * (1 / (((2 ^ n : Nat) : Rat))) :=
          rat_add_le_add hunitWidth htailWidth
    _ <= 2 * (1 / (((2 ^ n : Nat) : Rat))) +
          2 * (1 / (((2 ^ n : Nat) : Rat))) :=
          rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left hsmall (by decide +kernel))
            Rat.le_refl
    _ = 4 * (1 / (((2 ^ n : Nat) : Rat))) := by
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc]

/-- The two finite Cauchy calculations on the scheduled projective core and
on the unit-plus-reciprocal-tail assembly are enclosed together in one
explicit rational interval. -/
def projectiveCompactDyadicScheduledCauchyBridgeEnvelope (n : Nat) : QInterval :=
  QInterval.hull
    (ArctanGeometry.integralSumInterval
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals))
    (ArctanGeometry.integralSumInterval
      (cauchyUnitReciprocalTailDyadicIntervals
        (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8)))

theorem projectiveCompactDyadicScheduledCauchyBridgeEnvelope_contains_core
    (n : Nat) :
    (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).ContainsInterval
      (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)) :=
  QInterval.hull_contains_left _ _

theorem projectiveCompactDyadicScheduledCauchyBridgeEnvelope_contains_assembly
    (n : Nat) :
    (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).ContainsInterval
      (ArctanGeometry.integralSumInterval
        (cauchyUnitReciprocalTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8))) :=
  QInterval.hull_contains_right _ _

/-- The common scheduled Cauchy envelope has a dyadically vanishing width. -/
theorem projectiveCompactDyadicScheduledCauchyBridgeEnvelope_width_le
    (n : Nat) :
    (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).width <=
      12 * (1 / (((2 ^ n : Nat) : Rat))) := by
  let core : List (Rat × Rat) := projectiveCompactIntervals
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
  let assembly : List (Rat × Rat) :=
    cauchyUnitReciprocalTailDyadicIntervals
      (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8)
  have hsource := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (projectiveCompactDyadicEndpoint_nonnegative (n + 2)) ((n + 2) * 6)
  have hcoreNonnegative : ArctanGeometry.NonnegativeIntervals core := by
    dsimp [core]
    exact projectiveCompactIntervals_nonnegative 0
      (projectiveCompactDyadicEndpoint (n + 2)) _ (by decide +kernel)
      (projectiveCompactDyadicEndpoint_lt_one _) hsource
  have hassemblyCover := projectiveCompactDyadicCauchyAssemblyIntervals_covers
    n (5 * n + 8)
  have hassemblyNonnegative : ArctanGeometry.NonnegativeIntervals assembly := by
    dsimp [assembly]
    exact ArctanGeometry.CoversInterval.nonnegative (by decide +kernel)
      hassemblyCover
  have hcoreOrdered := ArctanGeometry.integralSumInterval_ordered core
    hcoreNonnegative
  have hassemblyOrdered := ArctanGeometry.integralSumInterval_ordered assembly
    hassemblyNonnegative
  have hover : QInterval.Overlaps
      (ArctanGeometry.integralSumInterval core)
      (ArctanGeometry.integralSumInterval assembly) := by
    dsimp [core, assembly]
    exact projectiveCompactDyadicScheduledCore_overlaps_cauchyAssembly
      n (5 * n + 8)
  have hcoreWidth : (ArctanGeometry.integralSumInterval core).width <=
      8 * (1 / (((2 ^ ((n + 2) * 2) : Nat) : Rat))) := by
    dsimp [core]
    calc
      (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)).width <=
          8 / (((2 ^ ((n + 2) * 2) : Nat) : Rat)) :=
        projectiveCompactDyadicCauchyCore_integral_width_le (n + 2)
      _ = 8 * (1 / (((2 ^ ((n + 2) * 2) : Nat) : Rat))) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
  have hassemblyWidth : (ArctanGeometry.integralSumInterval assembly).width <=
      4 * (1 / (((2 ^ n : Nat) : Rat))) := by
    dsimp [assembly]
    exact projectiveCompactDyadicCauchyAssembly_integral_width_le n
  have hstage : n <= (n + 2) * 2 := by omega
  have hpow : 2 ^ n <= 2 ^ ((n + 2) * 2) :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hstage
  have hsmall : 1 / (((2 ^ ((n + 2) * 2) : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    FTC.one_div_nat_antitone (Nat.pow_pos (by omega : 0 < 2))
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  change (QInterval.hull
    (ArctanGeometry.integralSumInterval core)
    (ArctanGeometry.integralSumInterval assembly)).width <=
      12 * (1 / (((2 ^ n : Nat) : Rat)))
  calc
    (QInterval.hull
      (ArctanGeometry.integralSumInterval core)
      (ArctanGeometry.integralSumInterval assembly)).width <=
        (ArctanGeometry.integralSumInterval core).width +
          (ArctanGeometry.integralSumInterval assembly).width :=
      QInterval.hull_width_le_add_of_overlaps hcoreOrdered hassemblyOrdered hover
    _ <= 8 * (1 / (((2 ^ ((n + 2) * 2) : Nat) : Rat))) +
          4 * (1 / (((2 ^ n : Nat) : Rat))) :=
      rat_add_le_add hcoreWidth hassemblyWidth
    _ <= 8 * (1 / (((2 ^ n : Nat) : Rat))) +
          4 * (1 / (((2 ^ n : Nat) : Rat))) :=
      rat_add_le_add
        (Rat.mul_le_mul_of_nonneg_left hsmall (by decide +kernel)) Rat.le_refl
    _ = 12 * (1 / (((2 ^ n : Nat) : Rat))) := by
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc]

/-- Exact left-endpoint secant expansion for the compact projective chart.
The displayed remainder is nonnegative on the positive compact branch, so
this is the finite rational replacement for the lower derivative bound used
in a change-of-variables argument. -/
theorem projectiveCompactCoordinate_sub_eq_leftJacobian_add
    (p r : Rat) (hp : 1 - p * p ≠ 0) (hr : 1 - r * r ≠ 0) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p =
      projectiveCompactJacobian p * (r - p) +
        ((r - p) * (r - p) *
          (3 * p + p * p * p + (r - p) * (1 + p * p))) /
          (((1 - p * p) * (1 - p * p)) * (1 - r * r)) := by
  let dp : Rat := 1 - p * p
  let dr : Rat := 1 - r * r
  let E : Rat := 3 * p + p * p * p + (r - p) * (1 + p * p)
  have hdp : dp ≠ 0 := by simpa [dp] using hp
  have hdr : dr ≠ 0 := by simpa [dr] using hr
  have hdp2 : dp * dp ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hdp hzero
    · exact hdp hzero
  have hden : dp * dp * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdp hzero
      · exact hdp hzero
    · exact hdr hzero
  have hdp_cancel : dp * dp⁻¹ = 1 := Rat.mul_inv_cancel dp hdp
  have hdr_cancel : dr * dr⁻¹ = 1 := Rat.mul_inv_cancel dr hdr
  have hdp2_cancel : (dp * dp) * (dp * dp)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdp2
  have hden_cancel : (dp * dp * dr) * (dp * dp * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hden
  have hcleared : (r / dr - p / dp) * (dr * dp) =
      (r - p) * (1 + p * r) := by
    simpa [projectiveCompactCoordinate, dp, dr] using
      projectiveCompactCoordinate_sub_cleared p r hp hr
  have hpoly : (1 + p * r) * dp = (1 + p * p) * dr + (r - p) * E := by
    dsimp [dp, dr, E]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hright :
      (((1 + p * p) / (dp * dp)) * (r - p) +
        ((r - p) * (r - p) * E) / (dp * dp * dr)) * (dp * dp * dr) =
        ((1 + p * p) * dr) * (r - p) + (r - p) * (r - p) * E := by
    simp only [Rat.div_def]
    rw [Rat.add_mul]
    have hdp2_inv : (dp * dp)⁻¹ * (dp * dp) = 1 :=
      Rat.inv_mul_cancel _ hdp2
    have hden_inv : (dp * dp * dr)⁻¹ * (dp * dp * dr) = 1 :=
      Rat.inv_mul_cancel _ hden
    congr 1
    · calc
        (((1 + p * p) * (dp * dp)⁻¹) * (r - p)) * (dp * dp * dr) =
            ((1 + p * p) * (r - p)) * ((dp * dp)⁻¹ * (dp * dp) * dr) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ = ((1 + p * p) * dr) * (r - p) := by
              rw [hdp2_inv]
              simp
              grind [Rat.mul_assoc, Rat.mul_comm]
    · calc
        ((r - p) * (r - p) * E * (dp * dp * dr)⁻¹) * (dp * dp * dr) =
            (r - p) * (r - p) * E *
              ((dp * dp * dr)⁻¹ * (dp * dp * dr)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ = (r - p) * (r - p) * E := by rw [hden_inv, Rat.mul_one]
  unfold projectiveCompactCoordinate projectiveCompactJacobian
  change r / dr - p / dp =
    ((1 + p * p) / (dp * dp)) * (r - p) +
      ((r - p) * (r - p) * E) /
        (dp * dp * dr)
  apply rat_eq_of_mul_eq_mul_ne (c := dp * dp * dr) hden
  calc
    (r / dr - p / dp) * (dp * dp * dr) =
        ((r / dr - p / dp) * (dr * dp)) * dp := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = ((r - p) * (1 + p * r)) * dp := by rw [hcleared]
    _ = (r - p) * ((1 + p * r) * dp) := by rw [Rat.mul_assoc]
    _ = (r - p) * ((1 + p * p) * dr + (r - p) * E) := by rw [hpoly]
    _ = ((1 + p * p) * dr) * (r - p) + (r - p) * (r - p) * E := by
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    _ = (((1 + p * p) / (dp * dp)) * (r - p) +
        ((r - p) * (r - p) * E) / (dp * dp * dr)) * (dp * dp * dr) :=
      hright.symm

/-- On the nonnegative compact chart branch, the projective secant is at
least its left endpoint Jacobian times the source-cell width. -/
theorem projectiveCompactJacobian_left_mul_le_coordinate_sub
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    projectiveCompactJacobian p * (r - p) <=
      projectiveCompactCoordinate r - projectiveCompactCoordinate p := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hfactor : 0 <=
      3 * p + p * p * p + (r - p) * (1 + p * p) := by
    have hp3 : 0 <= p * p * p :=
      Rat.mul_nonneg (Rat.mul_nonneg hp0 hp0) hp0
    have htail : 0 <= (r - p) * (1 + p * p) :=
      Rat.mul_nonneg hwidth (by
        have hsq : 0 <= p * p := Rat.mul_nonneg hp0 hp0
        grind)
    exact Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) hp0) hp3)
      htail
  have hrem : 0 <=
      ((r - p) * (r - p) *
        (3 * p + p * p * p + (r - p) * (1 + p * p))) /
        (((1 - p * p) * (1 - p * p)) * (1 - r * r)) := by
    rw [Rat.div_def]
    apply Rat.mul_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg hwidth hwidth) hfactor
    · exact Rat.le_of_lt ((Rat.inv_pos).2
        (Rat.mul_pos (Rat.mul_pos hdp hdp) hdr))
  rw [projectiveCompactCoordinate_sub_eq_leftJacobian_add p r
    (Rat.ne_of_gt hdp) (Rat.ne_of_gt hdr)]
  grind [Rat.sub_eq_add_neg]

/-- Exact right-endpoint secant expansion for the compact projective chart.
Its remainder is again nonnegative on the positive compact branch. -/
theorem projectiveCompactCoordinate_sub_eq_rightJacobian_sub
    (p r : Rat) (hp : 1 - p * p ≠ 0) (hr : 1 - r * r ≠ 0) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p =
      projectiveCompactJacobian r * (r - p) -
        ((r - p) * (r - p) *
          (3 * r + r * r * r - (r - p) * (1 + r * r))) /
          (((1 - p * p) * (1 - r * r)) * (1 - r * r)) := by
  let dp : Rat := 1 - p * p
  let dr : Rat := 1 - r * r
  let E : Rat := 3 * r + r * r * r - (r - p) * (1 + r * r)
  have hdp : dp ≠ 0 := by simpa [dp] using hp
  have hdr : dr ≠ 0 := by simpa [dr] using hr
  have hdr2 : dr * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hdr hzero
    · exact hdr hzero
  have hden : dp * dr * dr ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdp hzero
      · exact hdr hzero
    · exact hdr hzero
  have hdp_cancel : dp * dp⁻¹ = 1 := Rat.mul_inv_cancel dp hdp
  have hdr_cancel : dr * dr⁻¹ = 1 := Rat.mul_inv_cancel dr hdr
  have hdr2_cancel : (dr * dr) * (dr * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdr2
  have hden_cancel : (dp * dr * dr) * (dp * dr * dr)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hden
  have hcleared : (r / dr - p / dp) * (dr * dp) =
      (r - p) * (1 + p * r) := by
    simpa [projectiveCompactCoordinate, dp, dr] using
      projectiveCompactCoordinate_sub_cleared p r hp hr
  have hpoly : (1 + p * r) * dr = (1 + r * r) * dp - (r - p) * E := by
    dsimp [dp, dr, E]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hright :
      (((1 + r * r) / (dr * dr)) * (r - p) -
        ((r - p) * (r - p) * E) / (dp * dr * dr)) * (dp * dr * dr) =
        ((1 + r * r) * dp) * (r - p) - (r - p) * (r - p) * E := by
    simp only [Rat.div_def, Rat.sub_eq_add_neg]
    rw [Rat.add_mul, Rat.neg_mul]
    have hdr2_inv : (dr * dr)⁻¹ * (dr * dr) = 1 :=
      Rat.inv_mul_cancel _ hdr2
    have hden_inv : (dp * dr * dr)⁻¹ * (dp * dr * dr) = 1 :=
      Rat.inv_mul_cancel _ hden
    congr 1
    · calc
        (((1 + r * r) * (dr * dr)⁻¹) * (r + -p)) * (dp * dr * dr) =
            ((1 + r * r) * (r + -p)) * ((dr * dr)⁻¹ * (dr * dr) * dp) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ = ((1 + r * r) * dp) * (r + -p) := by
              rw [hdr2_inv]
              simp
              grind [Rat.mul_assoc, Rat.mul_comm]
    · congr 1
      calc
        ((r + -p) * (r + -p) * E * (dp * dr * dr)⁻¹) * (dp * dr * dr) =
            (r + -p) * (r + -p) * E *
              ((dp * dr * dr)⁻¹ * (dp * dr * dr)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ = (r + -p) * (r + -p) * E := by rw [hden_inv, Rat.mul_one]
  unfold projectiveCompactCoordinate projectiveCompactJacobian
  change r / dr - p / dp =
    ((1 + r * r) / (dr * dr)) * (r - p) -
      ((r - p) * (r - p) * E) /
        (dp * dr * dr)
  apply rat_eq_of_mul_eq_mul_ne (c := dp * dr * dr) hden
  calc
    (r / dr - p / dp) * (dp * dr * dr) =
        ((r / dr - p / dp) * (dr * dp)) * dr := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = ((r - p) * (1 + p * r)) * dr := by rw [hcleared]
    _ = (r - p) * ((1 + p * r) * dr) := by rw [Rat.mul_assoc]
    _ = (r - p) * ((1 + r * r) * dp - (r - p) * E) := by rw [hpoly]
    _ = ((1 + r * r) * dp) * (r - p) - (r - p) * (r - p) * E := by
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ = (((1 + r * r) / (dr * dr)) * (r - p) -
        ((r - p) * (r - p) * E) / (dp * dr * dr)) * (dp * dr * dr) :=
      hright.symm

/-- On the nonnegative compact chart branch, the projective secant is at
most its right endpoint Jacobian times the source-cell width. -/
theorem coordinate_sub_le_projectiveCompactJacobian_right_mul
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    projectiveCompactCoordinate r - projectiveCompactCoordinate p <=
      projectiveCompactJacobian r * (r - p) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hwidth_le_r : r - p <= r := by grind
  have hr2 : 0 <= r * r := Rat.mul_nonneg (Rat.le_trans hp0 hpr)
    (Rat.le_trans hp0 hpr)
  have hrightFactor : 0 <=
      3 * r + r * r * r - (r - p) * (1 + r * r) := by
    have hr0 : 0 <= r := Rat.le_trans hp0 hpr
    have hmul : (r - p) * (1 + r * r) <= r * (1 + r * r) :=
      Rat.mul_le_mul_of_nonneg_right hwidth_le_r (by grind)
    calc
      0 <= 2 * r := Rat.mul_nonneg (by decide +kernel) hr0
      _ = (3 * r + r * r * r) - r * (1 + r * r) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
          Rat.mul_comm]
      _ <= (3 * r + r * r * r) - (r - p) * (1 + r * r) := by
        grind [Rat.sub_eq_add_neg]
  have hrem : 0 <=
      ((r - p) * (r - p) *
        (3 * r + r * r * r - (r - p) * (1 + r * r))) /
        (((1 - p * p) * (1 - r * r)) * (1 - r * r)) := by
    rw [Rat.div_def]
    apply Rat.mul_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg hwidth hwidth) hrightFactor
    · exact Rat.le_of_lt ((Rat.inv_pos).2
        (Rat.mul_pos (Rat.mul_pos hdp hdr) hdr))
  rw [projectiveCompactCoordinate_sub_eq_rightJacobian_sub p r
    (Rat.ne_of_gt hdp) (Rat.ne_of_gt hdr)]
  grind [Rat.sub_eq_add_neg]

/-- Exact rational compactification of the Cauchy density.  Away from the
two chart endpoints, the pullback of `1 / (1 + u^2)` under
`u = x / (1 - x^2)` is the everywhere-defined density
`(1 + x^2) / (x^4 - x^2 + 1)`.  This is the finite algebraic core of the
reciprocal-quartic pi route; endpoint and integral certificates remain
separate analytic work. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback
    (x : Rat) (hx : 1 - x * x ≠ 0) :
    reciprocalQuarticSymmetricDensity (-1) x =
      projectiveCompactJacobian x *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate x) := by
  let d : Rat := 1 - x * x
  let q : Rat := reciprocalQuarticDenominator (-1) x
  have hd : d ≠ 0 := by simpa [d] using hx
  have hd2 : d * d ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact hd hzero
    · exact hd hzero
  have hden : 1 + (x / d) * (x / d) = q / (d * d) := by
    apply rat_eq_of_mul_eq_mul_ne (c := d * d) hd2
    rw [Rat.div_def]
    calc
      (1 + (x / d) * (x / d)) * (d * d) = d * d + x * x := by
        have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hd
        grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ = q := by
        dsimp [d, q, reciprocalQuarticDenominator]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
          Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      _ = q * (d * d)⁻¹ * (d * d) := by
        have hcancel : (d * d) * (d * d)⁻¹ = 1 :=
          Rat.mul_inv_cancel (d * d) hd2
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hkernel : ArctanGeometry.integralKernel (x / d) = (d * d) / q := by
    unfold ArctanGeometry.integralKernel
    rw [hden]
    simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.one_mul]
  have hkernel' :
      ArctanGeometry.integralKernel (x / (1 - x * x)) =
        ((1 - x * x) * (1 - x * x)) /
          reciprocalQuarticDenominator (-1) x := by
    simpa [d, q] using hkernel
  unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
    projectiveCompactJacobian projectiveCompactCoordinate
  rw [hkernel']
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : (d * d)⁻¹ * (d * d) = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel (d * d) hd2
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The lower Lipschitz rectangle for the compact reciprocal-quartic density
on a positive chart cell lies below the upper Cauchy-kernel rectangle on its
projective image.  This is a cellwise, finite rational half of the projective
quadrature comparison. -/
theorem projectiveCompact_lipschitzLowerCell_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    (r - p) *
      (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      ArctanGeometry.integralUpperStep
        (projectiveCompactCoordinate p) (projectiveCompactCoordinate r) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hwidth : 0 <= r - p := by grind
  have hsub : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) p := by
    have herror : 0 <= 8 * (r - p) :=
      Rat.mul_nonneg (by decide +kernel) hwidth
    grind [Rat.sub_eq_add_neg]
  have hkernel : 0 <=
      ArctanGeometry.integralKernel (projectiveCompactCoordinate p) :=
    Rat.le_of_lt (ArctanGeometry.integralKernel_pos _)
  have hsecant :=
    projectiveCompactJacobian_left_mul_le_coordinate_sub hp0 hpr hr1
  have hpullback :=
    reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback p
      (Rat.ne_of_gt hdp)
  unfold ArctanGeometry.integralUpperStep
  calc
    (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      (r - p) * reciprocalQuarticSymmetricDensity (-1) p :=
        Rat.mul_le_mul_of_nonneg_left hsub hwidth
    _ = (projectiveCompactJacobian p * (r - p)) *
          ArctanGeometry.integralKernel (projectiveCompactCoordinate p) := by
        rw [hpullback]
        grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (projectiveCompactCoordinate r - projectiveCompactCoordinate p) *
          ArctanGeometry.integralKernel (projectiveCompactCoordinate p) :=
        Rat.mul_le_mul_of_nonneg_right hsecant hkernel

/-- The lower Cauchy-kernel rectangle on a positive projective image cell
lies below the upper Lipschitz rectangle for the compact reciprocal-quartic
density.  Together with the preceding theorem this gives overlap cell by
cell, without assuming a substitution theorem. -/
theorem projectiveCompact_integralLowerStep_le_lipschitzUpperCell
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r < 1) :
    ArctanGeometry.integralLowerStep
      (projectiveCompactCoordinate p) (projectiveCompactCoordinate r) <=
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
  have hp1 : p < 1 := by grind
  have hplo : -1 < p := by grind
  have hrlo : -1 < r := by grind
  have hdp : 0 < 1 - p * p := projectiveCompactDenominator_pos hplo hp1
  have hdr : 0 < 1 - r * r := projectiveCompactDenominator_pos hrlo hr1
  have hwidth : 0 <= r - p := by grind
  have hkernel : 0 <=
      ArctanGeometry.integralKernel (projectiveCompactCoordinate r) :=
    Rat.le_of_lt (ArctanGeometry.integralKernel_pos _)
  have hsecant :=
    coordinate_sub_le_projectiveCompactJacobian_right_mul hp0 hpr hr1
  have hrpullback :=
    reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback r
      (Rat.ne_of_gt hdr)
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    p r (by grind) (by grind) (by grind) (by grind)
  have hdiff : reciprocalQuarticSymmetricDensity (-1) r -
      reciprocalQuarticSymmetricDensity (-1) p <= 8 * (r - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) r -
          reciprocalQuarticSymmetricDensity (-1) p <=
        qabs (reciprocalQuarticSymmetricDensity (-1) r -
          reciprocalQuarticSymmetricDensity (-1) p) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) p -
          reciprocalQuarticSymmetricDensity (-1) r) := by
          rw [show reciprocalQuarticSymmetricDensity (-1) r -
            reciprocalQuarticSymmetricDensity (-1) p =
              -(reciprocalQuarticSymmetricDensity (-1) p -
                reciprocalQuarticSymmetricDensity (-1) r) by
                grind [Rat.sub_eq_add_neg], qabs_neg]
      _ <= 8 * qabs (r - p) := hlip
      _ = 8 * (r - p) := by
          rw [qabs_eq_self_of_nonneg hwidth]
  have hpoint : reciprocalQuarticSymmetricDensity (-1) r <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    grind [Rat.sub_eq_add_neg]
  unfold ArctanGeometry.integralLowerStep
  calc
    (projectiveCompactCoordinate r - projectiveCompactCoordinate p) *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate r) <=
      (projectiveCompactJacobian r * (r - p)) *
        ArctanGeometry.integralKernel (projectiveCompactCoordinate r) :=
        Rat.mul_le_mul_of_nonneg_right hsecant hkernel
    _ = (r - p) * reciprocalQuarticSymmetricDensity (-1) r := by
        rw [hrpullback]
        grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hwidth

/-- Finite lower Lipschitz sum for the compact reciprocal-quartic density on
a positive compact branch. -/
def projectiveCompactLipschitzLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) +
        projectiveCompactLipschitzLowerSum rest

/-- Matching finite upper Lipschitz sum for the compact reciprocal-quartic
density on a positive compact branch. -/
def projectiveCompactLipschitzUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) +
        projectiveCompactLipschitzUpperSum rest

/-- The width of a compact Lipschitz bracket is exactly the accumulated
Lipschitz uncertainty of its finite cells. -/
theorem projectiveCompactLipschitzSum_width_eq_sixteen_squareSum
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzUpperSum intervals -
        projectiveCompactLipschitzLowerSum intervals =
      16 * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      decide +kernel
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [projectiveCompactLipschitzLowerSum,
        projectiveCompactLipschitzUpperSum,
        ArctanGeometry.intervalSquareSum]
      calc
        (r - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) +
              projectiveCompactLipschitzUpperSum rest -
            ((r - p) * (reciprocalQuarticSymmetricDensity (-1) p -
                8 * (r - p)) + projectiveCompactLipschitzLowerSum rest) =
            16 * ((r - p) * (r - p)) +
              (projectiveCompactLipschitzUpperSum rest -
                projectiveCompactLipschitzLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ = 16 * ((r - p) * (r - p)) +
              16 * ArctanGeometry.intervalSquareSum rest := by rw [ih]
        _ = 16 * ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- The compact lower Lipschitz sum lies below the transported Cauchy upper
sum on every finite positive branch cover. -/
theorem projectiveCompactLipschitzLowerSum_le_integralUpperSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    projectiveCompactLipschitzLowerSum intervals <=
      ArctanGeometry.integralUpperSum (projectiveCompactIntervals intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactLipschitzLowerSum, projectiveCompactIntervals,
        ArctanGeometry.integralUpperSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hr1 : r < 1 := by grind
      have hcell :=
        projectiveCompact_lipschitzLowerCell_le_integralUpperStep ha hpr hr1
      have htail := ih r hr0 hrest
      simp only [projectiveCompactLipschitzLowerSum, projectiveCompactIntervals,
        ArctanGeometry.integralUpperSum]
      exact rat_add_le_add hcell htail

/-- The transported Cauchy lower sum lies below the compact upper Lipschitz
sum on every finite positive branch cover. -/
theorem projectiveCompactIntegralLowerSum_le_lipschitzUpperSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    ArctanGeometry.integralLowerSum (projectiveCompactIntervals intervals) <=
      projectiveCompactLipschitzUpperSum intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [projectiveCompactLipschitzUpperSum, projectiveCompactIntervals,
        ArctanGeometry.integralLowerSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrs : r <= s := ArctanGeometry.CoversInterval.start_le_end hrest
      have hr1 : r < 1 := by grind
      have hcell :=
        projectiveCompact_integralLowerStep_le_lipschitzUpperCell ha hpr hr1
      have htail := ih r hr0 hrest
      simp only [projectiveCompactLipschitzUpperSum, projectiveCompactIntervals,
        ArctanGeometry.integralLowerSum]
      exact rat_add_le_add hcell htail

/-- The finite compact-density Lipschitz bracket overlaps the ordinary Cauchy
rectangle bracket after projective transport of the same source partition.
This is the assembled finite quadrature bridge; the remaining work is to
turn its endpoint schedule into an equivalence of the full integral raws. -/
theorem projectiveCompactLipschitzSum_overlaps_integralSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    QInterval.Overlaps
      { lo := projectiveCompactLipschitzLowerSum intervals,
        hi := projectiveCompactLipschitzUpperSum intervals }
      (ArctanGeometry.integralSumInterval (projectiveCompactIntervals intervals)) := by
  unfold QInterval.Overlaps ArctanGeometry.integralSumInterval
  exact ⟨projectiveCompactLipschitzLowerSum_le_integralUpperSum a s intervals
      ha hs hcover,
    projectiveCompactIntegralLowerSum_le_lipschitzUpperSum a s intervals
      ha hs hcover⟩

/-- A factor-two symmetric core bracket obtained from the positive source
branch.  It is a convenient finite bridge for an even density; identifying it
with a particular left- or right-endpoint partition remains a separate
cell-orientation calculation. -/
def projectiveCompactSymmetricLipschitzSum
    (intervals : List (Rat × Rat)) : QInterval :=
  { lo := 2 * projectiveCompactLipschitzLowerSum intervals,
    hi := 2 * projectiveCompactLipschitzUpperSum intervals }

/-- The matching two-branch Cauchy rectangle bracket for the projective image
of a positive source partition. -/
def projectiveCompactSymmetricIntegralSum
    (intervals : List (Rat × Rat)) : QInterval :=
  { lo := 2 * ArctanGeometry.integralLowerSum
      (projectiveCompactIntervals intervals),
    hi := 2 * ArctanGeometry.integralUpperSum
      (projectiveCompactIntervals intervals) }

/-- The factor-two symmetric compact bracket has twice the positive-branch
Lipschitz uncertainty. -/
theorem projectiveCompactSymmetricLipschitzSum_width_eq_thirtytwo_squareSum
    (intervals : List (Rat × Rat)) :
    (projectiveCompactSymmetricLipschitzSum intervals).width =
      32 * ArctanGeometry.intervalSquareSum intervals := by
  unfold projectiveCompactSymmetricLipschitzSum QInterval.width
  change 2 * projectiveCompactLipschitzUpperSum intervals -
      2 * projectiveCompactLipschitzLowerSum intervals =
        32 * ArctanGeometry.intervalSquareSum intervals
  calc
    2 * projectiveCompactLipschitzUpperSum intervals -
        2 * projectiveCompactLipschitzLowerSum intervals =
        2 * (projectiveCompactLipschitzUpperSum intervals -
          projectiveCompactLipschitzLowerSum intervals) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    _ = 2 * (16 * ArctanGeometry.intervalSquareSum intervals) := by
          rw [projectiveCompactLipschitzSum_width_eq_sixteen_squareSum]
    _ = 32 * ArctanGeometry.intervalSquareSum intervals := by
          grind [Rat.mul_assoc, Rat.mul_comm]

/-- Reflecting a compact lower left-endpoint cell through zero produces the
corresponding positive right-endpoint cell.  This is the finite orientation
identity needed to match the affine dyadic candidate to a symmetric positive
partition. -/
theorem projectiveCompact_reflectedLowerCell_eq_rightCell (p r : Rat) :
    ((-p) - (-r)) *
        (reciprocalQuarticSymmetricDensity (-1) (-r) -
          8 * ((-p) - (-r))) =
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r - 8 * (r - p)) := by
  rw [reciprocalQuarticSymmetricDensity_minus_one_even]
  grind [Rat.neg_sub, Rat.sub_eq_add_neg]

/-- The analogous reflected-cell identity for upper Lipschitz rectangles. -/
theorem projectiveCompact_reflectedUpperCell_eq_rightCell (p r : Rat) :
    ((-p) - (-r)) *
        (reciprocalQuarticSymmetricDensity (-1) (-r) +
          8 * ((-p) - (-r))) =
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r + 8 * (r - p)) := by
  rw [reciprocalQuarticSymmetricDensity_minus_one_even]
  grind [Rat.neg_sub, Rat.sub_eq_add_neg]

/-- Reverse an ordered positive partition through the origin. -/
def projectiveCompactReflectedIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      projectiveCompactReflectedIntervals rest ++ [(-r, -p)]

/-- Right-endpoint lower Lipschitz sum on a positive compact partition. -/
def projectiveCompactLipschitzRightLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r - 8 * (r - p)) +
        projectiveCompactLipschitzRightLowerSum rest

/-- Right-endpoint upper Lipschitz sum on a positive compact partition. -/
def projectiveCompactLipschitzRightUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r + 8 * (r - p)) +
        projectiveCompactLipschitzRightUpperSum rest

/-- The correctly oriented symmetric compact bracket: after reflection, the
negative half uses positive right endpoints while the positive half uses left
endpoints.  Unlike the auxiliary factor-two bracket, this is a literal
left-endpoint bracket on the reflected appended partition. -/
def projectiveCompactOrientedSymmetricLipschitzSum
    (intervals : List (Rat × Rat)) : QInterval :=
  { lo := projectiveCompactLipschitzRightLowerSum intervals +
      projectiveCompactLipschitzLowerSum intervals,
    hi := projectiveCompactLipschitzRightUpperSum intervals +
      projectiveCompactLipschitzUpperSum intervals }

private theorem projectiveCompact_rightLowerCell_le_leftUpperCell
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r - 8 * (r - p)) <=
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hqabs : qabs (r - p) = r - p := qabs_eq_self_of_nonneg hlen
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    p r (by grind) (by grind) (by grind) hr1
  have hdiff : reciprocalQuarticSymmetricDensity (-1) r -
      reciprocalQuarticSymmetricDensity (-1) p <= 8 * (r - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) r -
          reciprocalQuarticSymmetricDensity (-1) p <=
          qabs (reciprocalQuarticSymmetricDensity (-1) r -
            reciprocalQuarticSymmetricDensity (-1) p) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) r) := by
            rw [show reciprocalQuarticSymmetricDensity (-1) r -
              reciprocalQuarticSymmetricDensity (-1) p =
              -(reciprocalQuarticSymmetricDensity (-1) p -
                reciprocalQuarticSymmetricDensity (-1) r) by
                grind [Rat.sub_eq_add_neg], qabs_neg]
      _ <= 8 * qabs (r - p) := hlip
      _ = 8 * (r - p) := by rw [hqabs]
  have hvalue : reciprocalQuarticSymmetricDensity (-1) r - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue hlen

private theorem projectiveCompact_leftLowerCell_le_rightUpperCell
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) r + 8 * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hqabs : qabs (r - p) = r - p := qabs_eq_self_of_nonneg hlen
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    p r (by grind) (by grind) (by grind) hr1
  have hdiff : reciprocalQuarticSymmetricDensity (-1) p -
      reciprocalQuarticSymmetricDensity (-1) r <= 8 * (r - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) p -
          reciprocalQuarticSymmetricDensity (-1) r <=
          qabs (reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) r) := self_le_qabs _
      _ <= 8 * qabs (r - p) := hlip
      _ = 8 * (r - p) := by rw [hqabs]
  have hvalue : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) r + 8 * (r - p) := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue hlen

private theorem projectiveCompact_leftLowerCell_le_leftUpperCell
    {p r : Rat} (hpr : p <= r) :
    (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      (r - p) *
        (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hvalue : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    have hscale : 0 <= 8 * (r - p) :=
      Rat.mul_nonneg (by decide +kernel) hlen
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue hlen

private theorem projectiveCompactLipschitzRightLowerSum_le_leftUpperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    projectiveCompactLipschitzRightLowerSum intervals <=
      projectiveCompactLipschitzUpperSum intervals := by
  induction intervals with
  | nil =>
      exact Rat.le_refl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [projectiveCompactLipschitzRightLowerSum,
        projectiveCompactLipschitzUpperSum]
      exact rat_add_le_add
        (projectiveCompact_rightLowerCell_le_leftUpperCell hp0 hpr hr1)
        (ih hrest)

private theorem projectiveCompactLipschitzLowerSum_le_rightUpperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    projectiveCompactLipschitzLowerSum intervals <=
      projectiveCompactLipschitzRightUpperSum intervals := by
  induction intervals with
  | nil =>
      exact Rat.le_refl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [projectiveCompactLipschitzLowerSum,
        projectiveCompactLipschitzRightUpperSum]
      exact rat_add_le_add
        (projectiveCompact_leftLowerCell_le_rightUpperCell hp0 hpr hr1)
        (ih hrest)

private theorem projectiveCompactLipschitzLowerSum_le_upperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    projectiveCompactLipschitzLowerSum intervals <=
      projectiveCompactLipschitzUpperSum intervals := by
  induction intervals with
  | nil =>
      exact Rat.le_refl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      simp only [projectiveCompactLipschitzLowerSum,
        projectiveCompactLipschitzUpperSum]
      exact rat_add_le_add
        (projectiveCompact_leftLowerCell_le_leftUpperCell hpr)
        (ih hrest)

/-- The literal oriented symmetric bracket overlaps the auxiliary factor-two
symmetric bracket on every unit partition.  This moves the projective
positive-branch bridge onto the candidate's actual cell orientation without
changing either Pi definition. -/
theorem projectiveCompactOrientedSymmetricLipschitzSum_overlaps_symmetric
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    QInterval.Overlaps
      (projectiveCompactOrientedSymmetricLipschitzSum intervals)
      (projectiveCompactSymmetricLipschitzSum intervals) := by
  have hright := projectiveCompactLipschitzRightLowerSum_le_leftUpperSum
    intervals hunit
  have hleftRight := projectiveCompactLipschitzLowerSum_le_rightUpperSum
    intervals hunit
  have hleft := projectiveCompactLipschitzLowerSum_le_upperSum intervals hunit
  unfold QInterval.Overlaps projectiveCompactOrientedSymmetricLipschitzSum
    projectiveCompactSymmetricLipschitzSum
  constructor
  · calc
      projectiveCompactLipschitzRightLowerSum intervals +
          projectiveCompactLipschitzLowerSum intervals <=
          projectiveCompactLipschitzUpperSum intervals +
            projectiveCompactLipschitzUpperSum intervals :=
        rat_add_le_add hright hleft
      _ = 2 * projectiveCompactLipschitzUpperSum intervals := by
        grind [Rat.mul_add, Rat.add_comm]
  · calc
      2 * projectiveCompactLipschitzLowerSum intervals =
          projectiveCompactLipschitzLowerSum intervals +
            projectiveCompactLipschitzLowerSum intervals := by
            grind [Rat.mul_add, Rat.add_comm]
      _ <= projectiveCompactLipschitzRightUpperSum intervals +
            projectiveCompactLipschitzUpperSum intervals :=
        rat_add_le_add hleftRight hleft

private theorem projectiveCompact_orientedTailUpper_le
    {s : Rat} (hs0 : 0 <= s) (hs1 : s <= 1) :
    projectiveCompactLipschitzRightUpperSum [(s, 1)] +
        projectiveCompactLipschitzUpperSum [(s, 1)] <=
      ((64 : Rat) / 3) * (1 - s) := by
  have hwidth : 0 <= 1 - s := by grind [Rat.sub_eq_add_neg]
  have hwidth_le_one : 1 - s <= 1 := by grind [Rat.sub_eq_add_neg]
  have hsvalue : reciprocalQuarticSymmetricDensity (-1) s <= (8 : Rat) / 3 :=
    reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
      (by grind) hs1
  have honevalue : reciprocalQuarticSymmetricDensity (-1) 1 <= (8 : Rat) / 3 :=
    reciprocalQuarticSymmetricDensity_minus_one_le_eight_thirds_on_unit
      (by decide +kernel) (by decide +kernel)
  simp only [projectiveCompactLipschitzRightUpperSum,
    projectiveCompactLipschitzUpperSum]
  rw [Rat.add_zero, Rat.add_zero]
  calc
    (1 - s) *
          (reciprocalQuarticSymmetricDensity (-1) 1 + 8 * (1 - s)) +
        (1 - s) *
          (reciprocalQuarticSymmetricDensity (-1) s + 8 * (1 - s)) <=
        (1 - s) * ((8 : Rat) / 3 + 8 * (1 - s)) +
          (1 - s) * ((8 : Rat) / 3 + 8 * (1 - s)) :=
      rat_add_le_add
        (Rat.mul_le_mul_of_nonneg_left
          ((Rat.add_le_add_right).2 honevalue) hwidth)
        (Rat.mul_le_mul_of_nonneg_left
          ((Rat.add_le_add_right).2 hsvalue) hwidth)
    _ <= (1 - s) * ((8 : Rat) / 3 + 8 * 1) +
          (1 - s) * ((8 : Rat) / 3 + 8 * 1) :=
      rat_add_le_add
        (Rat.mul_le_mul_of_nonneg_left
          ((Rat.add_le_add_left).2
            (Rat.mul_le_mul_of_nonneg_left hwidth_le_one (by decide +kernel))) hwidth)
        (Rat.mul_le_mul_of_nonneg_left
          ((Rat.add_le_add_left).2
            (Rat.mul_le_mul_of_nonneg_left hwidth_le_one (by decide +kernel))) hwidth)
    _ = ((64 : Rat) / 3) * (1 - s) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The certified symmetric tail raw also absorbs the two differently oriented
endpoint cells of the literal candidate mesh. -/
theorem projectiveCompactDyadicOrientedTailUpper_le
    (n : Nat) :
    projectiveCompactLipschitzRightUpperSum
        [(projectiveCompactDyadicEndpoint n, 1)] +
      projectiveCompactLipschitzUpperSum
        [(projectiveCompactDyadicEndpoint n, 1)] <=
      (projectiveCompactDyadicSymmetricTailError.compute n).hi := by
  rw [projectiveCompactDyadicSymmetricTailError_compute]
  have htail := projectiveCompact_orientedTailUpper_le
    (projectiveCompactDyadicEndpoint_nonnegative n)
    (Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n))
  calc
    projectiveCompactLipschitzRightUpperSum
          [(projectiveCompactDyadicEndpoint n, 1)] +
        projectiveCompactLipschitzUpperSum
          [(projectiveCompactDyadicEndpoint n, 1)] <=
        ((64 : Rat) / 3) * (1 - projectiveCompactDyadicEndpoint n) := htail
    _ = ((64 : Rat) / 3) * (1 / (((2 ^ n : Nat) : Rat))) := by
      dsimp [projectiveCompactDyadicEndpoint]
      grind [Rat.sub_eq_add_neg]

private theorem projectiveCompactLipschitzLowerSum_append
    (left right : List (Rat × Rat)) :
    projectiveCompactLipschitzLowerSum (left ++ right) =
      projectiveCompactLipschitzLowerSum left +
        projectiveCompactLipschitzLowerSum right := by
  induction left with
  | nil =>
      exact (Rat.zero_add _).symm
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, projectiveCompactLipschitzLowerSum]
      rw [ih]
      grind [Rat.add_assoc]

private theorem projectiveCompactLipschitzUpperSum_append
    (left right : List (Rat × Rat)) :
    projectiveCompactLipschitzUpperSum (left ++ right) =
      projectiveCompactLipschitzUpperSum left +
        projectiveCompactLipschitzUpperSum right := by
  induction left with
  | nil =>
      exact (Rat.zero_add _).symm
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, projectiveCompactLipschitzUpperSum]
      rw [ih]
      grind [Rat.add_assoc]

/-- Splitting a compact-density Lipschitz cell at any rational interior point
tightens its lower and upper brackets.  This is the arbitrary-split form of
the midpoint refinement theorem, needed to compare differently scheduled
finite partitions. -/
private theorem projectiveCompactLipschitzCells_split
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) (hr1 : r <= 1) :
    (r - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) <=
      (q - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (q - p)) +
        (r - q) * (reciprocalQuarticSymmetricDensity (-1) q - 8 * (r - q)) /\
    (q - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (q - p)) +
        (r - q) * (reciprocalQuarticSymmetricDensity (-1) q + 8 * (r - q)) <=
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hp1 : p <= 1 := Rat.le_trans hpq (Rat.le_trans hqr hr1)
  have hq1 : q <= 1 := Rat.le_trans hqr hr1
  have hpq0 : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hqr0 : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hdist : qabs (q - p) = q - p := qabs_eq_self_of_nonneg hpq0
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    p q (by grind) hp1 (by grind) hq1
  have hforward : reciprocalQuarticSymmetricDensity (-1) p -
      reciprocalQuarticSymmetricDensity (-1) q <= 8 * (q - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) p -
          reciprocalQuarticSymmetricDensity (-1) q <=
          qabs (reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) q) := self_le_qabs _
      _ <= 8 * qabs (q - p) := hlip
      _ = 8 * (q - p) := by rw [hdist]
  have hreverse : reciprocalQuarticSymmetricDensity (-1) q -
      reciprocalQuarticSymmetricDensity (-1) p <= 8 * (q - p) := by
    calc
      reciprocalQuarticSymmetricDensity (-1) q -
          reciprocalQuarticSymmetricDensity (-1) p =
          -(reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) q) := by
            grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) q)) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) p -
            reciprocalQuarticSymmetricDensity (-1) q) := qabs_neg _
      _ <= 8 * (q - p) := by simpa [hdist] using hlip
  have hleftLower : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) p - 8 * (q - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth
      (by decide +kernel : (0 : Rat) <= 8)
    grind [Rat.sub_eq_add_neg]
  have hrightLower : reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p) <=
      reciprocalQuarticSymmetricDensity (-1) q - 8 * (r - q) := by
    grind [Rat.sub_eq_add_neg]
  have hleftUpper : reciprocalQuarticSymmetricDensity (-1) p + 8 * (q - p) <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth
      (by decide +kernel : (0 : Rat) <= 8)
    grind [Rat.sub_eq_add_neg]
  have hrightUpper : reciprocalQuarticSymmetricDensity (-1) q + 8 * (r - q) <=
      reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p) := by
    grind [Rat.sub_eq_add_neg]
  constructor
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleftLower hpq0
    have hright := Rat.mul_le_mul_of_nonneg_left hrightLower hqr0
    calc
      (r - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) =
          (q - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) +
            (r - q) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (r - p)) := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
                Rat.add_assoc, Rat.add_comm]
      _ <= (q - p) * (reciprocalQuarticSymmetricDensity (-1) p - 8 * (q - p)) +
            (r - q) * (reciprocalQuarticSymmetricDensity (-1) q - 8 * (r - q)) :=
            rat_add_le_add hleft hright
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleftUpper hpq0
    have hright := Rat.mul_le_mul_of_nonneg_left hrightUpper hqr0
    calc
      (q - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (q - p)) +
          (r - q) * (reciprocalQuarticSymmetricDensity (-1) q + 8 * (r - q)) <=
          (q - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) +
            (r - q) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) :=
            rat_add_le_add hleft hright
      _ = (r - p) * (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) := by
            grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
              Rat.add_assoc, Rat.add_comm]

private theorem projectiveCompactLipschitzUpperSum_nonnegative
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    0 <= projectiveCompactLipschitzUpperSum intervals := by
  induction intervals with
  | nil =>
      simp [projectiveCompactLipschitzUpperSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      have hwidth : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
      have hvalue : 0 <= reciprocalQuarticSymmetricDensity (-1) p +
          8 * (r - p) :=
        Rat.add_nonneg (reciprocalQuarticSymmetricDensity_minus_one_nonneg _)
          (Rat.mul_nonneg (by decide +kernel) hwidth)
      have hcell : 0 <= (r - p) *
          (reciprocalQuarticSymmetricDensity (-1) p + 8 * (r - p)) :=
        Rat.mul_nonneg hwidth hvalue
      exact Rat.add_nonneg hcell (ih hrest)

private theorem projectiveCompactLipschitzLowerSum_eq_zero_of_covers_point
    {a : Rat} {intervals : List (Rat × Rat)}
    (hcover : ArctanGeometry.CoversInterval a a intervals) :
    projectiveCompactLipschitzLowerSum intervals = 0 := by
  induction intervals generalizing a with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hra_le : r <= a := ArctanGeometry.CoversInterval.start_le_end hrest
      have hra : r = a := by grind
      subst r
      have htail := ih hrest
      simp [projectiveCompactLipschitzLowerSum, htail]
      grind [Rat.sub_eq_add_neg]

/-- Lower and upper compact-density Lipschitz sums on any two ordered covers
of the same rational subinterval have the expected cross inequality.  The
proof refines only finite rational cells; no completed integral is used. -/
private theorem projectiveCompactLipschitzLowerSum_le_upperSum_of_covers
    {a b : Rat} (ha : 0 <= a) (hb : b <= 1)
    (lower upper : List (Rat × Rat))
    (hlower : ArctanGeometry.CoversInterval a b lower)
    (hupper : ArctanGeometry.CoversInterval a b upper) :
    projectiveCompactLipschitzLowerSum lower <=
      projectiveCompactLipschitzUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a -> b <= 1 ->
        ArctanGeometry.CoversInterval a b lower ->
        ArctanGeometry.CoversInterval a b upper ->
        projectiveCompactLipschitzLowerSum lower <=
          projectiveCompactLipschitzUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hb hlower hupper
        cases lower <;> cases upper <;>
          simp [projectiveCompactLipschitzLowerSum,
            projectiveCompactLipschitzUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hb hlower hupper
        cases lower with
        | nil =>
            have hupperNonnegative : 0 <= projectiveCompactLipschitzUpperSum upper :=
              projectiveCompactLipschitzUpperSum_nonnegative upper
                (ArctanGeometry.CoversInterval.unit ha hb hupper)
            simpa [projectiveCompactLipschitzLowerSum] using hupperNonnegative
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [ArctanGeometry.CoversInterval] using hupper
                subst b
                have hzero :=
                  projectiveCompactLipschitzLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest) hlower
                simp [projectiveCompactLipschitzUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsle : s <= b := ArctanGeometry.CoversInterval.start_le_end hupperRest
                  have hsplitUpper : ArctanGeometry.CoversInterval r b
                      ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec : lowerRest.length + ((r, s) :: upperRest).length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec := ih lowerRest ((r, s) :: upperRest) r b
                    hlenRec hr0 hb hlowerRest hsplitUpper
                  have hheadLow :
                      (r - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                        8 * (r - a)) <=
                        (r - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (r - a)) :=
                    projectiveCompact_leftLowerCell_le_leftUpperCell hpr
                  have hheadSplit :
                      (r - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                        8 * (r - a)) +
                        (s - r) * (reciprocalQuarticSymmetricDensity (-1) r +
                          8 * (s - r)) <=
                        (s - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (s - a)) :=
                    (projectiveCompactLipschitzCells_split ha hpr hrs
                      (Rat.le_trans hsle hb)).2
                  simp [projectiveCompactLipschitzLowerSum,
                    projectiveCompactLipschitzUpperSum] at hrec ⊢
                  calc
                    (r - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                        8 * (r - a)) + projectiveCompactLipschitzLowerSum lowerRest <=
                        (r - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (r - a)) +
                          ((s - r) * (reciprocalQuarticSymmetricDensity (-1) r +
                            8 * (s - r)) +
                            projectiveCompactLipschitzUpperSum upperRest) :=
                      rat_add_le_add hheadLow hrec
                    _ = ((r - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (r - a)) +
                          (s - r) * (reciprocalQuarticSymmetricDensity (-1) r +
                            8 * (s - r))) +
                          projectiveCompactLipschitzUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= (s - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (s - a)) +
                          projectiveCompactLipschitzUpperSum upperRest :=
                      rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hrle : r <= b := ArctanGeometry.CoversInterval.start_le_end hlowerRest
                  have hsplitLower : ArctanGeometry.CoversInterval s b
                      ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec : ((s, r) :: lowerRest).length + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec := ih ((s, r) :: lowerRest) upperRest s b
                    hlenRec hs0 hb hsplitLower hupperRest
                  have hheadSplit :
                      (r - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                        8 * (r - a)) <=
                        (s - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                          8 * (s - a)) +
                          (r - s) * (reciprocalQuarticSymmetricDensity (-1) s -
                            8 * (r - s)) :=
                    (projectiveCompactLipschitzCells_split ha hps hsr
                      (Rat.le_trans hrle hb)).1
                  have hheadLow :
                      (s - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                        8 * (s - a)) <=
                        (s - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (s - a)) :=
                    projectiveCompact_leftLowerCell_le_leftUpperCell hps
                  simp [projectiveCompactLipschitzLowerSum,
                    projectiveCompactLipschitzUpperSum] at hrec ⊢
                  calc
                    (r - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                        8 * (r - a)) + projectiveCompactLipschitzLowerSum lowerRest <=
                        ((s - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                          8 * (s - a)) +
                          (r - s) * (reciprocalQuarticSymmetricDensity (-1) s -
                            8 * (r - s))) + projectiveCompactLipschitzLowerSum lowerRest :=
                      rat_add_le_add hheadSplit Rat.le_refl
                    _ = (s - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                          8 * (s - a)) +
                          ((r - s) * (reciprocalQuarticSymmetricDensity (-1) s -
                            8 * (r - s)) +
                            projectiveCompactLipschitzLowerSum lowerRest) := by
                            grind [Rat.add_assoc]
                    _ <= (s - a) * (reciprocalQuarticSymmetricDensity (-1) a -
                          8 * (s - a)) +
                          projectiveCompactLipschitzUpperSum upperRest :=
                      rat_add_le_add Rat.le_refl hrec
                    _ <= (s - a) * (reciprocalQuarticSymmetricDensity (-1) a +
                          8 * (s - a)) +
                          projectiveCompactLipschitzUpperSum upperRest :=
                      rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hb hlower hupper

private theorem projectiveCompactLipschitzSum_overlaps_of_covers
    {a b : Rat} (ha : 0 <= a) (hb : b <= 1)
    (left right : List (Rat × Rat))
    (hleft : ArctanGeometry.CoversInterval a b left)
    (hright : ArctanGeometry.CoversInterval a b right) :
    QInterval.Overlaps
      { lo := projectiveCompactLipschitzLowerSum left,
        hi := projectiveCompactLipschitzUpperSum left }
      { lo := projectiveCompactLipschitzLowerSum right,
        hi := projectiveCompactLipschitzUpperSum right } := by
  exact ⟨projectiveCompactLipschitzLowerSum_le_upperSum_of_covers
      ha hb left right hleft hright,
    projectiveCompactLipschitzLowerSum_le_upperSum_of_covers
      ha hb right left hright hleft⟩

private theorem projectiveCompactLipschitzRightLowerSum_append
    (left right : List (Rat × Rat)) :
    projectiveCompactLipschitzRightLowerSum (left ++ right) =
      projectiveCompactLipschitzRightLowerSum left +
        projectiveCompactLipschitzRightLowerSum right := by
  induction left with
  | nil =>
      exact (Rat.zero_add _).symm
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, projectiveCompactLipschitzRightLowerSum]
      rw [ih]
      grind [Rat.add_assoc]

private theorem projectiveCompactLipschitzRightUpperSum_append
    (left right : List (Rat × Rat)) :
    projectiveCompactLipschitzRightUpperSum (left ++ right) =
      projectiveCompactLipschitzRightUpperSum left +
        projectiveCompactLipschitzRightUpperSum right := by
  induction left with
  | nil =>
      exact (Rat.zero_add _).symm
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, projectiveCompactLipschitzRightUpperSum]
      rw [ih]
      grind [Rat.add_assoc]

private theorem projectiveCompactLipschitzRightLowerSum_le_rightUpperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    projectiveCompactLipschitzRightLowerSum intervals <=
      projectiveCompactLipschitzRightUpperSum intervals := by
  induction intervals with
  | nil =>
      exact Rat.le_refl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
      have hvalue : reciprocalQuarticSymmetricDensity (-1) r - 8 * (r - p) <=
          reciprocalQuarticSymmetricDensity (-1) r + 8 * (r - p) := by
        have hscale : 0 <= 8 * (r - p) :=
          Rat.mul_nonneg (by decide +kernel) hlen
        grind [Rat.sub_eq_add_neg]
      simp only [projectiveCompactLipschitzRightLowerSum,
        projectiveCompactLipschitzRightUpperSum]
      exact rat_add_le_add
        (Rat.mul_le_mul_of_nonneg_left hvalue hlen) (ih hrest)

private theorem projectiveCompactOrientedSymmetricLipschitzSum_ordered
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    (projectiveCompactOrientedSymmetricLipschitzSum intervals).lo <=
      (projectiveCompactOrientedSymmetricLipschitzSum intervals).hi := by
  unfold projectiveCompactOrientedSymmetricLipschitzSum
  exact rat_add_le_add
    (projectiveCompactLipschitzRightLowerSum_le_rightUpperSum intervals hunit)
    (projectiveCompactLipschitzLowerSum_le_upperSum intervals hunit)

private theorem projectiveCompactOrientedSymmetricLipschitzSum_append
    (left right : List (Rat × Rat)) :
    projectiveCompactOrientedSymmetricLipschitzSum (left ++ right) =
      { lo := (projectiveCompactOrientedSymmetricLipschitzSum left).lo +
          (projectiveCompactOrientedSymmetricLipschitzSum right).lo,
        hi := (projectiveCompactOrientedSymmetricLipschitzSum left).hi +
          (projectiveCompactOrientedSymmetricLipschitzSum right).hi } := by
  unfold projectiveCompactOrientedSymmetricLipschitzSum
  rw [projectiveCompactLipschitzRightLowerSum_append,
    projectiveCompactLipschitzLowerSum_append,
    projectiveCompactLipschitzRightUpperSum_append,
    projectiveCompactLipschitzUpperSum_append]
  apply (QInterval.mk.injEq _ _ _ _).mpr
  constructor <;> dsimp <;> grind [Rat.add_assoc, Rat.add_comm]

/-- Appending a nonnegative, bounded tail enclosure to an oriented compact
core preserves overlap with the factor-two core bracket. -/
theorem projectiveCompactOrientedSymmetric_append_overlaps_tailEnclosure
    (core tail : List (Rat × Rat)) (tailUpper : Rat)
    (hcore : QInterval.Overlaps
      (projectiveCompactOrientedSymmetricLipschitzSum core)
      (projectiveCompactSymmetricLipschitzSum core))
    (htail_ordered :
      (projectiveCompactOrientedSymmetricLipschitzSum tail).lo <=
        (projectiveCompactOrientedSymmetricLipschitzSum tail).hi)
    (htail_upper :
      (projectiveCompactOrientedSymmetricLipschitzSum tail).hi <= tailUpper)
    (htail_nonneg : 0 <=
      (projectiveCompactOrientedSymmetricLipschitzSum tail).hi) :
    QInterval.Overlaps
      (projectiveCompactOrientedSymmetricLipschitzSum (core ++ tail))
      { lo := (projectiveCompactSymmetricLipschitzSum core).lo,
        hi := (projectiveCompactSymmetricLipschitzSum core).hi + tailUpper } := by
  rw [projectiveCompactOrientedSymmetricLipschitzSum_append]
  unfold QInterval.Overlaps at hcore
  change
    (projectiveCompactOrientedSymmetricLipschitzSum core).lo +
        (projectiveCompactOrientedSymmetricLipschitzSum tail).lo <=
      (projectiveCompactSymmetricLipschitzSum core).hi + tailUpper /\
    (projectiveCompactSymmetricLipschitzSum core).lo <=
      (projectiveCompactOrientedSymmetricLipschitzSum core).hi +
        (projectiveCompactOrientedSymmetricLipschitzSum tail).hi
  constructor
  · exact rat_add_le_add hcore.1 (Rat.le_trans htail_ordered htail_upper)
  · exact Rat.le_trans hcore.2 (by grind)

/-- The reflected lower sum is exactly the positive right-endpoint lower sum. -/
theorem projectiveCompactLipschitzLowerSum_reflected_eq_right
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzLowerSum
      (projectiveCompactReflectedIntervals intervals) =
      projectiveCompactLipschitzRightLowerSum intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [projectiveCompactReflectedIntervals,
        projectiveCompactLipschitzRightLowerSum]
      rw [projectiveCompactLipschitzLowerSum_append, ih]
      simp only [projectiveCompactLipschitzLowerSum]
      rw [projectiveCompact_reflectedLowerCell_eq_rightCell]
      grind [Rat.add_assoc, Rat.add_comm]

/-- The reflected upper sum is exactly the positive right-endpoint upper sum. -/
theorem projectiveCompactLipschitzUpperSum_reflected_eq_right
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzUpperSum
      (projectiveCompactReflectedIntervals intervals) =
      projectiveCompactLipschitzRightUpperSum intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [projectiveCompactReflectedIntervals,
        projectiveCompactLipschitzRightUpperSum]
      rw [projectiveCompactLipschitzUpperSum_append, ih]
      simp only [projectiveCompactLipschitzUpperSum]
      rw [projectiveCompact_reflectedUpperCell_eq_rightCell]
      grind [Rat.add_assoc, Rat.add_comm]

/-- The left-endpoint compact bracket on a symmetric reflected partition is
the sum of the positive right- and left-endpoint brackets.  This is the exact
orientation formula for the candidate's negative and positive halves. -/
theorem projectiveCompactLipschitzLowerSum_reflected_append_eq_right_add_left
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzLowerSum
      (projectiveCompactReflectedIntervals intervals ++ intervals) =
      projectiveCompactLipschitzRightLowerSum intervals +
        projectiveCompactLipschitzLowerSum intervals := by
  rw [projectiveCompactLipschitzLowerSum_append,
    projectiveCompactLipschitzLowerSum_reflected_eq_right]

/-- The upper counterpart of the exact reflected-partition orientation
formula. -/
theorem projectiveCompactLipschitzUpperSum_reflected_append_eq_right_add_left
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzUpperSum
      (projectiveCompactReflectedIntervals intervals ++ intervals) =
      projectiveCompactLipschitzRightUpperSum intervals +
        projectiveCompactLipschitzUpperSum intervals := by
  rw [projectiveCompactLipschitzUpperSum_append,
    projectiveCompactLipschitzUpperSum_reflected_eq_right]

/-- Reflection turns an ordered cover of `[a,b]` into an ordered cover of
`[-b,-a]`. -/
theorem projectiveCompactReflectedIntervals_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval (-b) (-a)
      (projectiveCompactReflectedIntervals intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp only [projectiveCompactReflectedIntervals,
        ArctanGeometry.CoversInterval] at hcover ⊢
      grind
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      simp only [projectiveCompactReflectedIntervals]
      exact ArctanGeometry.CoversInterval.extend_right
        (ih r hrest) (by grind [Rat.neg_le_neg_iff])

/-- Joining a positive cover with its reflection covers the symmetric compact
core. -/
theorem projectiveCompactReflected_append_covers
    (s : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval 0 s intervals) :
    ArctanGeometry.CoversInterval (-s) s
      (projectiveCompactReflectedIntervals intervals ++ intervals) := by
  exact ArctanGeometry.CoversInterval.append
    (projectiveCompactReflectedIntervals_covers 0 s intervals hcover)
    hcover

/-- The two symmetric finite quadrature cores overlap after the projective
transport.  The proof is just positive rational scaling of the verified
one-branch cellwise bridge; the evenness lemmas above justify its intended
two-branch interpretation. -/
theorem projectiveCompactSymmetricLipschitzSum_overlaps_integralSum
    (a s : Rat) (intervals : List (Rat × Rat))
    (ha : 0 <= a) (hs : s < 1)
    (hcover : ArctanGeometry.CoversInterval a s intervals) :
    QInterval.Overlaps
      (projectiveCompactSymmetricLipschitzSum intervals)
      (projectiveCompactSymmetricIntegralSum intervals) := by
  have h := projectiveCompactLipschitzSum_overlaps_integralSum
    a s intervals ha hs hcover
  unfold QInterval.Overlaps projectiveCompactSymmetricLipschitzSum
    projectiveCompactSymmetricIntegralSum at *
  exact ⟨Rat.mul_le_mul_of_nonneg_left h.1 (by decide +kernel),
    Rat.mul_le_mul_of_nonneg_left h.2 (by decide +kernel)⟩

/-- The compactified density has finite rational endpoint values, so the
projective chart's poles are removable at the level of the intended integrand. -/
theorem reciprocalQuarticSymmetricDensity_minus_one_at_one :
    reciprocalQuarticSymmetricDensity (-1) 1 = 2 := by
  decide +kernel

theorem reciprocalQuarticSymmetricDensity_minus_one_at_neg_one :
    reciprocalQuarticSymmetricDensity (-1) (-1) = 2 := by
  decide +kernel

/-- Exact rational-name evaluator for the compactified clean quartic density.
It is defined on every rational input; later interval regularity will certify
its finite-interval integral. -/
def reciprocalQuarticMinusOneCompactRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ =>
    let y := reciprocalQuarticSymmetricDensity (-1) x
    { lo := y, hi := y }

/-- The compact reciprocal-quartic density restricted to a rational interval. -/
def reciprocalQuarticMinusOneCompactOnInterval (a b : Rat) : FunctionOnInterval where
  raw := reciprocalQuarticMinusOneCompactRaw
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x _hx
    simpa [reciprocalQuarticMinusOneCompactRaw] using
      RealCompute.ofRat_valid (reciprocalQuarticSymmetricDensity (-1) x)

theorem reciprocalQuarticMinusOneCompactOnInterval_valid (a b : Rat) :
    (reciprocalQuarticMinusOneCompactOnInterval a b).toRealFunRaw.Valid :=
  FunctionOnInterval.toRealFunRaw_valid _

theorem reciprocalQuarticMinusOneCompactRaw_compute_eq_density
    (x : Rat) (h : reciprocalQuarticMinusOneCompactRaw.definedAt x) (n : Nat) :
    reciprocalQuarticMinusOneCompactRaw.compute x h n =
      { lo := reciprocalQuarticSymmetricDensity (-1) x,
        hi := reciprocalQuarticSymmetricDensity (-1) x } := by
  simp [reciprocalQuarticMinusOneCompactRaw]

/-- The exact compact-density evaluator is rational epsilon-delta continuous
on `[-1,1]`.  The modulus uses the explicit Lipschitz constant `8`. -/
theorem reciprocalQuarticMinusOneCompact_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) := by
  intro eps
  let delta : QPos :=
    { val := eps.val / 8
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide +kernel)) }
  refine ⟨delta, 0, ?_⟩
  intro x y hx hy hxy
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    x y hxlo hxhi hylo hyhi
  have hdist :
      qabs (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) <= eps.val := by
    calc
      qabs (reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y) <= 8 * qabs (y - x) := hlip
      _ <= 8 * (eps.val / 8) := Rat.mul_le_mul_of_nonneg_left (by
        simpa [delta] using hxy)
        (by decide +kernel)
      _ = eps.val := by
        rw [Rat.div_def]
        have hcancel : (8 : Rat) * (8 : Rat)⁻¹ = 1 := by decide +kernel
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hreverse :
      reciprocalQuarticSymmetricDensity (-1) y -
        reciprocalQuarticSymmetricDensity (-1) x <= eps.val := by
    calc
      reciprocalQuarticSymmetricDensity (-1) y -
          reciprocalQuarticSymmetricDensity (-1) x =
          -(reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y) := by
            grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y)) := self_le_qabs _
      _ = qabs (reciprocalQuarticSymmetricDensity (-1) x -
            reciprocalQuarticSymmetricDensity (-1) y) := qabs_neg _
      _ <= eps.val := hdist
  have hforward :
      reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) y <= eps.val := by
    exact Rat.le_trans (self_le_qabs _) hdist
  unfold QInterval.NearAt
  change
    reciprocalQuarticSymmetricDensity (-1) x <=
        reciprocalQuarticSymmetricDensity (-1) y + eps.val /\
      reciprocalQuarticSymmetricDensity (-1) y <=
        reciprocalQuarticSymmetricDensity (-1) x + eps.val /\
      reciprocalQuarticSymmetricDensity (-1) x -
          reciprocalQuarticSymmetricDensity (-1) x <= eps.val /\
      reciprocalQuarticSymmetricDensity (-1) y -
          reciprocalQuarticSymmetricDensity (-1) y <= eps.val
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor <;> grind

/-- A finite rational scaling fact used by the compact-density interval
evaluator. -/
private theorem reciprocalQuartic_interval_width_scale (w : Rat) (n : Nat)
    (hn : n ≠ 0)
    (hw : w <= 1 / ((16 * n : Nat) : Rat)) :
    16 * w <= 1 / (n : Rat) := by
  calc
    16 * w <= 16 * (1 / ((16 * n : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by decide +kernel)
    _ = 1 / (n : Rat) := by
      rw [Rat.div_def]
      rw [show ((16 * n : Nat) : Rat) = (16 : Rat) * (n : Rat) by
        exact Rat.natCast_mul 16 n]
      have h16 : (16 : Rat) ≠ 0 := by decide +kernel
      have hn' : (n : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Interval evaluator for the compact reciprocal-quartic density on
`[-1,1]`.  It evaluates the exact rational formula at the input midpoint and
enlarges by the proved `8`-Lipschitz error. -/
def reciprocalQuarticMinusOneCompact_evalInterval (I : QInterval) : QInterval :=
  let v := reciprocalQuarticSymmetricDensity (-1) I.midpoint
  { lo := v - 8 * I.width, hi := v + 8 * I.width }

theorem reciprocalQuarticMinusOneCompact_evalInterval_width (I : QInterval) :
    (reciprocalQuarticMinusOneCompact_evalInterval I).width = 16 * I.width := by
  simp [reciprocalQuarticMinusOneCompact_evalInterval, QInterval.width]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The compact reciprocal-quartic density is interval-regular on `[-1,1]`.

Every rational input box is enclosed by midpoint evaluation widened using the
checked `8`-Lipschitz bound.  This supplies the interval-level continuity data
needed by the integral, inverse, and ODE interfaces without importing a
topology or a completed real line. -/
def reciprocalQuarticMinusOneCompact_intervalRegular :
    IntervalRegularOn (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) := by
  refine
    { evalInterval := fun I _ _ => reciprocalQuarticMinusOneCompact_evalInterval I
      inputPrecision := fun n => 16 * (n + 1)
      inputPrecision_pos := by
        intro n
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    rcases hI with ⟨hlo, hord, hhi⟩
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    constructor
    · rw [reciprocalQuarticMinusOneCompact_evalInterval_width]
      exact Rat.mul_nonneg (by decide +kernel) hwidth_nonneg
    · rw [reciprocalQuarticMinusOneCompact_evalInterval_width]
      exact reciprocalQuartic_interval_width_scale I.width (n + 1)
        (Nat.succ_ne_zero n) hwidth
  · intro I hI x hx n hxlo hxhi
    rcases hI with ⟨hIlo, hordered, hIhi⟩
    have hmid := QInterval.midpoint_mem hordered
    have hmid_domain : inDomainInterval (-1) 1 I.midpoint :=
      ⟨Rat.le_trans hIlo hmid.1, Rat.le_trans hmid.2 hIhi⟩
    have hxdomain : inDomainInterval (-1) 1 x := hx
    have hdist : qabs (I.midpoint - x) <= I.width := by
      rw [show I.midpoint - x = -(x - I.midpoint) by
        grind [Rat.sub_eq_add_neg], qabs_neg]
      exact QInterval.qabs_sub_midpoint_le_width hordered hxlo hxhi
    have hlip := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
      x I.midpoint hxdomain.1 hxdomain.2 hmid_domain.1 hmid_domain.2
    have hdiff :
        qabs (reciprocalQuarticSymmetricDensity (-1) x -
          reciprocalQuarticSymmetricDensity (-1) I.midpoint) <= 8 * I.width := by
      exact Rat.le_trans hlip
        (Rat.mul_le_mul_of_nonneg_left hdist (by decide +kernel))
    have hupper : reciprocalQuarticSymmetricDensity (-1) x -
        reciprocalQuarticSymmetricDensity (-1) I.midpoint <= 8 * I.width :=
      Rat.le_trans (self_le_qabs _) hdiff
    have hlower : reciprocalQuarticSymmetricDensity (-1) I.midpoint -
        reciprocalQuarticSymmetricDensity (-1) x <= 8 * I.width := by
      calc
        reciprocalQuarticSymmetricDensity (-1) I.midpoint -
            reciprocalQuarticSymmetricDensity (-1) x =
            -(reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint) := by
              grind [Rat.sub_eq_add_neg]
        _ <= qabs (-(reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint)) := self_le_qabs _
        _ = qabs (reciprocalQuarticSymmetricDensity (-1) x -
              reciprocalQuarticSymmetricDensity (-1) I.midpoint) := qabs_neg _
        _ <= 8 * I.width := hdiff
    unfold QInterval.ContainsInterval
    change reciprocalQuarticSymmetricDensity (-1) I.midpoint - 8 * I.width <=
        reciprocalQuarticSymmetricDensity (-1) x /\
      reciprocalQuarticSymmetricDensity (-1) x <=
        reciprocalQuarticSymmetricDensity (-1) I.midpoint + 8 * I.width
    constructor <;> grind [Rat.sub_eq_add_neg]

/-- The compact reciprocal-quartic density packaged for theorem-facing
calculus consumers. -/
def reciprocalQuarticMinusOneCompact_continuous : ContinuousFunctionOnInterval where
  function := reciprocalQuarticMinusOneCompactOnInterval (-1) 1
  regular := reciprocalQuarticMinusOneCompact_intervalRegular

/-- The generic interval-regularity bridge reproduces rational
epsilon-delta continuity for the compact reciprocal-quartic density. -/
theorem reciprocalQuarticMinusOneCompact_epsilonDeltaContinuous_from_intervalRegular :
    EpsilonDeltaContinuousOn
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) :=
  reciprocalQuarticMinusOneCompact_intervalRegular.epsilonDeltaContinuous

/-- The affine unit-interval presentation of the compact reciprocal-quartic
density.  It is exactly the change of variables `x = 2t - 1`, including the
Jacobian `2`; hence it is the form on which the ordinary midpoint-dyadic
Riemann mesh operates.  This is a finite rational function at every rational
sample point--not an appeal to a completed interval integral. -/
def reciprocalQuarticMinusOneUnitDensity (t : Rat) : Rat :=
  2 * reciprocalQuarticSymmetricDensity (-1) (2 * t - 1)

/-- The affine unit density is `32`-Lipschitz on `[0,1]`.  The factor is the
product of the compact-density constant `8`, the affine-coordinate stretch
`2`, and the Jacobian factor `2`. -/
theorem reciprocalQuarticMinusOneUnitDensity_lipschitz_on_unit
    (s t : Rat)
    (hs0 : 0 <= s) (hs1 : s <= 1)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs (reciprocalQuarticMinusOneUnitDensity s -
      reciprocalQuarticMinusOneUnitDensity t) <= 32 * qabs (t - s) := by
  have hslo : -1 <= 2 * s - 1 := by grind
  have hshi : 2 * s - 1 <= 1 := by grind
  have htlo : -1 <= 2 * t - 1 := by grind
  have hthi : 2 * t - 1 <= 1 := by grind
  have hcompact := reciprocalQuarticSymmetricDensity_minus_one_lipschitz_on_unit
    (2 * s - 1) (2 * t - 1) hslo hshi htlo hthi
  have hstretch : qabs ((2 * t - 1) - (2 * s - 1)) = 2 * qabs (t - s) := by
    rw [show (2 * t - 1) - (2 * s - 1) = 2 * (t - s) by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm]]
    rw [qabs_mul, qabs_eq_self_of_nonneg (by decide +kernel : (0 : Rat) <= 2)]
  have hscaled :
      qabs (2 * (reciprocalQuarticSymmetricDensity (-1) (2 * s - 1) -
        reciprocalQuarticSymmetricDensity (-1) (2 * t - 1))) <=
        2 * (8 * qabs ((2 * t - 1) - (2 * s - 1))) := by
    rw [qabs_mul, qabs_eq_self_of_nonneg (by decide +kernel : (0 : Rat) <= 2)]
    exact Rat.mul_le_mul_of_nonneg_left hcompact (by decide +kernel)
  calc
    qabs (reciprocalQuarticMinusOneUnitDensity s -
        reciprocalQuarticMinusOneUnitDensity t) =
        qabs (2 * (reciprocalQuarticSymmetricDensity (-1) (2 * s - 1) -
          reciprocalQuarticSymmetricDensity (-1) (2 * t - 1))) := by
          simp only [reciprocalQuarticMinusOneUnitDensity]
          congr 1
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm]
    _ <= 2 * (8 * qabs ((2 * t - 1) - (2 * s - 1))) := hscaled
    _ = 32 * qabs (t - s) := by rw [hstretch]; grind [Rat.mul_assoc, Rat.mul_comm]

/-- The exact left Riemann sum of the affine compact density on the ordinary
static dyadic mesh.  The stage is visibly a finite rational computation: no
limit, topology, or real-number completeness is hidden in this definition. -/
def reciprocalQuarticMinusOneUnitLeftRiemann (stage : Nat) : Rat :=
  riemannLeftExact reciprocalQuarticMinusOneUnitDensity 0 1 (2 ^ stage)

theorem reciprocalQuarticMinusOneUnitLeftRiemann_eq_finite_sum (stage : Nat) :
    reciprocalQuarticMinusOneUnitLeftRiemann stage =
      riemannLeftExact reciprocalQuarticMinusOneUnitDensity 0 1 (2 ^ stage) :=
  rfl

/-- A Lipschitz lower rectangle at the left endpoint of a unit cell.  The
subtracted term is the certified 32-Lipschitz oscillation bound over that
cell. -/
private def reciprocalQuarticMinusOneUnitLowerCell (p r : Rat) : Rat :=
  Integral.lipschitzLowerCell reciprocalQuarticMinusOneUnitDensity 32 p r

/-- The matching Lipschitz upper rectangle at the left endpoint of a unit
cell. -/
private def reciprocalQuarticMinusOneUnitUpperCell (p r : Rat) : Rat :=
  Integral.lipschitzUpperCell reciprocalQuarticMinusOneUnitDensity 32 p r

private def reciprocalQuarticMinusOneUnitLowerSum :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      reciprocalQuarticMinusOneUnitLowerCell p r +
        reciprocalQuarticMinusOneUnitLowerSum rest

private def reciprocalQuarticMinusOneUnitUpperSum :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      reciprocalQuarticMinusOneUnitUpperCell p r +
        reciprocalQuarticMinusOneUnitUpperSum rest

/-- The affine transport of a unit partition to the compact quartic interval
via `x = 2t - 1`. -/
def reciprocalQuarticMinusOneCompactAffineIntervals :
    List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (2 * p - 1, 2 * r - 1) ::
        reciprocalQuarticMinusOneCompactAffineIntervals rest

/-- Affine transport preserves the finite ordered-cover invariant. -/
theorem reciprocalQuarticMinusOneCompactAffineIntervals_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval (2 * a - 1) (2 * b - 1)
      (reciprocalQuarticMinusOneCompactAffineIntervals intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp only [reciprocalQuarticMinusOneCompactAffineIntervals,
        ArctanGeometry.CoversInterval] at hcover ⊢
      grind
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      simp only [reciprocalQuarticMinusOneCompactAffineIntervals,
        ArctanGeometry.CoversInterval]
      refine ⟨by grind, ?_, ih r hrest⟩
      rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
      exact (Rat.add_le_add_right (c := (-1 : Rat))).2
        (Rat.mul_le_mul_of_nonneg_left hpr
          (show (0 : Rat) <= 2 by decide +kernel))

/-- The affine image of the concrete unit dyadic partition is an ordered
rational cover of the whole compact projective interval. -/
theorem reciprocalQuarticMinusOneCompactAffineDyadicIntervals_covers
    (stage : Nat) :
    ArctanGeometry.CoversInterval (-1) 1
      (reciprocalQuarticMinusOneCompactAffineIntervals
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) := by
  have hcover := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (x := (1 : Rat)) (by decide +kernel) stage
  have h := reciprocalQuarticMinusOneCompactAffineIntervals_covers 0 1
    (ArctanGeometry.arctanAreaLoopState 1 stage).intervals hcover
  have hleft : (2 : Rat) * 0 - 1 = -1 := by decide +kernel
  have hright : (2 : Rat) * 1 - 1 = 1 := by decide +kernel
  rw [hleft, hright] at h
  exact h

/-- The list-level midpoint refinement used only to expose the exact symmetry
of the concrete unit dyadic mesh. -/
private def reciprocalQuarticUnitMidpointRefine : List (Rat × Rat) ->
    List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (p, (p + r) / 2) :: ((p + r) / 2, r) ::
        reciprocalQuarticUnitMidpointRefine rest

/-- Scale a unit partition into its left half. -/
private def reciprocalQuarticUnitLeftHalf : List (Rat × Rat) ->
    List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (p / 2, r / 2) :: reciprocalQuarticUnitLeftHalf rest

/-- Scale a unit partition into its right half. -/
private def reciprocalQuarticUnitRightHalf : List (Rat × Rat) ->
    List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      ((p + 1) / 2, (r + 1) / 2) :: reciprocalQuarticUnitRightHalf rest

/-- Reverse a unit partition through the midpoint of the unit interval. -/
private def reciprocalQuarticUnitReflectedIntervals : List (Rat × Rat) ->
    List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      reciprocalQuarticUnitReflectedIntervals rest ++ [(1 - r, 1 - p)]

private theorem reciprocalQuarticUnitMidpointRefine_eq_refineAux_intervals
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    reciprocalQuarticUnitMidpointRefine intervals =
      (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitMidpointRefine,
        ArctanGeometry.AreaLoopState.refineAux]
      rw [ih (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
        (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)]

private theorem reciprocalQuarticUnitDyadicIntervals_succ
    (stage : Nat) :
    (ArctanGeometry.arctanAreaLoopState 1 (stage + 1)).intervals =
      reciprocalQuarticUnitMidpointRefine
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
  rw [ArctanGeometry.arctanAreaLoopState_succ]
  change (ArctanGeometry.AreaLoopState.refineAux _ _ _).intervals = _
  exact (reciprocalQuarticUnitMidpointRefine_eq_refineAux_intervals _ _ _).symm

private theorem reciprocalQuarticUnitMidpointRefine_append
    (left right : List (Rat × Rat)) :
    reciprocalQuarticUnitMidpointRefine (left ++ right) =
      reciprocalQuarticUnitMidpointRefine left ++
        reciprocalQuarticUnitMidpointRefine right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, reciprocalQuarticUnitMidpointRefine]
      rw [ih]

private theorem reciprocalQuarticUnitLeftHalf_append
    (left right : List (Rat × Rat)) :
    reciprocalQuarticUnitLeftHalf (left ++ right) =
      reciprocalQuarticUnitLeftHalf left ++ reciprocalQuarticUnitLeftHalf right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, reciprocalQuarticUnitLeftHalf]
      rw [ih]

private theorem reciprocalQuarticUnitRightHalf_append
    (left right : List (Rat × Rat)) :
    reciprocalQuarticUnitRightHalf (left ++ right) =
      reciprocalQuarticUnitRightHalf left ++ reciprocalQuarticUnitRightHalf right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, reciprocalQuarticUnitRightHalf]
      rw [ih]

private theorem reciprocalQuarticUnitMidpointRefine_leftHalf
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticUnitMidpointRefine
        (reciprocalQuarticUnitLeftHalf intervals) =
      reciprocalQuarticUnitLeftHalf
        (reciprocalQuarticUnitMidpointRefine intervals) := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitLeftHalf,
        reciprocalQuarticUnitMidpointRefine]
      rw [ih]
      congr 3 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel]

private theorem reciprocalQuarticUnitMidpointRefine_rightHalf
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticUnitMidpointRefine
        (reciprocalQuarticUnitRightHalf intervals) =
      reciprocalQuarticUnitRightHalf
        (reciprocalQuarticUnitMidpointRefine intervals) := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitRightHalf,
        reciprocalQuarticUnitMidpointRefine]
      rw [ih]
      congr 3 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel]

private theorem reciprocalQuarticUnitDyadicIntervals_succ_split
    (stage : Nat) :
    (ArctanGeometry.arctanAreaLoopState 1 (stage + 1)).intervals =
      reciprocalQuarticUnitLeftHalf
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals ++
        reciprocalQuarticUnitRightHalf
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
  induction stage with
  | zero =>
      decide +kernel
  | succ stage ih =>
      calc
        (ArctanGeometry.arctanAreaLoopState 1 (stage.succ + 1)).intervals =
            reciprocalQuarticUnitMidpointRefine
              (ArctanGeometry.arctanAreaLoopState 1 stage.succ).intervals :=
          reciprocalQuarticUnitDyadicIntervals_succ stage.succ
        _ = reciprocalQuarticUnitMidpointRefine
              (reciprocalQuarticUnitLeftHalf
                (ArctanGeometry.arctanAreaLoopState 1 stage).intervals ++
                reciprocalQuarticUnitRightHalf
                  (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) := by
            rw [ih]
        _ = reciprocalQuarticUnitLeftHalf
              (reciprocalQuarticUnitMidpointRefine
                (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) ++
              reciprocalQuarticUnitRightHalf
                (reciprocalQuarticUnitMidpointRefine
                  (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) := by
            rw [reciprocalQuarticUnitMidpointRefine_append,
              reciprocalQuarticUnitMidpointRefine_leftHalf,
              reciprocalQuarticUnitMidpointRefine_rightHalf]
        _ = reciprocalQuarticUnitLeftHalf
              (ArctanGeometry.arctanAreaLoopState 1 stage.succ).intervals ++
              reciprocalQuarticUnitRightHalf
                (ArctanGeometry.arctanAreaLoopState 1 stage.succ).intervals := by
            rw [← reciprocalQuarticUnitDyadicIntervals_succ stage]

private theorem reciprocalQuarticUnitReflected_append
    (left right : List (Rat × Rat)) :
    reciprocalQuarticUnitReflectedIntervals (left ++ right) =
      reciprocalQuarticUnitReflectedIntervals right ++
        reciprocalQuarticUnitReflectedIntervals left := by
  induction left with
  | nil =>
      simp [reciprocalQuarticUnitReflectedIntervals]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, reciprocalQuarticUnitReflectedIntervals]
      rw [ih]
      exact List.append_assoc _ _ _

private theorem reciprocalQuarticUnitReflected_leftHalf
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticUnitReflectedIntervals
        (reciprocalQuarticUnitLeftHalf intervals) =
      reciprocalQuarticUnitRightHalf
        (reciprocalQuarticUnitReflectedIntervals intervals) := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitLeftHalf,
        reciprocalQuarticUnitReflectedIntervals]
      rw [ih]
      rw [reciprocalQuarticUnitRightHalf_append]
      simp only [reciprocalQuarticUnitRightHalf]
      congr 2 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel]

private theorem reciprocalQuarticUnitReflected_rightHalf
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticUnitReflectedIntervals
        (reciprocalQuarticUnitRightHalf intervals) =
      reciprocalQuarticUnitLeftHalf
        (reciprocalQuarticUnitReflectedIntervals intervals) := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitRightHalf,
        reciprocalQuarticUnitReflectedIntervals]
      rw [ih]
      rw [reciprocalQuarticUnitLeftHalf_append]
      simp only [reciprocalQuarticUnitLeftHalf]
      congr 2 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel]

private theorem reciprocalQuarticUnitDyadicIntervals_reflected
    (stage : Nat) :
    reciprocalQuarticUnitReflectedIntervals
      (ArctanGeometry.arctanAreaLoopState 1 stage).intervals =
      (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
  induction stage with
  | zero =>
      decide +kernel
  | succ stage ih =>
      rw [reciprocalQuarticUnitDyadicIntervals_succ_split,
        reciprocalQuarticUnitReflected_append,
        reciprocalQuarticUnitReflected_rightHalf,
        reciprocalQuarticUnitReflected_leftHalf, ih]

private theorem reciprocalQuarticUnitLeftHalf_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval (a / 2) (b / 2)
      (reciprocalQuarticUnitLeftHalf intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp only [reciprocalQuarticUnitLeftHalf,
        ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      simp only [reciprocalQuarticUnitLeftHalf,
        ArctanGeometry.CoversInterval]
      refine ⟨trivial, ?_, ih r hrest⟩
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right hpr (by decide +kernel)

private theorem reciprocalQuarticUnitRightHalf_covers
    (a b : Rat) (intervals : List (Rat × Rat))
    (hcover : ArctanGeometry.CoversInterval a b intervals) :
    ArctanGeometry.CoversInterval ((a + 1) / 2) ((b + 1) / 2)
      (reciprocalQuarticUnitRightHalf intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp only [reciprocalQuarticUnitRightHalf,
        ArctanGeometry.CoversInterval] at hcover ⊢
      rw [hcover]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      simp only [reciprocalQuarticUnitRightHalf,
        ArctanGeometry.CoversInterval]
      refine ⟨trivial, ?_, ih r hrest⟩
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right
        ((Rat.add_le_add_right (c := (1 : Rat))).2 hpr) (by decide +kernel)

private theorem projectiveCompactDyadicEndpoint_succ (n : Nat) :
    (projectiveCompactDyadicEndpoint n + 1) / 2 =
      projectiveCompactDyadicEndpoint (n + 1) := by
  unfold projectiveCompactDyadicEndpoint
  have hpow : (((2 ^ (n + 1) : Nat) : Rat)) =
      (((2 ^ n : Nat) : Rat)) * 2 := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.pow_succ 2 n))
  rw [hpow, Rat.div_def, Rat.div_def]
  have hne : (((2 ^ n : Nat) : Rat)) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2
      (Nat.pow_pos (by omega : 0 < 2)))
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel]

/-- The positive dyadic mesh with its final endpoint cell removed.  This is
the literal trimmed core on which the projective coordinate is defined. -/
def reciprocalQuarticUnitDyadicCoreIntervals : Nat -> List (Rat × Rat)
  | 0 => []
  | n + 1 =>
      reciprocalQuarticUnitLeftHalf
        (ArctanGeometry.arctanAreaLoopState 1 n).intervals ++
      reciprocalQuarticUnitRightHalf
        (reciprocalQuarticUnitDyadicCoreIntervals n)

theorem reciprocalQuarticUnitDyadicCoreIntervals_covers
    (n : Nat) :
    ArctanGeometry.CoversInterval 0 (projectiveCompactDyadicEndpoint n)
      (reciprocalQuarticUnitDyadicCoreIntervals n) := by
  induction n with
  | zero =>
      change 0 = projectiveCompactDyadicEndpoint 0
      decide +kernel
  | succ n ih =>
      have hfull := ArctanGeometry.arctanAreaLoopState_intervals_covers
        (x := (1 : Rat)) (by decide +kernel) n
      have hleft := reciprocalQuarticUnitLeftHalf_covers 0 1
        (ArctanGeometry.arctanAreaLoopState 1 n).intervals hfull
      have hright := reciprocalQuarticUnitRightHalf_covers 0
        (projectiveCompactDyadicEndpoint n)
        (reciprocalQuarticUnitDyadicCoreIntervals n) ih
      have hzero : (0 : Rat) / 2 = 0 := by decide +kernel
      have hmid : (1 : Rat) / 2 = (0 + 1) / 2 := by decide +kernel
      rw [← hmid] at hright
      have hjoin := ArctanGeometry.CoversInterval.append hleft hright
      rw [hzero, projectiveCompactDyadicEndpoint_succ] at hjoin
      simpa [reciprocalQuarticUnitDyadicCoreIntervals] using hjoin

/-- The projective image of the literal trimmed compact core and the explicit
unit-plus-reciprocal-tail mesh are two finite Cauchy rectangle covers of the
same positive interval. -/
theorem projectiveCompactDyadicCoreIntervals_overlaps_cauchyAssembly
    (n mesh : Nat) :
    QInterval.Overlaps
      (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))))
      (ArctanGeometry.integralSumInterval
        (cauchyUnitReciprocalTailDyadicIntervals
          (projectiveCompactDyadicCauchyTailStart n) mesh)) := by
  have hcore := projectiveCompactIntervals_covers 0
    (projectiveCompactDyadicEndpoint (n + 2))
    (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))
    (by decide +kernel) (projectiveCompactDyadicEndpoint_lt_one _)
    (reciprocalQuarticUnitDyadicCoreIntervals_covers (n + 2))
  have hzero : projectiveCompactCoordinate (0 : Rat) = 0 := by
    decide +kernel
  rw [hzero] at hcore
  exact ArctanGeometry.integralSumInterval_overlaps_of_covers
    (by decide +kernel) _ _ hcore
    (projectiveCompactDyadicCauchyAssemblyIntervals_covers n mesh)

/-- The literal trimmed compact core and the fast projective schedule are
finite Lipschitz brackets for the same compact interval. -/
theorem reciprocalQuarticUnitDyadicCore_symmetric_overlaps_scheduled
    (n : Nat) :
    QInterval.Overlaps
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n))
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals) := by
  have hscheduled := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (projectiveCompactDyadicEndpoint_nonnegative n) (n * 6)
  have h := projectiveCompactLipschitzSum_overlaps_of_covers
    (a := 0) (b := projectiveCompactDyadicEndpoint n)
    (by decide +kernel) (Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n))
    (reciprocalQuarticUnitDyadicCoreIntervals n)
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint n) (n * 6)).intervals
    (reciprocalQuarticUnitDyadicCoreIntervals_covers n) hscheduled
  change
    2 * projectiveCompactLipschitzLowerSum
          (reciprocalQuarticUnitDyadicCoreIntervals n) <=
        2 * projectiveCompactLipschitzUpperSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals ∧
      2 * projectiveCompactLipschitzLowerSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals <=
        2 * projectiveCompactLipschitzUpperSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)
  exact ⟨Rat.mul_le_mul_of_nonneg_left h.1 (by decide +kernel),
    Rat.mul_le_mul_of_nonneg_left h.2 (by decide +kernel)⟩

/-- The factor-two compact bracket on the rapidly refined projective schedule
has an explicit source-mesh width bound. -/
theorem projectiveCompactDyadicScheduledCore_symmetric_width_le
    (n : Nat) :
    (projectiveCompactSymmetricLipschitzSum
      (ArctanGeometry.arctanAreaLoopState
        (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).width <=
      32 * (1 / (((2 ^ (n * 6) : Nat) : Rat))) := by
  rw [projectiveCompactSymmetricLipschitzSum_width_eq_thirtytwo_squareSum,
    ArctanGeometry.arctanAreaLoopState_squareSum]
  have hs0 : 0 <= projectiveCompactDyadicEndpoint n :=
    projectiveCompactDyadicEndpoint_nonnegative n
  have hs1 : projectiveCompactDyadicEndpoint n <= 1 :=
    Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n)
  have hsquare : projectiveCompactDyadicEndpoint n *
      projectiveCompactDyadicEndpoint n <= 1 := by
    calc
      projectiveCompactDyadicEndpoint n * projectiveCompactDyadicEndpoint n <=
          1 * projectiveCompactDyadicEndpoint n :=
        Rat.mul_le_mul_of_nonneg_right hs1 hs0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hs1 (by decide +kernel)
      _ = 1 := by decide +kernel
  have hDpos : 0 < (((2 ^ (n * 6) : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hsmall : (projectiveCompactDyadicEndpoint n *
      projectiveCompactDyadicEndpoint n) /
        (((2 ^ (n * 6) : Nat) : Rat)) <=
      1 / (((2 ^ (n * 6) : Nat) : Rat)) := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hsquare
      (Rat.le_of_lt ((Rat.inv_pos).2 hDpos))
  exact Rat.mul_le_mul_of_nonneg_left hsmall (by decide +kernel)

/-- The literal trimmed dyadic core is now within the proved projective
quadrature bridge: its factor-two compact bracket overlaps the matching
two-branch Cauchy rectangle bracket. -/
theorem reciprocalQuarticUnitDyadicCore_symmetric_overlaps_projective
    (n : Nat) :
    QInterval.Overlaps
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n))
      (projectiveCompactSymmetricIntegralSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)) := by
  exact projectiveCompactSymmetricLipschitzSum_overlaps_integralSum
    0 (projectiveCompactDyadicEndpoint n)
    (reciprocalQuarticUnitDyadicCoreIntervals n)
    (by decide +kernel) (projectiveCompactDyadicEndpoint_lt_one n)
    (reciprocalQuarticUnitDyadicCoreIntervals_covers n)

/-- The finite compact bracket consisting of the literal projective core plus
the certified upper budget for its two omitted endpoint cells. -/
def projectiveCompactDyadicCoreTailBracket (n : Nat) : QInterval :=
  { lo := (projectiveCompactSymmetricLipschitzSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).lo,
    hi := (projectiveCompactSymmetricLipschitzSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
        (projectiveCompactDyadicSymmetricTailError.compute n).hi }

/-- A projective Cauchy-core enclosure for the literal compact candidate.
Its additional lower and upper compact-core widths make the transfer from the
compact bracket sound using only finite interval overlap; the final summand is
the independently certified removable-endpoint budget. -/
def projectiveCauchyDyadicCoreTailEnvelope (n : Nat) : QInterval :=
  { lo := (projectiveCompactSymmetricIntegralSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).lo -
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).width,
    hi := (projectiveCompactSymmetricIntegralSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).width +
        (projectiveCompactDyadicSymmetricTailError.compute n).hi }

/-- The full positive dyadic mesh is its trimmed core followed by the one
cell that touches the removable chart endpoint. -/
theorem reciprocalQuarticUnitDyadicIntervals_eq_core_append_tail
    (n : Nat) :
    (ArctanGeometry.arctanAreaLoopState 1 n).intervals =
      reciprocalQuarticUnitDyadicCoreIntervals n ++
        [(projectiveCompactDyadicEndpoint n, 1)] := by
  induction n with
  | zero =>
      decide +kernel
  | succ n ih =>
      calc
        (ArctanGeometry.arctanAreaLoopState 1 (n.succ)).intervals =
            reciprocalQuarticUnitLeftHalf
              (ArctanGeometry.arctanAreaLoopState 1 n).intervals ++
              reciprocalQuarticUnitRightHalf
                (ArctanGeometry.arctanAreaLoopState 1 n).intervals := by
          simpa [Nat.succ_eq_add_one] using
            reciprocalQuarticUnitDyadicIntervals_succ_split n
        _ = reciprocalQuarticUnitLeftHalf
              (ArctanGeometry.arctanAreaLoopState 1 n).intervals ++
              reciprocalQuarticUnitRightHalf
                (reciprocalQuarticUnitDyadicCoreIntervals n ++
                  [(projectiveCompactDyadicEndpoint n, 1)]) := by
            rw [ih]
        _ = reciprocalQuarticUnitDyadicCoreIntervals n.succ ++
              [(projectiveCompactDyadicEndpoint n.succ, 1)] := by
            rw [reciprocalQuarticUnitRightHalf_append]
            simp only [reciprocalQuarticUnitRightHalf]
            rw [projectiveCompactDyadicEndpoint_succ]
            have hone : ((1 : Rat) + 1) / 2 = 1 := by decide +kernel
            rw [hone]
            simp [reciprocalQuarticUnitDyadicCoreIntervals, List.append_assoc]

private theorem intervalSquareSum_append
    (left right : List (Rat × Rat)) :
    ArctanGeometry.intervalSquareSum (left ++ right) =
      ArctanGeometry.intervalSquareSum left +
        ArctanGeometry.intervalSquareSum right := by
  induction left with
  | nil =>
      exact (Rat.zero_add _).symm
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append, ArctanGeometry.intervalSquareSum]
      rw [ih]
      grind [Rat.add_assoc]

/-- Omitting the final dyadic cell cannot increase the squared mesh of the
literal positive partition. -/
theorem reciprocalQuarticUnitDyadicCore_squareSum_le
    (n : Nat) :
    ArctanGeometry.intervalSquareSum
        (reciprocalQuarticUnitDyadicCoreIntervals n) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  have hsum := ArctanGeometry.arctanAreaLoopState_one_squareSum n
  rw [reciprocalQuarticUnitDyadicIntervals_eq_core_append_tail,
    intervalSquareSum_append] at hsum
  simp only [ArctanGeometry.intervalSquareSum, Rat.add_zero] at hsum
  have hwidth : 0 <= 1 - projectiveCompactDyadicEndpoint n := by
    have hendpoint := projectiveCompactDyadicEndpoint_lt_one n
    grind [Rat.sub_eq_add_neg]
  have htail : 0 <= (1 - projectiveCompactDyadicEndpoint n) *
      (1 - projectiveCompactDyadicEndpoint n) :=
    Rat.mul_nonneg hwidth hwidth
  calc
    ArctanGeometry.intervalSquareSum
          (reciprocalQuarticUnitDyadicCoreIntervals n) <=
        ArctanGeometry.intervalSquareSum
            (reciprocalQuarticUnitDyadicCoreIntervals n) +
          (1 - projectiveCompactDyadicEndpoint n) *
            (1 - projectiveCompactDyadicEndpoint n) := by
              grind
    _ = 1 / (((2 ^ n : Nat) : Rat)) := hsum

/-- The width lost when replacing the literal compact core by its projective
rectangle bracket decays at the same dyadic rate. -/
theorem reciprocalQuarticUnitDyadicCore_symmetric_width_le
    (n : Nat) :
    (projectiveCompactSymmetricLipschitzSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).width <=
      32 * (1 / (((2 ^ n : Nat) : Rat))) := by
  rw [projectiveCompactSymmetricLipschitzSum_width_eq_thirtytwo_squareSum]
  exact Rat.mul_le_mul_of_nonneg_left
    (reciprocalQuarticUnitDyadicCore_squareSum_le n) (by decide +kernel)

private theorem reciprocalQuarticMinusOneCompactAffineIntervals_append
    (left right : List (Rat × Rat)) :
    reciprocalQuarticMinusOneCompactAffineIntervals (left ++ right) =
      reciprocalQuarticMinusOneCompactAffineIntervals left ++
        reciprocalQuarticMinusOneCompactAffineIntervals right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [List.cons_append,
        reciprocalQuarticMinusOneCompactAffineIntervals]
      rw [ih]

private theorem reciprocalQuarticMinusOneCompactAffineIntervals_rightHalf
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticMinusOneCompactAffineIntervals
      (reciprocalQuarticUnitRightHalf intervals) = intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitRightHalf,
        reciprocalQuarticMinusOneCompactAffineIntervals]
      rw [ih]
      congr 1 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel]

private theorem reciprocalQuarticMinusOneCompactAffineIntervals_leftHalf_reflected
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticMinusOneCompactAffineIntervals
      (reciprocalQuarticUnitLeftHalf
        (reciprocalQuarticUnitReflectedIntervals intervals)) =
      projectiveCompactReflectedIntervals intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticUnitReflectedIntervals,
        reciprocalQuarticUnitLeftHalf_append,
        reciprocalQuarticMinusOneCompactAffineIntervals_append,
        projectiveCompactReflectedIntervals]
      rw [ih]
      simp only [reciprocalQuarticUnitLeftHalf,
        reciprocalQuarticMinusOneCompactAffineIntervals]
      congr 2 <;>
        grind [Rat.div_def, Rat.add_mul, Rat.mul_add, Rat.mul_assoc,
          Rat.mul_comm, Rat.mul_inv_cancel, Rat.sub_eq_add_neg]

/-- The affine image of each concrete dyadic mesh after its first refinement
is literally a reflected copy of the preceding positive mesh followed by that
positive mesh.  This is the exact finite partition split needed to connect the
candidate's left-endpoint bracket to the oriented symmetric projective core. -/
theorem reciprocalQuarticMinusOneCompactAffineDyadicIntervals_succ_eq_reflected_append
    (stage : Nat) :
    reciprocalQuarticMinusOneCompactAffineIntervals
      (ArctanGeometry.arctanAreaLoopState 1 (stage + 1)).intervals =
      projectiveCompactReflectedIntervals
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals ++
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
  rw [reciprocalQuarticUnitDyadicIntervals_succ_split,
    reciprocalQuarticMinusOneCompactAffineIntervals_append,
    reciprocalQuarticMinusOneCompactAffineIntervals_rightHalf]
  have hmirror := reciprocalQuarticUnitDyadicIntervals_reflected stage
  have hleft :
      reciprocalQuarticMinusOneCompactAffineIntervals
        (reciprocalQuarticUnitLeftHalf
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) =
        projectiveCompactReflectedIntervals
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
    calc
      reciprocalQuarticMinusOneCompactAffineIntervals
          (reciprocalQuarticUnitLeftHalf
            (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) =
          reciprocalQuarticMinusOneCompactAffineIntervals
            (reciprocalQuarticUnitLeftHalf
              (reciprocalQuarticUnitReflectedIntervals
                (ArctanGeometry.arctanAreaLoopState 1 stage).intervals)) := by
              rw [hmirror]
      _ = projectiveCompactReflectedIntervals
            (ArctanGeometry.arctanAreaLoopState 1 stage).intervals :=
        reciprocalQuarticMinusOneCompactAffineIntervals_leftHalf_reflected _
  rw [hleft]

private theorem reciprocalQuarticMinusOneUnit_lowerCell_eq_compact
    (p r : Rat) :
    reciprocalQuarticMinusOneUnitLowerCell p r =
      (2 * r - 1 - (2 * p - 1)) *
        (reciprocalQuarticSymmetricDensity (-1) (2 * p - 1) -
          8 * (2 * r - 1 - (2 * p - 1))) := by
  unfold reciprocalQuarticMinusOneUnitLowerCell Integral.lipschitzLowerCell
    reciprocalQuarticMinusOneUnitDensity
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem reciprocalQuarticMinusOneUnit_upperCell_eq_compact
    (p r : Rat) :
    reciprocalQuarticMinusOneUnitUpperCell p r =
      (2 * r - 1 - (2 * p - 1)) *
        (reciprocalQuarticSymmetricDensity (-1) (2 * p - 1) +
          8 * (2 * r - 1 - (2 * p - 1))) := by
  unfold reciprocalQuarticMinusOneUnitUpperCell Integral.lipschitzUpperCell
    reciprocalQuarticMinusOneUnitDensity
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Under the affine compactification, the concrete dyadic lower bracket is
exactly the compact density's 8-Lipschitz lower bracket. -/
theorem projectiveCompactLipschitzLowerSum_affine_eq_unitLowerSum
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzLowerSum
        (reciprocalQuarticMinusOneCompactAffineIntervals intervals) =
      reciprocalQuarticMinusOneUnitLowerSum intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticMinusOneCompactAffineIntervals,
        projectiveCompactLipschitzLowerSum,
        reciprocalQuarticMinusOneUnitLowerSum]
      rw [reciprocalQuarticMinusOneUnit_lowerCell_eq_compact, ih]

/-- The analogous affine identity for the concrete dyadic upper bracket. -/
theorem projectiveCompactLipschitzUpperSum_affine_eq_unitUpperSum
    (intervals : List (Rat × Rat)) :
    projectiveCompactLipschitzUpperSum
        (reciprocalQuarticMinusOneCompactAffineIntervals intervals) =
      reciprocalQuarticMinusOneUnitUpperSum intervals := by
  induction intervals with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [reciprocalQuarticMinusOneCompactAffineIntervals,
        projectiveCompactLipschitzUpperSum,
        reciprocalQuarticMinusOneUnitUpperSum]
      rw [reciprocalQuarticMinusOneUnit_upperCell_eq_compact, ih]

/-- The explicit two-sided dyadic bracket for the affine compact quartic
density.  Its centre is the ordinary left Riemann sum; its radius is supplied
cellwise from the proved rational Lipschitz estimate. -/
def reciprocalQuarticMinusOneUnitDyadicCompute (stage : Nat) : QInterval :=
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  { lo := reciprocalQuarticMinusOneUnitLowerSum cells
    hi := reciprocalQuarticMinusOneUnitUpperSum cells }

/-- The actual compact dyadic bracket is exactly a compact-density Lipschitz
bracket on the affine image of its unit partition. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_eq_affineCompact
    (stage : Nat) :
    reciprocalQuarticMinusOneUnitDyadicCompute stage =
      let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
      { lo := projectiveCompactLipschitzLowerSum
          (reciprocalQuarticMinusOneCompactAffineIntervals cells),
        hi := projectiveCompactLipschitzUpperSum
          (reciprocalQuarticMinusOneCompactAffineIntervals cells) } := by
  dsimp [reciprocalQuarticMinusOneUnitDyadicCompute]
  rw [projectiveCompactLipschitzLowerSum_affine_eq_unitLowerSum,
    projectiveCompactLipschitzUpperSum_affine_eq_unitUpperSum]

/-- After the initial dyadic refinement, the concrete compact candidate is
exactly the oriented symmetric bracket of the preceding positive unit mesh.
This is an equality of its actual rational interval computations, not an
auxiliary symmetric estimate. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_eq_orientedSymmetric
    (stage : Nat) :
    reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1) =
      projectiveCompactOrientedSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
  rw [reciprocalQuarticMinusOneUnitDyadicCompute_eq_affineCompact]
  dsimp
  rw [reciprocalQuarticMinusOneCompactAffineDyadicIntervals_succ_eq_reflected_append,
    projectiveCompactLipschitzLowerSum_reflected_append_eq_right_add_left,
    projectiveCompactLipschitzUpperSum_reflected_append_eq_right_add_left]
  rfl

/-- The actual compact candidate overlaps the earlier factor-two symmetric
bracket at the preceding dyadic stage.  The latter is the finite object already
connected to the positive projective Cauchy bridge. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_symmetric
    (stage : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1))
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState 1 stage).intervals) := by
  rw [reciprocalQuarticMinusOneUnitDyadicCompute_succ_eq_orientedSymmetric]
  exact projectiveCompactOrientedSymmetricLipschitzSum_overlaps_symmetric _
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (by decide +kernel) (by decide +kernel) stage)

/-- The actual compact candidate at stage `n+1` overlaps the literal trimmed
projective core together with the certified two-cell endpoint budget. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_coreTail
    (n : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1))
      (projectiveCompactDyadicCoreTailBracket n) := by
  let core := reciprocalQuarticUnitDyadicCoreIntervals n
  let tail : List (Rat × Rat) := [(projectiveCompactDyadicEndpoint n, 1)]
  have hcore_cover := reciprocalQuarticUnitDyadicCoreIntervals_covers n
  have hcore_unit : ArctanGeometry.UnitIntervals core := by
    dsimp [core]
    exact ArctanGeometry.CoversInterval.unit (by decide +kernel)
      (Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n)) hcore_cover
  have hcore := projectiveCompactOrientedSymmetricLipschitzSum_overlaps_symmetric
    core hcore_unit
  have htail_unit : ArctanGeometry.UnitIntervals tail := by
    dsimp [tail]
    exact ⟨projectiveCompactDyadicEndpoint_nonnegative n,
      Rat.le_of_lt (projectiveCompactDyadicEndpoint_lt_one n),
      Rat.le_refl, trivial⟩
  have htail_ordered :=
    projectiveCompactOrientedSymmetricLipschitzSum_ordered tail htail_unit
  have htail_upper :
      (projectiveCompactOrientedSymmetricLipschitzSum tail).hi <=
        (projectiveCompactDyadicSymmetricTailError.compute n).hi := by
    dsimp [tail, projectiveCompactOrientedSymmetricLipschitzSum]
    exact projectiveCompactDyadicOrientedTailUpper_le n
  have htail_nonneg : 0 <=
      (projectiveCompactOrientedSymmetricLipschitzSum tail).hi := by
    dsimp [tail, projectiveCompactOrientedSymmetricLipschitzSum]
    simp only [projectiveCompactLipschitzRightUpperSum,
      projectiveCompactLipschitzUpperSum]
    rw [Rat.add_zero, Rat.add_zero]
    have hwidth : 0 <= 1 - projectiveCompactDyadicEndpoint n := by
      exact Rat.le_of_lt (by
        dsimp [projectiveCompactDyadicEndpoint]
        rw [Rat.div_def]
        have hinv : 0 < (((2 ^ n : Nat) : Rat))⁻¹ := (Rat.inv_pos).2
          ((Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2)))
        have hpos : 0 < (1 : Rat) * (((2 ^ n : Nat) : Rat))⁻¹ :=
          Rat.mul_pos (by decide +kernel : (0 : Rat) < 1) hinv
        grind [Rat.sub_eq_add_neg])
    have hright : 0 <= reciprocalQuarticSymmetricDensity (-1) 1 +
        8 * (1 - projectiveCompactDyadicEndpoint n) := by
      exact Rat.add_nonneg
        (reciprocalQuarticSymmetricDensity_minus_one_nonneg 1)
        (Rat.mul_nonneg (by decide +kernel) hwidth)
    have hleft : 0 <= reciprocalQuarticSymmetricDensity (-1)
        (projectiveCompactDyadicEndpoint n) +
          8 * (1 - projectiveCompactDyadicEndpoint n) := by
      exact Rat.add_nonneg
        (reciprocalQuarticSymmetricDensity_minus_one_nonneg _)
        (Rat.mul_nonneg (by decide +kernel) hwidth)
    exact Rat.add_nonneg
      (Rat.mul_nonneg hwidth hright) (Rat.mul_nonneg hwidth hleft)
  have h := projectiveCompactOrientedSymmetric_append_overlaps_tailEnclosure
    core tail (projectiveCompactDyadicSymmetricTailError.compute n).hi
    hcore htail_ordered htail_upper htail_nonneg
  rw [reciprocalQuarticMinusOneUnitDyadicCompute_succ_eq_orientedSymmetric,
    reciprocalQuarticUnitDyadicIntervals_eq_core_append_tail]
  simpa [core, tail, projectiveCompactDyadicCoreTailBracket] using h

/-- The actual compact candidate reaches the projective Cauchy core at every
dyadic stage.  The compact-core width is included explicitly: interval
overlap alone is not transitively composable for arbitrary finite boxes. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_projectiveCauchyCoreTail
    (n : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1))
      (projectiveCauchyDyadicCoreTailEnvelope n) := by
  have hcandidate := reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_coreTail n
  have hcore := reciprocalQuarticUnitDyadicCore_symmetric_overlaps_projective n
  unfold QInterval.Overlaps at hcandidate hcore ⊢
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
          (projectiveCompactDyadicSymmetricTailError.compute n).hi /\
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).hi at hcandidate
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).lo <=
        (projectiveCompactSymmetricIntegralSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width +
          (projectiveCompactDyadicSymmetricTailError.compute n).hi /\
      (projectiveCompactSymmetricIntegralSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).lo -
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).hi
  constructor
  · have hwidth :
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).hi <=
          (projectiveCompactSymmetricIntegralSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
            (projectiveCompactSymmetricLipschitzSum
              (reciprocalQuarticUnitDyadicCoreIntervals n)).width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans hcandidate.1 (by grind)
  · have hwidth :
        (projectiveCompactSymmetricIntegralSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).lo -
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width <=
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).lo := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans hwidth hcandidate.2

/-- A common compact enclosure for the literal dyadic candidate and the
rapidly refined projective schedule.  The literal core width is spent on both
sides of the finite cover comparison, while the removable endpoint budget is
needed only above. -/
def projectiveCompactDyadicScheduledCompactTailEnvelope (n : Nat) : QInterval :=
  { lo := (projectiveCompactSymmetricLipschitzSum
      (ArctanGeometry.arctanAreaLoopState
        (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).lo -
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)).width,
    hi := (projectiveCompactSymmetricLipschitzSum
      (ArctanGeometry.arctanAreaLoopState
        (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).hi +
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)).width +
      (projectiveCompactDyadicSymmetricTailError.compute n).hi }

/-- The actual compact dyadic box is enclosed by the fast compact schedule
after paying only the checked literal-core width and endpoint-cell budget. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_scheduledCompactTail
    (n : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1))
      (projectiveCompactDyadicScheduledCompactTailEnvelope n) := by
  have hcandidate := reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_coreTail n
  have hcore := reciprocalQuarticUnitDyadicCore_symmetric_overlaps_scheduled n
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).hi +
          (projectiveCompactDyadicSymmetricTailError.compute n).hi /\
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).hi at hcandidate
  change
    (projectiveCompactSymmetricLipschitzSum
      (reciprocalQuarticUnitDyadicCoreIntervals n)).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).hi /\
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).hi at hcore
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).hi +
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width +
          (projectiveCompactDyadicSymmetricTailError.compute n).hi /\
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).lo -
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 1)).hi
  have hupper :
      (projectiveCompactSymmetricLipschitzSum
        (reciprocalQuarticUnitDyadicCoreIntervals n)).hi <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).hi +
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hlower :
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint n) (n * 6)).intervals).lo -
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals n)).width <=
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals n)).lo := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  constructor
  · exact Rat.le_trans hcandidate.1 (by grind)
  · exact Rat.le_trans hlower hcandidate.2

/-- A symmetric Cauchy envelope for the literal compact candidate.  The
positive scheduled Cauchy bridge is scaled by two for the two compact chart
branches; the two finite compact bracket widths are recorded explicitly. -/
def projectiveCompactDyadicScheduledCauchyCandidateEnvelope (n : Nat) : QInterval :=
  { lo := 2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo -
      ((projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width +
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width),
    hi := 2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi +
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width +
        (projectiveCompactSymmetricLipschitzSum
          (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width +
        (projectiveCompactDyadicSymmetricTailError.compute (n + 2)).hi }

/-- The actual compact candidate meets the two-branch scheduled Cauchy
envelope.  Every widening in this finite transfer is a separately proved
compact bracket width or removable-endpoint error. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_scheduledCauchy
    (n : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1))
      (projectiveCompactDyadicScheduledCauchyCandidateEnvelope n) := by
  have hcandidate :=
    reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_scheduledCompactTail (n + 2)
  have hsource := ArctanGeometry.arctanAreaLoopState_intervals_covers
    (projectiveCompactDyadicEndpoint_nonnegative (n + 2)) ((n + 2) * 6)
  have hquad := projectiveCompactSymmetricLipschitzSum_overlaps_integralSum
    0 (projectiveCompactDyadicEndpoint (n + 2))
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
    (by decide +kernel) (projectiveCompactDyadicEndpoint_lt_one _) hsource
  have hbridge := projectiveCompactDyadicScheduledCauchyBridgeEnvelope_contains_core n
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).hi +
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width +
          (projectiveCompactDyadicSymmetricTailError.compute (n + 2)).hi /\
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).lo -
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).hi at hcandidate
  change
    (projectiveCompactSymmetricLipschitzSum
      (ArctanGeometry.arctanAreaLoopState
        (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).lo <=
        (projectiveCompactSymmetricIntegralSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).hi /\
      (projectiveCompactSymmetricIntegralSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).lo <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).hi at hquad
  change
    (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo <=
      (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)).lo /\
    (ArctanGeometry.integralSumInterval
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)).hi <=
      (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi at hbridge
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).lo <=
        2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi +
          (projectiveCompactSymmetricLipschitzSum
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width +
          (projectiveCompactSymmetricLipschitzSum
            (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width +
          (projectiveCompactDyadicSymmetricTailError.compute (n + 2)).hi /\
      2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo -
          ((projectiveCompactSymmetricLipschitzSum
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width +
            (projectiveCompactSymmetricLipschitzSum
              (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))).width) <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).hi
  have hbridgeHi :
      2 * (ArctanGeometry.integralSumInterval
        (projectiveCompactIntervals
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)).hi <=
        2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi :=
    Rat.mul_le_mul_of_nonneg_left hbridge.2 (by decide +kernel)
  have hbridgeLo :
      2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo <=
        2 * (ArctanGeometry.integralSumInterval
          (projectiveCompactIntervals
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)).lo :=
    Rat.mul_le_mul_of_nonneg_left hbridge.1 (by decide +kernel)
  have hupper :
      (projectiveCompactSymmetricLipschitzSum
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).hi <=
        2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi +
          (projectiveCompactSymmetricLipschitzSum
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width := by
    unfold projectiveCompactSymmetricIntegralSum at hquad
    have hbridgeHi' :
        2 * ArctanGeometry.integralUpperSum
          (projectiveCompactIntervals
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals) <=
          2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).hi := by
      simpa [ArctanGeometry.integralSumInterval] using hbridgeHi
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hlower :
      2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo -
          (projectiveCompactSymmetricLipschitzSum
            (ArctanGeometry.arctanAreaLoopState
              (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).width <=
        (projectiveCompactSymmetricLipschitzSum
          (ArctanGeometry.arctanAreaLoopState
            (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals).lo := by
    unfold projectiveCompactSymmetricIntegralSum at hquad
    have hbridgeLo' :
        2 * (projectiveCompactDyadicScheduledCauchyBridgeEnvelope n).lo <=
          2 * ArctanGeometry.integralLowerSum
            (projectiveCompactIntervals
              (ArctanGeometry.arctanAreaLoopState
                (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals) := by
      simpa [ArctanGeometry.integralSumInterval] using hbridgeLo
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  constructor
  · exact Rat.le_trans hcandidate.1 (by grind)
  · exact Rat.le_trans (by grind) hcandidate.2

/-- A common full-line Cauchy enclosure for the projective quartic candidate.
It combines the two-branch projective bridge with the standard four-unit-mesh
representation of the completed Cauchy full-line raw. -/
def projectiveCompactDyadicFullCauchyEnvelope (n : Nat) : QInterval :=
  let unit := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals
  let a := projectiveCompactDyadicCauchyTailStart n
  let tail := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a (5 * n + 8))
  let bridge := projectiveCompactDyadicScheduledCauchyBridgeEnvelope n
  let scheduled := projectiveCompactSymmetricLipschitzSum
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
  let literal := projectiveCompactSymmetricLipschitzSum
    (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))
  let endpoint := projectiveCompactDyadicSymmetricTailError.compute (n + 2)
  { lo := 4 * unit.lo -
      (2 * (a + tail.width) + 2 * bridge.width +
        scheduled.width + literal.width),
    hi := 4 * unit.hi +
      2 * (a + tail.width) + 2 * bridge.width +
        scheduled.width + literal.width + endpoint.hi }

private theorem intervalSquareSum_nonnegative
    (intervals : List (Rat × Rat)) :
    0 <= ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [ArctanGeometry.intervalSquareSum]
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp only [ArctanGeometry.intervalSquareSum]
      exact Rat.add_nonneg (rat_square_nonneg (r - p)) ih

/-- The full Cauchy envelope contains the completed Cauchy raw at its
four-unit-mesh stage. -/
theorem projectiveCompactDyadicFullCauchyEnvelope_contains_cauchyFullLine
    (n : Nat) :
    (projectiveCompactDyadicFullCauchyEnvelope n).ContainsInterval
      (cauchyFullLineIntegral.compute (5 * n + 8)) := by
  let unit : QInterval := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals
  let a : Rat := projectiveCompactDyadicCauchyTailStart n
  let tail : QInterval := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a (5 * n + 8))
  let bridge : QInterval := projectiveCompactDyadicScheduledCauchyBridgeEnvelope n
  let scheduled : QInterval := projectiveCompactSymmetricLipschitzSum
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
  let literal : QInterval := projectiveCompactSymmetricLipschitzSum
    (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))
  let endpoint : QInterval := projectiveCompactDyadicSymmetricTailError.compute (n + 2)
  have ha0 : 0 <= a := Rat.le_of_lt (projectiveCompactDyadicCauchyTailStart_pos n)
  have htail0 : 0 <= tail.width := by
    dsimp [tail]
    exact ArctanGeometry.integralSumInterval_ordered _
      (ArctanGeometry.CoversInterval.nonnegative ha0
        (cauchyTailDyadicIntervals_covers ha0
          (projectiveCompactDyadicCauchyTailStart_le_one n) (5 * n + 8)))
  have hbridge0 : 0 <= bridge.width := by
    let core : QInterval := ArctanGeometry.integralSumInterval
      (projectiveCompactIntervals
        (ArctanGeometry.arctanAreaLoopState
          (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals)
    let assembly : QInterval := ArctanGeometry.integralSumInterval
      (cauchyUnitReciprocalTailDyadicIntervals
        (projectiveCompactDyadicCauchyTailStart n) (5 * n + 8))
    have hsource := ArctanGeometry.arctanAreaLoopState_intervals_covers
      (projectiveCompactDyadicEndpoint_nonnegative (n + 2)) ((n + 2) * 6)
    have hcore0 : 0 <= core.width := by
      dsimp [core]
      exact ArctanGeometry.integralSumInterval_ordered _
        (projectiveCompactIntervals_nonnegative 0
          (projectiveCompactDyadicEndpoint (n + 2)) _ (by decide +kernel)
          (projectiveCompactDyadicEndpoint_lt_one _) hsource)
    have hassembly0 : 0 <= assembly.width := by
      dsimp [assembly]
      exact ArctanGeometry.integralSumInterval_ordered _
        (ArctanGeometry.CoversInterval.nonnegative (by decide +kernel)
          (projectiveCompactDyadicCauchyAssemblyIntervals_covers n (5 * n + 8)))
    change 0 <= (QInterval.hull core assembly).width
    unfold QInterval.width QInterval.hull at *
    have hmin : min core.lo assembly.lo <= core.lo := by grind
    have hmax : core.hi <= max core.hi assembly.hi := by grind
    grind [Rat.sub_eq_add_neg]
  have hscheduled0 : 0 <= scheduled.width := by
    dsimp [scheduled]
    rw [projectiveCompactSymmetricLipschitzSum_width_eq_thirtytwo_squareSum]
    exact Rat.mul_nonneg (by decide +kernel) (intervalSquareSum_nonnegative _)
  have hliteral0 : 0 <= literal.width := by
    dsimp [literal]
    rw [projectiveCompactSymmetricLipschitzSum_width_eq_thirtytwo_squareSum]
    exact Rat.mul_nonneg (by decide +kernel) (intervalSquareSum_nonnegative _)
  have hendpoint0 : 0 <= endpoint.hi := by
    dsimp [endpoint]
    rw [projectiveCompactDyadicSymmetricTailError_compute]
    exact Rat.mul_nonneg (by decide +kernel)
      (by
        have hDpos : 0 < (((2 ^ (n + 2) : Nat) : Rat)) :=
          (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
        rw [Rat.div_def]
        exact Rat.mul_nonneg (by decide +kernel)
          (Rat.le_of_lt ((Rat.inv_pos).2 hDpos)))
  rw [cauchyFullLineIntegral_compute_eq_four_rectangle]
  change (projectiveCompactDyadicFullCauchyEnvelope n).ContainsInterval
    (RealCompute.scaleRatCompute 4 arctanIntegralRectangleForAtOne (5 * n + 8))
  unfold RealCompute.scaleRatCompute
  rw [if_pos (by decide +kernel : (0 : Rat) <= 4)]
  rw [arctanIntegralRectangleForAtOne_compute_eq]
  change
    4 * unit.lo -
        (2 * (a + tail.width) + 2 * bridge.width +
          scheduled.width + literal.width) <= 4 * unit.lo /\
      4 * unit.hi <= 4 * unit.hi +
        2 * (a + tail.width) + 2 * bridge.width +
          scheduled.width + literal.width + endpoint.hi
  grind [Rat.sub_eq_add_neg]

/-- The literal compact candidate reaches the full-line Cauchy envelope at a
finite stage.  The only bridge costs are explicit widths already certified on
the compact and Cauchy sides. -/
theorem reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_fullCauchy
    (n : Nat) :
    QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1))
      (projectiveCompactDyadicFullCauchyEnvelope n) := by
  let unit : QInterval := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals
  let a : Rat := projectiveCompactDyadicCauchyTailStart n
  let tail : QInterval := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a (5 * n + 8))
  let assembly : QInterval := ArctanGeometry.integralSumInterval
    (cauchyUnitReciprocalTailDyadicIntervals a (5 * n + 8))
  let bridge : QInterval := projectiveCompactDyadicScheduledCauchyBridgeEnvelope n
  let scheduled : QInterval := projectiveCompactSymmetricLipschitzSum
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
  let literal : QInterval := projectiveCompactSymmetricLipschitzSum
    (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))
  let endpoint : QInterval := projectiveCompactDyadicSymmetricTailError.compute (n + 2)
  have hcandidate :=
    reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_scheduledCauchy n
  have hassembly := cauchyUnitReciprocalTailDyadicIntervals_overlaps_twoUnitEnvelope
    (a := a) (projectiveCompactDyadicCauchyTailStart_pos n)
    (projectiveCompactDyadicCauchyTailStart_le_one n) (5 * n + 8)
  have hbridge := projectiveCompactDyadicScheduledCauchyBridgeEnvelope_contains_assembly n
  have ha0 : 0 <= a := Rat.le_of_lt (projectiveCompactDyadicCauchyTailStart_pos n)
  have hcandidate' : QInterval.Overlaps
      (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1))
      { lo := 2 * bridge.lo - (scheduled.width + literal.width),
        hi := 2 * bridge.hi + scheduled.width + literal.width + endpoint.hi } := by
    simpa [bridge, scheduled, literal, endpoint,
      projectiveCompactDyadicScheduledCauchyCandidateEnvelope] using hcandidate
  have hassembly' : QInterval.Overlaps assembly
      { lo := 2 * unit.lo - (a + tail.width),
        hi := 2 * unit.hi + tail.width } := by
    simpa [assembly, unit, tail,
      cauchyUnitReciprocalTailDyadicUnitEnvelope] using hassembly
  have hbridge' : bridge.ContainsInterval assembly := by
    simpa [bridge, assembly, a] using hbridge
  have hbridgeHi : bridge.hi <= assembly.lo + bridge.width := by
    unfold QInterval.ContainsInterval at hbridge'
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hbridgeLo : assembly.hi - bridge.width <= bridge.lo := by
    unfold QInterval.ContainsInterval at hbridge'
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  change assembly.lo <= 2 * unit.hi + tail.width /\
      2 * unit.lo - (a + tail.width) <= assembly.hi at hassembly'
  have hhigh : 2 * bridge.hi <=
      4 * unit.hi + 2 * (a + tail.width) + 2 * bridge.width := by
    have hbridgeHi2 : 2 * bridge.hi <=
        2 * (assembly.lo + bridge.width) :=
      Rat.mul_le_mul_of_nonneg_left hbridgeHi (by decide +kernel)
    have hassemblyLo2 : 2 * assembly.lo <=
        2 * (2 * unit.hi + tail.width) :=
      Rat.mul_le_mul_of_nonneg_left hassembly'.1 (by decide +kernel)
    calc
      2 * bridge.hi <= 2 * (assembly.lo + bridge.width) := hbridgeHi2
      _ = 2 * assembly.lo + 2 * bridge.width := by
        grind [Rat.mul_add]
      _ <= 2 * (2 * unit.hi + tail.width) + 2 * bridge.width :=
        rat_add_le_add hassemblyLo2 Rat.le_refl
      _ = 4 * unit.hi + 2 * tail.width + 2 * bridge.width := by
        grind
      _ <= 4 * unit.hi + 2 * (a + tail.width) + 2 * bridge.width := by
        grind
  have hlow :
      4 * unit.lo - (2 * (a + tail.width) + 2 * bridge.width) <=
        2 * bridge.lo := by
    have hbridgeLo2 : 2 * (assembly.hi - bridge.width) <=
        2 * bridge.lo :=
      Rat.mul_le_mul_of_nonneg_left hbridgeLo (by decide +kernel)
    have hassemblyHi2 : 2 * (2 * unit.lo - (a + tail.width)) <=
        2 * assembly.hi :=
      Rat.mul_le_mul_of_nonneg_left hassembly'.2 (by decide +kernel)
    calc
      4 * unit.lo - (2 * (a + tail.width) + 2 * bridge.width) =
          2 * (2 * unit.lo - (a + tail.width)) - 2 * bridge.width := by
            grind [Rat.sub_eq_add_neg]
      _ <= 2 * assembly.hi - 2 * bridge.width := by
        simpa [Rat.sub_eq_add_neg] using
          (rat_add_le_add hassemblyHi2 Rat.le_refl)
      _ = 2 * (assembly.hi - bridge.width) := by
        grind [Rat.sub_eq_add_neg]
      _ <= 2 * bridge.lo := hbridgeLo2
  change
    (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).lo <=
        4 * unit.hi + 2 * (a + tail.width) + 2 * bridge.width +
          scheduled.width + literal.width + endpoint.hi /\
      4 * unit.lo -
          (2 * (a + tail.width) + 2 * bridge.width +
            scheduled.width + literal.width) <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (n + 2 + 1)).hi
  exact ⟨Rat.le_trans hcandidate'.1 (by grind),
    Rat.le_trans (by grind) hcandidate'.2⟩

/-- Splitting one unit cell at its rational midpoint tightens the elementary
Lipschitz rectangle.  This is the finite refinement inequality from which the
raw interval algorithm will obtain nestedness. -/
private theorem reciprocalQuarticMinusOneUnit_cells_refine
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    let q := (p + r) / 2
    reciprocalQuarticMinusOneUnitLowerCell p r <=
      reciprocalQuarticMinusOneUnitLowerCell p q +
        reciprocalQuarticMinusOneUnitLowerCell q r /\
    reciprocalQuarticMinusOneUnitUpperCell p q +
        reciprocalQuarticMinusOneUnitUpperCell q r <=
      reciprocalQuarticMinusOneUnitUpperCell p r := by
  have hlip : Integral.LipschitzOnUnit reciprocalQuarticMinusOneUnitDensity 32 :=
    ⟨by decide +kernel,
      fun s t hs0 hs1 ht0 ht1 =>
        reciprocalQuarticMinusOneUnitDensity_lipschitz_on_unit
          s t hs0 hs1 ht0 ht1⟩
  simpa [reciprocalQuarticMinusOneUnitLowerCell,
    reciprocalQuarticMinusOneUnitUpperCell] using
    (Integral.lipschitzCells_refine hlip hp0 hpr hr1)

private theorem reciprocalQuarticMinusOneUnit_lowerSum_refineAux
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitLowerSum intervals <=
      reciprocalQuarticMinusOneUnitLowerSum
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := reciprocalQuarticMinusOneUnit_cells_refine hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitLowerSum] at htail ⊢
      calc
        reciprocalQuarticMinusOneUnitLowerCell p r +
            reciprocalQuarticMinusOneUnitLowerSum rest <=
            (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
              reciprocalQuarticMinusOneUnitLowerSum rest :=
          rat_add_le_add hcell.1 Rat.le_refl
        _ <= (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
              reciprocalQuarticMinusOneUnitLowerSum
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals :=
          by
            have hsum :
                (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
                  reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
                    reciprocalQuarticMinusOneUnitLowerSum rest <=
                (reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
                  reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r) +
                    reciprocalQuarticMinusOneUnitLowerSum
                      (ArctanGeometry.AreaLoopState.refineAux
                        (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                        (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                        rest).intervals :=
              rat_add_le_add Rat.le_refl htail
            grind [Rat.add_assoc]
        _ = reciprocalQuarticMinusOneUnitLowerCell p ((p + r) / 2) +
              (reciprocalQuarticMinusOneUnitLowerCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitLowerSum
                  (ArctanGeometry.AreaLoopState.refineAux
                    (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                    (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                    rest).intervals) := by
            grind [Rat.add_assoc]

private theorem reciprocalQuarticMinusOneUnit_upperSum_refineAux
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitUpperSum
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals <=
      reciprocalQuarticMinusOneUnitUpperSum intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := reciprocalQuarticMinusOneUnit_cells_refine hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux,
        reciprocalQuarticMinusOneUnitUpperSum] at htail ⊢
      calc
        reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
            (reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
              reciprocalQuarticMinusOneUnitUpperSum
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals) =
            reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitUpperSum
                  (ArctanGeometry.AreaLoopState.refineAux
                    (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                    (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                    rest).intervals := by
              grind [Rat.add_assoc]
        _ <= reciprocalQuarticMinusOneUnitUpperCell p ((p + r) / 2) +
              reciprocalQuarticMinusOneUnitUpperCell ((p + r) / 2) r +
                reciprocalQuarticMinusOneUnitUpperSum rest :=
          rat_add_le_add Rat.le_refl htail
        _ <= reciprocalQuarticMinusOneUnitUpperCell p r +
              reciprocalQuarticMinusOneUnitUpperSum rest :=
          rat_add_le_add hcell.2 Rat.le_refl

theorem reciprocalQuarticMinusOneUnitDyadicCompute_step_refines (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).lo <=
      (reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1)).lo /\
    (reciprocalQuarticMinusOneUnitDyadicCompute (stage + 1)).hi <=
      (reciprocalQuarticMinusOneUnitDyadicCompute stage).hi := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute
  rw [show stage + 1 = Nat.succ stage by omega,
    ArctanGeometry.arctanAreaLoopState_succ]
  dsimp
  let state := ArctanGeometry.arctanAreaLoopState 1 stage
  have hunit : ArctanGeometry.UnitIntervals state.intervals :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  constructor
  · exact reciprocalQuarticMinusOneUnit_lowerSum_refineAux
      state.lo state.hi state.intervals hunit
  · exact reciprocalQuarticMinusOneUnit_upperSum_refineAux
      state.lo state.hi state.intervals hunit

private theorem reciprocalQuarticMinusOneUnit_lowerCell_le_upperCell
    {p r : Rat} (hpr : p <= r) :
    reciprocalQuarticMinusOneUnitLowerCell p r <=
      reciprocalQuarticMinusOneUnitUpperCell p r := by
  have hwidth : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hinner :
      reciprocalQuarticMinusOneUnitDensity p - 32 * (r - p) <=
        reciprocalQuarticMinusOneUnitDensity p + 32 * (r - p) := by
    have hterm : 0 <= 32 * (r - p) :=
      Rat.mul_nonneg (by decide +kernel) hwidth
    grind [Rat.sub_eq_add_neg]
  unfold reciprocalQuarticMinusOneUnitLowerCell
    reciprocalQuarticMinusOneUnitUpperCell
  exact Rat.mul_le_mul_of_nonneg_left hinner hwidth

private theorem reciprocalQuarticMinusOneUnit_lowerSum_le_upperSum
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    reciprocalQuarticMinusOneUnitLowerSum intervals <=
      reciprocalQuarticMinusOneUnitUpperSum intervals := by
  induction intervals with
  | nil =>
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum]
      exact rat_add_le_add
        (reciprocalQuarticMinusOneUnit_lowerCell_le_upperCell hpr)
        (ih hrest)

private theorem reciprocalQuarticMinusOneUnit_cell_width
    (p r : Rat) :
    reciprocalQuarticMinusOneUnitUpperCell p r -
        reciprocalQuarticMinusOneUnitLowerCell p r =
      64 * ((r - p) * (r - p)) := by
  change
    (r - p) * (reciprocalQuarticMinusOneUnitDensity p + 32 * (r - p)) -
        (r - p) * (reciprocalQuarticMinusOneUnitDensity p - 32 * (r - p)) =
      64 * ((r - p) * (r - p))
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem reciprocalQuarticMinusOneUnit_sum_width
    (intervals : List (Rat × Rat)) :
    reciprocalQuarticMinusOneUnitUpperSum intervals -
        reciprocalQuarticMinusOneUnitLowerSum intervals =
      64 * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum,
        ArctanGeometry.intervalSquareSum]
      decide +kernel
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      have hcell := reciprocalQuarticMinusOneUnit_cell_width p r
      simp [reciprocalQuarticMinusOneUnitLowerSum,
        reciprocalQuarticMinusOneUnitUpperSum,
        ArctanGeometry.intervalSquareSum]
      calc
        reciprocalQuarticMinusOneUnitUpperCell p r +
              reciprocalQuarticMinusOneUnitUpperSum rest -
            (reciprocalQuarticMinusOneUnitLowerCell p r +
              reciprocalQuarticMinusOneUnitLowerSum rest) =
            (reciprocalQuarticMinusOneUnitUpperCell p r -
              reciprocalQuarticMinusOneUnitLowerCell p r) +
              (reciprocalQuarticMinusOneUnitUpperSum rest -
                reciprocalQuarticMinusOneUnitLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ = 64 * ((r - p) * (r - p)) +
              64 * ArctanGeometry.intervalSquareSum rest := by
              rw [hcell, ih]
        _ = 64 * ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_ordered (stage : Nat) :
    0 <= (reciprocalQuarticMinusOneUnitDyadicCompute stage).width := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute QInterval.width
  dsimp
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hunit : ArctanGeometry.UnitIntervals cells :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  have hsum := reciprocalQuarticMinusOneUnit_lowerSum_le_upperSum cells hunit
  grind [Rat.sub_eq_add_neg]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_width (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).width =
      64 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  unfold reciprocalQuarticMinusOneUnitDyadicCompute QInterval.width
  dsimp
  rw [reciprocalQuarticMinusOneUnit_sum_width,
    ArctanGeometry.arctanAreaLoopState_one_squareSum]

theorem reciprocalQuarticMinusOneUnitDyadicCompute_nested
    (n m : Nat) (hnm : n <= m) :
    (reciprocalQuarticMinusOneUnitDyadicCompute n).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute m).lo /\
      (reciprocalQuarticMinusOneUnitDyadicCompute m).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute m).hi /\
      (reciprocalQuarticMinusOneUnitDyadicCompute m).hi <=
        (reciprocalQuarticMinusOneUnitDyadicCompute n).hi := by
  induction hnm with
  | refl =>
      have hordered := reciprocalQuarticMinusOneUnitDyadicCompute_ordered n
      unfold QInterval.width at hordered
      have hmid :
          (reciprocalQuarticMinusOneUnitDyadicCompute n).lo <=
            (reciprocalQuarticMinusOneUnitDyadicCompute n).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_refl, hmid, Rat.le_refl⟩
  | step hnm ih =>
      rename_i k
      have hstep := reciprocalQuarticMinusOneUnitDyadicCompute_step_refines k
      have hordered :=
        reciprocalQuarticMinusOneUnitDyadicCompute_ordered (k + 1)
      unfold QInterval.width at hordered
      have hmid :
          (reciprocalQuarticMinusOneUnitDyadicCompute (k + 1)).lo <=
            (reciprocalQuarticMinusOneUnitDyadicCompute (k + 1)).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_trans ih.1 hstep.1, hmid,
        Rat.le_trans hstep.2 ih.2.2⟩

private theorem reciprocalQuarticMinusOneUnit_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

theorem reciprocalQuarticMinusOneUnitDyadicCompute_width_le_nat_over_succ
    (stage : Nat) :
    (reciprocalQuarticMinusOneUnitDyadicCompute stage).width <=
      (64 : Rat) / (((stage + 1 : Nat) : Rat)) := by
  rw [reciprocalQuarticMinusOneUnitDyadicCompute_width]
  have hpow : stage + 1 <= 2 ^ stage :=
    reciprocalQuarticMinusOneUnit_succ_le_two_pow stage
  have hinv :
      1 / (((2 ^ stage : Nat) : Rat)) <=
        1 / (((stage + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone (Nat.succ_pos stage)
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  calc
    64 * (1 / (((2 ^ stage : Nat) : Rat))) <=
      64 * (1 / (((stage + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hinv (by decide +kernel)
    _ = (64 : Rat) / (((stage + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]

private theorem reciprocalQuarticMinusOneUnit_widthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealCompute.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem reciprocalQuarticMinusOneUnitDyadicCompute_widthsShrink :
    RealCompute.WidthsShrinkToZero reciprocalQuarticMinusOneUnitDyadicCompute :=
  reciprocalQuarticMinusOneUnit_widthsShrink_of_natOverSuccBound
    reciprocalQuarticMinusOneUnitDyadicCompute_width_le_nat_over_succ

/-- The completed raw interval algorithm obtained from the dyadic Lipschitz
brackets.  At stage n its width is exactly 64 divided by 2^n; its nestedness
comes from the finite midpoint-refinement inequalities above. -/
def reciprocalQuarticMinusOneUnitDyadicRaw : RealCompute where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute

theorem reciprocalQuarticMinusOneUnitDyadicRaw_valid :
    reciprocalQuarticMinusOneUnitDyadicRaw.Valid := by
  change RealCompute.ValidCompute reciprocalQuarticMinusOneUnitDyadicCompute
  exact ⟨reciprocalQuarticMinusOneUnitDyadicCompute_ordered,
    reciprocalQuarticMinusOneUnitDyadicCompute_nested,
    reciprocalQuarticMinusOneUnitDyadicCompute_widthsShrink⟩

/-- The exact rational-name evaluator for the affine compact density. -/
def reciprocalQuarticMinusOneUnitRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun t _ _ =>
    let y := reciprocalQuarticMinusOneUnitDensity t
    { lo := y, hi := y }

/-- The affine compact quartic density as a total interval function on
[0,1]. -/
def reciprocalQuarticMinusOneUnitOnInterval : FunctionOnInterval where
  raw := reciprocalQuarticMinusOneUnitRaw
  lower := 0
  upper := 1
  defined_on := fun _ _ => trivial
  valid_on := by
    intro t _ht
    simpa [reciprocalQuarticMinusOneUnitRaw] using
      RealCompute.ofRat_valid (reciprocalQuarticMinusOneUnitDensity t)

/-- The concrete domain-aware integral construction for the affine compact
quartic density.  Unlike the earlier unconstrained placeholder interface, its
computation is visibly the finite left-cell Lipschitz bracket defined above. -/
def reciprocalQuarticMinusOneUnitDyadicConstruction :
    Integral.CandidateConstructionFor reciprocalQuarticMinusOneUnitOnInterval where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute
  certificate := reciprocalQuarticMinusOneUnitDyadicRaw_valid

def reciprocalQuarticMinusOneUnitDyadicIntegral : RealCompute :=
  Integral.candidateValueFor reciprocalQuarticMinusOneUnitOnInterval
    reciprocalQuarticMinusOneUnitDyadicConstruction

theorem reciprocalQuarticMinusOneUnitDyadicIntegral_valid :
    reciprocalQuarticMinusOneUnitDyadicIntegral.Valid :=
  Integral.candidateValueFor_valid reciprocalQuarticMinusOneUnitOnInterval
    reciprocalQuarticMinusOneUnitDyadicConstruction

theorem reciprocalQuarticMinusOneUnitDyadicIntegral_compute_eq (stage : Nat) :
    reciprocalQuarticMinusOneUnitDyadicIntegral.compute stage =
      reciprocalQuarticMinusOneUnitDyadicCompute stage :=
  rfl

/-- The affine unit density is the compact density composed with
x = 2t - 1, multiplied by its rational Jacobian. -/
theorem reciprocalQuarticMinusOneUnitDensity_eq_affineCompact (t : Rat) :
    reciprocalQuarticMinusOneUnitDensity t =
      2 * reciprocalQuarticSymmetricDensity (-1) (2 * t - 1) :=
  rfl

/-- The same dyadic bracket, now packaged for the actual compact density on
[-1,1].  Its finite cell expression is the affine unit construction above,
with the exact rational Jacobian already included in the integrand. -/
def reciprocalQuarticMinusOneCompactDyadicConstruction :
    Integral.CandidateConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) where
  compute := reciprocalQuarticMinusOneUnitDyadicCompute
  certificate := reciprocalQuarticMinusOneUnitDyadicRaw_valid

def reciprocalQuarticMinusOneCompactDyadicIntegral : RealCompute :=
  Integral.candidateValueFor
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    reciprocalQuarticMinusOneCompactDyadicConstruction

theorem reciprocalQuarticMinusOneCompactDyadicIntegral_valid :
    reciprocalQuarticMinusOneCompactDyadicIntegral.Valid :=
  Integral.candidateValueFor_valid
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    reciprocalQuarticMinusOneCompactDyadicConstruction

theorem reciprocalQuarticMinusOneCompactDyadicIntegral_compute_eq
    (stage : Nat) :
    reciprocalQuarticMinusOneCompactDyadicIntegral.compute stage =
      reciprocalQuarticMinusOneUnitDyadicCompute stage :=
  rfl

/-- Exact dyadic width of the compact reciprocal-quartic integral evaluator.
This is the rate of the public raw integral, rather than merely a comparison
envelope used in its Cauchy bridge. -/
theorem reciprocalQuarticMinusOneCompactDyadicIntegral_width (stage : Nat) :
    (reciprocalQuarticMinusOneCompactDyadicIntegral.compute stage).width =
      64 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  rw [reciprocalQuarticMinusOneCompactDyadicIntegral_compute_eq]
  exact reciprocalQuarticMinusOneUnitDyadicCompute_width stage

/-- Any nonnegative rational multiple of the standard dyadic zero budget
still shrinks, even after a schedule that is always at least the requested
stage.  This is a finite rational reindexing fact, used below to account for
the explicit widths in the projective/Cauchy bridge. -/
private theorem scaled_dyadic_budget_widthsShrink
    (C : Rat) (hC : 0 <= C) (stage : Nat -> Nat)
    (hstage : forall n, n <= stage n) :
    RealCompute.WidthsShrinkToZero (fun n : Nat =>
      ({ lo := (0 : Rat), hi := C * (1 / (((2 ^ (stage n) : Nat) : Rat))) } : QInterval)) := by
  let budget : RealCompute := RealCompute.scaleRat C projectiveCompactDyadicZero
  have hbudget : budget.Valid := by
    dsimp [budget]
    exact RealCompute.scaleRat_valid_of_nonneg hC projectiveCompactDyadicZero_valid
  intro eps
  obtain ⟨N, hN⟩ := hbudget.2.2 eps
  refine ⟨N, ?_⟩
  intro n hn
  have hstageN : N <= stage n := Nat.le_trans hn (hstage n)
  have hsmall := hN (stage n) hstageN
  change C * (1 / (((2 ^ (stage n) : Nat) : Rat))) - 0 <= eps.val
  simpa [budget, RealCompute.scaleRat, RealCompute.scaleRatCompute,
    projectiveCompactDyadicZero, hC, QInterval.width] using hsmall

/-- The finite full-line Cauchy envelope has an explicit dyadic width budget.
The deliberately coarse constant keeps every source of error visible: the
unit Cauchy mesh, omitted near-zero segment, tail mesh, finite bridge, two
compact brackets, and endpoint cell. -/
private theorem projectiveCompactDyadicFullCauchyEnvelope_width_le
    (n : Nat) :
    (projectiveCompactDyadicFullCauchyEnvelope n).width <=
      224 * (1 / (((2 ^ n : Nat) : Rat))) := by
  let unit : QInterval := ArctanGeometry.integralSumInterval
    (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals
  let a : Rat := projectiveCompactDyadicCauchyTailStart n
  let tail : QInterval := ArctanGeometry.integralSumInterval
    (cauchyTailDyadicIntervals a (5 * n + 8))
  let bridge : QInterval := projectiveCompactDyadicScheduledCauchyBridgeEnvelope n
  let scheduled : QInterval := projectiveCompactSymmetricLipschitzSum
    (ArctanGeometry.arctanAreaLoopState
      (projectiveCompactDyadicEndpoint (n + 2)) ((n + 2) * 6)).intervals
  let literal : QInterval := projectiveCompactSymmetricLipschitzSum
    (reciprocalQuarticUnitDyadicCoreIntervals (n + 2))
  let endpoint : QInterval := projectiveCompactDyadicSymmetricTailError.compute (n + 2)
  have hdyadic_pos (k : Nat) : 0 < (1 / (((2 ^ k : Nat) : Rat))) := by
    exact one_div_nat_pos (Nat.pow_pos (by omega : 0 < 2))
  have hdyadic_antitone {i j : Nat} (hij : i <= j) :
      1 / (((2 ^ j : Nat) : Rat)) <= 1 / (((2 ^ i : Nat) : Rat)) := by
    exact FTC.one_div_nat_antitone
      (Nat.pow_pos (by omega : 0 < 2))
      (Nat.pow_pos (by omega : 0 < 2))
      (Nat.pow_le_pow_right (by omega : 0 < 2) hij)
  have hunit : unit.width <= 2 * (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) := by
    have hunitIntervals : ArctanGeometry.UnitIntervals
        (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals :=
      ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by decide +kernel) (by decide +kernel) (5 * n + 8)
    calc
      unit.width <= 2 * ArctanGeometry.intervalSquareSum
          (ArctanGeometry.arctanAreaLoopState 1 (5 * n + 8)).intervals := by
        dsimp [unit]
        exact ArctanGeometry.integralSumInterval_width_le_two_squareSum _ hunitIntervals
      _ = 2 * (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) := by
        rw [ArctanGeometry.arctanAreaLoopState_squareSum]
        simp only [Rat.one_mul]
  have htail : tail.width <= 2 * (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) := by
    dsimp [tail]
    exact cauchyTailDyadicIntervals_integral_width_le_dyadic
      (Rat.le_of_lt (projectiveCompactDyadicCauchyTailStart_pos n))
      (projectiveCompactDyadicCauchyTailStart_le_one n) (5 * n + 8)
  have ha : a <= 2 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
    dsimp [a]
    exact projectiveCompactDyadicCauchyTailStart_le_dyadic n
  have hbridge : bridge.width <= 12 * (1 / (((2 ^ n : Nat) : Rat))) := by
    dsimp [bridge]
    exact projectiveCompactDyadicScheduledCauchyBridgeEnvelope_width_le n
  have hscheduled : scheduled.width <=
      32 * (1 / (((2 ^ ((n + 2) * 6) : Nat) : Rat))) := by
    dsimp [scheduled]
    exact projectiveCompactDyadicScheduledCore_symmetric_width_le (n + 2)
  have hliteral : literal.width <=
      32 * (1 / (((2 ^ (n + 2) : Nat) : Rat))) := by
    dsimp [literal]
    exact reciprocalQuarticUnitDyadicCore_symmetric_width_le (n + 2)
  have hendpoint : endpoint.hi =
      ((64 : Rat) / 3) * (1 / (((2 ^ (n + 2) : Nat) : Rat))) := by
    dsimp [endpoint]
    rw [projectiveCompactDyadicSymmetricTailError_compute]
  have hunitSmall : 1 / (((2 ^ (5 * n + 8) : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    hdyadic_antitone (by omega)
  have hsuccSmall : 1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    hdyadic_antitone (by omega)
  have htwoSmall : 1 / (((2 ^ (n + 2) : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    hdyadic_antitone (by omega)
  have hscheduledSmall : 1 / (((2 ^ ((n + 2) * 6) : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) :=
    hdyadic_antitone (by omega)
  have hfourUnit : 4 * unit.width <= 8 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      4 * unit.width <= 4 * (2 * (1 / (((2 ^ (5 * n + 8) : Nat) : Rat))) ) :=
        Rat.mul_le_mul_of_nonneg_left hunit (by decide +kernel)
      _ <= 4 * (2 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left hunitSmall (by decide +kernel))
          (by decide +kernel)
      _ = 8 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have hfourA : 4 * a <= 8 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      4 * a <= 4 * (2 * (1 / (((2 ^ (n + 1) : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left ha (by decide +kernel)
      _ <= 4 * (2 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left hsuccSmall (by decide +kernel))
          (by decide +kernel)
      _ = 8 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have hfourTail : 4 * tail.width <= 8 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      4 * tail.width <= 4 * (2 * (1 / (((2 ^ (5 * n + 8) : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left htail (by decide +kernel)
      _ <= 4 * (2 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left hunitSmall (by decide +kernel))
          (by decide +kernel)
      _ = 8 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have hfourBridge : 4 * bridge.width <= 48 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      4 * bridge.width <= 4 * (12 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left hbridge (by decide +kernel)
      _ = 48 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have htwoScheduled : 2 * scheduled.width <= 64 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      2 * scheduled.width <=
          2 * (32 * (1 / (((2 ^ ((n + 2) * 6) : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left hscheduled (by decide +kernel)
      _ <= 2 * (32 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left hscheduledSmall (by decide +kernel))
          (by decide +kernel)
      _ = 64 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have htwoLiteral : 2 * literal.width <= 64 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      2 * literal.width <= 2 * (32 * (1 / (((2 ^ (n + 2) : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left hliteral (by decide +kernel)
      _ <= 2 * (32 * (1 / (((2 ^ n : Nat) : Rat)))) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left htwoSmall (by decide +kernel))
          (by decide +kernel)
      _ = 64 * (1 / (((2 ^ n : Nat) : Rat))) := by grind [Rat.mul_assoc]
  have hendpointSmall : endpoint.hi <= 24 * (1 / (((2 ^ n : Nat) : Rat))) := by
    calc
      endpoint.hi = ((64 : Rat) / 3) * (1 / (((2 ^ (n + 2) : Nat) : Rat))) := hendpoint
      _ <= 24 * (1 / (((2 ^ (n + 2) : Nat) : Rat))) := by
        exact Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
          (Rat.le_of_lt (hdyadic_pos (n + 2)))
      _ <= 24 * (1 / (((2 ^ n : Nat) : Rat))) :=
        Rat.mul_le_mul_of_nonneg_left htwoSmall (by decide +kernel)
  change
    (4 * unit.hi + 2 * (a + tail.width) + 2 * bridge.width +
        scheduled.width + literal.width + endpoint.hi) -
      (4 * unit.lo -
        (2 * (a + tail.width) + 2 * bridge.width +
          scheduled.width + literal.width)) <=
      224 * (1 / (((2 ^ n : Nat) : Rat)))
  calc
    (4 * unit.hi + 2 * (a + tail.width) + 2 * bridge.width +
        scheduled.width + literal.width + endpoint.hi) -
      (4 * unit.lo -
        (2 * (a + tail.width) + 2 * bridge.width +
          scheduled.width + literal.width)) =
        4 * unit.width + 4 * a + 4 * tail.width + 4 * bridge.width +
          2 * scheduled.width + 2 * literal.width + endpoint.hi := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_assoc, Rat.add_assoc,
          Rat.add_comm]
    _ <= 8 * (1 / (((2 ^ n : Nat) : Rat))) +
          8 * (1 / (((2 ^ n : Nat) : Rat))) +
          8 * (1 / (((2 ^ n : Nat) : Rat))) +
          48 * (1 / (((2 ^ n : Nat) : Rat))) +
          64 * (1 / (((2 ^ n : Nat) : Rat))) +
          64 * (1 / (((2 ^ n : Nat) : Rat))) +
          24 * (1 / (((2 ^ n : Nat) : Rat))) := by
        exact rat_add_le_add
          (rat_add_le_add
            (rat_add_le_add
              (rat_add_le_add
                (rat_add_le_add
                  (rat_add_le_add hfourUnit hfourA) hfourTail)
                hfourBridge)
              htwoScheduled)
            htwoLiteral)
          hendpointSmall
    _ = 224 * (1 / (((2 ^ n : Nat) : Rat))) := by
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

private theorem projectiveCompactDyadicFullCauchyEnvelope_widthsShrink :
    RealCompute.WidthsShrinkToZero projectiveCompactDyadicFullCauchyEnvelope := by
  have hbudget := scaled_dyadic_budget_widthsShrink (224 : Rat)
    (by decide +kernel : (0 : Rat) <= 224) (fun n => n) (fun n => Nat.le_refl n)
  intro eps
  obtain ⟨N, hN⟩ := hbudget eps
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall : 224 * (1 / (((2 ^ n : Nat) : Rat))) <= eps.val := by
    have hsmall' := hN n hn
    change 224 * (1 / (((2 ^ n : Nat) : Rat))) - 0 <= eps.val at hsmall'
    grind [Rat.sub_eq_add_neg]
  exact Rat.le_trans (projectiveCompactDyadicFullCauchyEnvelope_width_le n)
    hsmall

/-- A shrinking rational enclosure proves raw-real order whenever its left
endpoint lies below one scheduled computation and its right endpoint lies
above the other.  The proof is the epsilon/2 gap argument, entirely over
rationals; the schedules only need to be cofinal. -/
private theorem realCompute_le_of_shrinking_enclosures
    {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (enclosure : Nat -> QInterval) (leftStage rightStage : Nat -> Nat)
    (hleftStage : forall k, k <= leftStage k)
    (hrightStage : forall k, k <= rightStage k)
    (hleft : forall k, (x.compute (leftStage k)).lo <= (enclosure k).hi)
    (hright : forall k, (enclosure k).lo <= (y.compute (rightStage k)).hi)
    (hshrink : RealCompute.WidthsShrinkToZero enclosure) :
    x.Le y := by
  intro n m
  by_cases hgood : (x.compute n).lo <= (y.compute m).hi
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo - (y.compute m).hi := by
      rw [← Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have htwo : (0 : Rat) < 2 := by decide +kernel
    have hhalfPos : 0 < ((x.compute n).lo - (y.compute m).hi) / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 htwo)
    obtain ⟨N, hN⟩ := hshrink
      { val := ((x.compute n).lo - (y.compute m).hi) / 2,
        property := hhalfPos }
    let k : Nat := Nat.max N (Nat.max n m)
    have hNk : N <= k := by
      dsimp [k]
      exact Nat.le_max_left _ _
    have hnk0 : n <= k := by
      dsimp [k]
      exact Nat.le_trans (Nat.le_max_left n m)
        (Nat.le_max_right N (Nat.max n m))
    have hmk0 : m <= k := by
      dsimp [k]
      exact Nat.le_trans (Nat.le_max_right n m)
        (Nat.le_max_right N (Nat.max n m))
    have hxnest := hx.2.1 n (leftStage k)
      (Nat.le_trans hnk0 (hleftStage k))
    have hynest := hy.2.1 m (rightStage k)
      (Nat.le_trans hmk0 (hrightStage k))
    have hsmall := hN k hNk
    have hgapLe :
        (x.compute n).lo - (y.compute m).hi <= (enclosure k).width := by
      have hxl := hleft k
      have hyr := hright k
      grind [QInterval.width, Rat.sub_eq_add_neg]
    have hhalfLt : ((x.compute n).lo - (y.compute m).hi) / 2 <
        (x.compute n).lo - (y.compute m).hi := by
      rw [Rat.div_lt_iff htwo]
      grind
    have hgapLeHalf :
        (x.compute n).lo - (y.compute m).hi <=
          ((x.compute n).lo - (y.compute m).hi) / 2 :=
      Rat.le_trans hgapLe hsmall
    have hgapLtHalf : (x.compute n).lo - (y.compute m).hi <
        ((x.compute n).lo - (y.compute m).hi) / 2 :=
      Rat.lt_of_le_of_ne hgapLeHalf (Rat.ne_of_gt hhalfLt)
    exact (Rat.ne_of_gt hhalfLt)
      (Rat.le_antisymm hgapLeHalf (Rat.le_of_lt hhalfLt))

/-- The literal compact reciprocal-quartic computation and the completed
Cauchy full-line computation determine the same raw real.  This uses their
finite projective bridge plus the explicitly shrinking common envelope; it
does not invoke completeness of an ambient real-number system. -/
theorem reciprocalQuarticMinusOneCompactDyadicIntegral_equiv_cauchyFullLine :
    reciprocalQuarticMinusOneCompactDyadicIntegral.Equiv cauchyFullLineIntegral := by
  apply RealCompute.equiv_of_le_of_ge
  · apply realCompute_le_of_shrinking_enclosures
      reciprocalQuarticMinusOneCompactDyadicIntegral_valid
      cauchyFullLineIntegral_valid projectiveCompactDyadicFullCauchyEnvelope
      (fun k => k + 3) (fun k => 5 * k + 8)
    · intro k
      omega
    · intro k
      omega
    · intro k
      have hover :=
        reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_fullCauchy k
      change (reciprocalQuarticMinusOneUnitDyadicCompute (k + 3)).lo <=
        (projectiveCompactDyadicFullCauchyEnvelope k).hi
      exact hover.1
    · intro k
      have hcontains := projectiveCompactDyadicFullCauchyEnvelope_contains_cauchyFullLine k
      exact Rat.le_trans hcontains.1
        (RealCompute.interval_order_of_valid cauchyFullLineIntegral
          cauchyFullLineIntegral_valid (5 * k + 8))
    · exact projectiveCompactDyadicFullCauchyEnvelope_widthsShrink
  · apply realCompute_le_of_shrinking_enclosures
      cauchyFullLineIntegral_valid
      reciprocalQuarticMinusOneCompactDyadicIntegral_valid
      projectiveCompactDyadicFullCauchyEnvelope
      (fun k => 5 * k + 8) (fun k => k + 3)
    · intro k
      omega
    · intro k
      omega
    · intro k
      have hcontains := projectiveCompactDyadicFullCauchyEnvelope_contains_cauchyFullLine k
      exact Rat.le_trans
        (RealCompute.interval_order_of_valid cauchyFullLineIntegral
          cauchyFullLineIntegral_valid (5 * k + 8)) hcontains.2
    · intro k
      have hover :=
        reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_fullCauchy k
      change (projectiveCompactDyadicFullCauchyEnvelope k).lo <=
        (reciprocalQuarticMinusOneUnitDyadicCompute (k + 3)).hi
      exact hover.2
    · exact projectiveCompactDyadicFullCauchyEnvelope_widthsShrink

theorem reciprocalQuarticMinusOneCompact_existsConstruction :
    Integral.ExistsCandidateConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1) :=
  ⟨reciprocalQuarticMinusOneCompactDyadicConstruction⟩

/-- The finite compact interval integral that represents the clean
projective-line quartic route.  Its integrand is the explicit density obtained
after the rational compactification of the line; a future route must therefore
provide an integral construction for this particular function, rather than an
unconstrained raw real. -/
def reciprocalQuarticMinusOneCompactIntegral
    (construction : Integral.CandidateConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) : RealCompute :=
  Integral.candidateValueFor (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
    construction

theorem reciprocalQuarticMinusOneCompactIntegral_valid
    (construction : Integral.CandidateConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) :
    (reciprocalQuarticMinusOneCompactIntegral construction).Valid :=
  Integral.candidateValueFor_valid _ construction

/-- The theorem-facing obligation for the compactified clean reciprocal
quartic integral.  The required equality is now tied to a construction for
the actual compact density on `[-1,1]`. -/
def ReciprocalQuarticMinusOneProjectiveAgreement
    (construction : Integral.CandidateConstructionFor
      (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)) : Prop :=
  (reciprocalQuarticMinusOneCompactIntegral construction).Equiv
    reciprocalQuarticMinusOneExpectedPi

/-- Data for the clean reciprocal quartic pi route.  The finite algebraic
pullback and compact interval integrand are formalized above.  What remains is
an analytic certificate that a concrete integral construction for that density
computes the expected pi value. -/
structure ReciprocalQuarticMinusOneProjectiveRoute where
  compactConstruction : Integral.CandidateConstructionFor
    (reciprocalQuarticMinusOneCompactOnInterval (-1) 1)
  computes_expected :
    ReciprocalQuarticMinusOneProjectiveAgreement compactConstruction

namespace ReciprocalQuarticMinusOneProjectiveRoute

/-- The projective-line integral is definitionally the finite integral of the
compactified rational density. -/
def projectiveIntegral (R : ReciprocalQuarticMinusOneProjectiveRoute) : RealCompute :=
  reciprocalQuarticMinusOneCompactIntegral R.compactConstruction

theorem projectiveIntegral_valid (R : ReciprocalQuarticMinusOneProjectiveRoute) :
    R.projectiveIntegral.Valid :=
  reciprocalQuarticMinusOneCompactIntegral_valid R.compactConstruction

end ReciprocalQuarticMinusOneProjectiveRoute

/-- Folding the positive half-line by the reciprocal map produces the symmetric
density \((1+x^2)/(x^4+a x^2+1)\) on the unit interval. -/
theorem reciprocalQuarticUnitFoldDensity_eq_symmetric
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hQrec : reciprocalQuarticDenominator a (1 / x) ≠ 0) :
    reciprocalQuarticUnitFoldDensity a x =
      reciprocalQuarticSymmetricDensity a x := by
  apply rat_eq_of_mul_eq_mul_ne (c := reciprocalQuarticDenominator a x) hQ
  have hrec := reciprocalQuarticDenominator_reciprocal_cleared a x hx
  have hx2 : x * x ≠ 0 := Rat.ne_of_gt (rat_square_pos_of_ne_zero hx)
  calc
    reciprocalQuarticUnitFoldDensity a x *
        reciprocalQuarticDenominator a x
        = 1 + x * x := by
          unfold reciprocalQuarticUnitFoldDensity reciprocalQuarticKernel
          rw [Rat.add_mul, Rat.div_def, Rat.div_def, Rat.div_def]
          rw [← hrec]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = reciprocalQuarticSymmetricDensity a x *
        reciprocalQuarticDenominator a x := by
          unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The exact pullback-density identity for the reciprocal quartic test
integral.  The positivity hypotheses needed in analysis will imply the two
nonzero denominator assumptions here. -/
theorem reciprocalQuarticSymmetricDensity_eq_pullback_shiftedCauchy
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hE : shiftedCauchyDenominator a (reciprocalDifference x) ≠ 0) :
    reciprocalQuarticSymmetricDensity a x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel a (reciprocalDifference x) := by
  apply rat_eq_of_mul_eq_mul_ne (c := reciprocalQuarticDenominator a x) hQ
  calc
    reciprocalQuarticSymmetricDensity a x *
        reciprocalQuarticDenominator a x
        = 1 + x * x := by
          unfold reciprocalQuarticSymmetricDensity reciprocalQuarticKernel
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (reciprocalDifferenceJacobian x *
          shiftedCauchyKernel a (reciprocalDifference x)) *
          reciprocalQuarticDenominator a x := by
          have hden :=
            reciprocalDifference_quartic_denominator a x hx
          have hjac :=
            reciprocalDifferenceJacobian_square_cleared x hx
          unfold shiftedCauchyKernel
          rw [Rat.div_def]
          rw [← hden]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The whole finite algebra chain used by the reciprocal quartic test:
fold the positive half-line by \(x\leftrightarrow1/x\), then substitute
`u = x - 1/x`. -/
theorem reciprocalQuarticUnitFoldDensity_eq_pullback_shiftedCauchy
    (a x : Rat) (hx : x ≠ 0)
    (hQ : reciprocalQuarticDenominator a x ≠ 0)
    (hQrec : reciprocalQuarticDenominator a (1 / x) ≠ 0)
    (hE : shiftedCauchyDenominator a (reciprocalDifference x) ≠ 0) :
    reciprocalQuarticUnitFoldDensity a x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel a (reciprocalDifference x) := by
  rw [reciprocalQuarticUnitFoldDensity_eq_symmetric a x hx hQ hQrec]
  exact reciprocalQuarticSymmetricDensity_eq_pullback_shiftedCauchy
    a x hx hQ hE

/-- The denominator-free specialization of the full finite algebra chain for
the pi-producing quartic \(x^4-x^2+1\). -/
theorem reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_shiftedCauchy
    (x : Rat) (hx : x ≠ 0) :
    reciprocalQuarticUnitFoldDensity (-1) x =
      reciprocalDifferenceJacobian x *
        shiftedCauchyKernel (-1) (reciprocalDifference x) := by
  exact reciprocalQuarticUnitFoldDensity_eq_pullback_shiftedCauchy
    (-1) x hx
    (Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos x))
    (Rat.ne_of_gt (reciprocalQuarticDenominator_minus_one_pos (1 / x)))
    (Rat.ne_of_gt
      (shiftedCauchyDenominator_minus_one_pos (reciprocalDifference x)))

/-- The denominator-free pi-case pullback, stated directly with the arctangent
kernel used by the rectangle construction. -/
theorem reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_integralKernel
    (x : Rat) (hx : x ≠ 0) :
    reciprocalQuarticUnitFoldDensity (-1) x =
      reciprocalDifferenceJacobian x *
        ArctanGeometry.integralKernel (reciprocalDifference x) := by
  rw [reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_shiftedCauchy x hx]
  rw [shiftedCauchyKernel_minus_one_eq_integralKernel]

/-- The geometric cosine algorithm, restricted to a rational interval where it
is defined. -/
def geometricCosOnInterval
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x) :
    FunctionOnInterval where
  raw := {
    definedAt := inDomainInterval a b
    compute := fun x hx => C.cosFunctionRaw.compute x (hdefined x hx)
  }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact C.cosFunctionRaw_valid x (hdefined x hx)

/-- The geometric sine algorithm, restricted to a rational interval where it
is defined. -/
def geometricSinOnInterval
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x) :
    FunctionOnInterval where
  raw := {
    definedAt := inDomainInterval a b
    compute := fun x hx => C.sinFunctionRaw.compute x (hdefined x hx)
  }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact C.sinFunctionRaw_valid x (hdefined x hx)

theorem geometricCosOnInterval_valid
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x) :
    forall x hx,
      RealCompute.ValidCompute
        ((geometricCosOnInterval C a b hdefined).compute x hx) := by
  intro x hx
  exact (geometricCosOnInterval C a b hdefined).valid_on
    x ((geometricCosOnInterval C a b hdefined).defined_on x hx)

theorem geometricSinOnInterval_valid
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat)
    (hdefined :
      forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x) :
    forall x hx,
      RealCompute.ValidCompute
        ((geometricSinOnInterval C a b hdefined).compute x hx) := by
  intro x hx
  exact (geometricSinOnInterval C a b hdefined).valid_on
    x ((geometricSinOnInterval C a b hdefined).defined_on x hx)

/-- The target package saying that geometric sine and cosine satisfy their
definite-integral identities on a chosen rational interval.  The derivative
proofs and the integral constructions are supplied as data. -/
structure GeometricTrigIntegralIdentities
    (C : RationalCircle.GeometricTrig.FunctionRawConstruction)
    (a b : Rat) where
  cos_defined :
    forall x, inDomainInterval a b x -> C.cosFunctionRaw.definedAt x
  sin_defined :
    forall x, inDomainInterval a b x -> C.sinFunctionRaw.definedAt x
  negCos : FunctionOnInterval
  integral_cos_eq_sin :
    Integral.CandidateEndpointAgreementOnInterval
      (geometricCosOnInterval C a b cos_defined)
      (geometricSinOnInterval C a b sin_defined)
  integral_sin_eq_negCos :
    Integral.CandidateEndpointAgreementOnInterval
      (geometricSinOnInterval C a b sin_defined)
      negCos

namespace GeometricTrigIntegralIdentities

def cosOnInterval
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    FunctionOnInterval :=
  geometricCosOnInterval C a b H.cos_defined

def sinOnInterval
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    FunctionOnInterval :=
  geometricSinOnInterval C a b H.sin_defined

theorem cos_integral_valid
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    (Integral.sampleValue
      (H.cosOnInterval).toRealFunRaw
      (H.cosOnInterval).lower
      (H.cosOnInterval).upper
      H.integral_cos_eq_sin.construction).Valid :=
  H.integral_cos_eq_sin.integral_valid

theorem sin_integral_valid
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {a b : Rat}
    (H : GeometricTrigIntegralIdentities C a b) :
    (Integral.sampleValue
      (H.sinOnInterval).toRealFunRaw
      (H.sinOnInterval).lower
      (H.sinOnInterval).upper
      H.integral_sin_eq_negCos.construction).Valid :=
  H.integral_sin_eq_negCos.integral_valid

end GeometricTrigIntegralIdentities

/-- Inverse elementary functions represented by the kernels that a calculus
student would recognize.  These identities are deliberately interval-local:
the branch and endpoint choices are part of the data. -/
structure InverseElementaryIntegralIdentities where
  arctan : FunctionOnInterval
  arctanKernel : FunctionOnInterval
  integral_invOnePlusSquare_eq_arctan :
    Integral.CandidateEndpointAgreementOnInterval arctanKernel arctan
  arcsin : FunctionOnInterval
  arcsinKernel : FunctionOnInterval
  integral_invSqrtOneMinusSquare_eq_arcsin :
    Integral.CandidateEndpointAgreementOnInterval arcsinKernel arcsin
  log : FunctionOnInterval
  logKernel : FunctionOnInterval
  integral_invX_eq_log :
    Integral.CandidateEndpointAgreementOnInterval logKernel log

/-- Abelian-integral forms related to trigonometric and inverse-trigonometric
functions.  The first two are inverse representations; elliptic integrals are
included as the next natural Abelian family beyond circular trigonometry. -/
structure AbelianTrigIntegralRepresentations where
  arcsinInverse : AbelianIntegral.InverseRepresentation
  arctanInverse : AbelianIntegral.InverseRepresentation
  sine_agrees_with_arcsinInverse :
    ComputableAnalysis.sin.agreesWithAbelianInverseRep arcsinInverse
  cosine_agrees_with_arctanInverse :
    ComputableAnalysis.cos.agreesWithAbelianInverseRep arctanInverse
  ellipticDifferential : AbelianIntegral.DifferentialRaw
  ellipticIntegral : AbelianIntegral.Candidate

/-!
## Generic finite Lipschitz--Darboux integrals on the unit interval

The earlier compact examples use the midpoint mesh from `ArctanGeometry`.
The following constructor exposes the part of that argument which is not
specific to a circle or a quartic density.  Given only a rational Lipschitz
bound on `[0,1]`, it produces nested rational lower and upper rectangle sums.
Thus it is an actual raw integral algorithm, rather than a postulated
`CandidateConstructionFor` certificate.
-/

namespace LipschitzDyadic

/-- The lower Lipschitz rectangle on a unit-interval cell. -/
private def lowerCell (f : Rat -> Rat) (L : Nat) (p r : Rat) : Rat :=
  Integral.lipschitzLowerCell f (L : Rat) p r

/-- The matching upper Lipschitz rectangle on a unit-interval cell. -/
private def upperCell (f : Rat -> Rat) (L : Nat) (p r : Rat) : Rat :=
  Integral.lipschitzUpperCell f (L : Rat) p r

private def lowerSum (f : Rat -> Rat) (L : Nat) :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => lowerCell f L p r + lowerSum f L rest

private def upperSum (f : Rat -> Rat) (L : Nat) :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => upperCell f L p r + upperSum f L rest

/-- Scaling a Lipschitz lower rectangle by a natural rational factor is an
exact finite identity.  Keeping this at the cell level makes later integral
identifications use the same literal Darboux boxes, rather than a separate
linearity axiom. -/
private theorem lowerCell_natScale (f : Rat -> Rat) (L scale : Nat)
    (p r : Rat) :
    lowerCell (fun x => (scale : Rat) * f x) (scale * L) p r =
      (scale : Rat) * lowerCell f L p r := by
  unfold lowerCell Integral.lipschitzLowerCell
  rw [Rat.natCast_mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

private theorem upperCell_natScale (f : Rat -> Rat) (L scale : Nat)
    (p r : Rat) :
    upperCell (fun x => (scale : Rat) * f x) (scale * L) p r =
      (scale : Rat) * upperCell f L p r := by
  unfold upperCell Integral.lipschitzUpperCell
  rw [Rat.natCast_mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

private theorem lowerSum_natScale (f : Rat -> Rat) (L scale : Nat) :
    forall intervals,
      lowerSum (fun x => (scale : Rat) * f x) (scale * L) intervals =
        (scale : Rat) * lowerSum f L intervals
  | [] => by
      simp only [lowerSum]
      grind
  | (p, r) :: rest => by
      rw [lowerSum, lowerSum, lowerCell_natScale, lowerSum_natScale]
      grind [Rat.mul_add]

private theorem upperSum_natScale (f : Rat -> Rat) (L scale : Nat) :
    forall intervals,
      upperSum (fun x => (scale : Rat) * f x) (scale * L) intervals =
        (scale : Rat) * upperSum f L intervals
  | [] => by
      simp only [upperSum]
      grind
  | (p, r) :: rest => by
      rw [upperSum, upperSum, upperCell_natScale, upperSum_natScale]
      grind [Rat.mul_add]

/-- The literal finite right-endpoint rectangle sum on a supplied rational
partition.  It is kept separate from the Darboux lower/upper sums so a later
integral theorem can compare a familiar Riemann computation with its certified
enclosure without appealing to a completed real number. -/
def rightEndpointSum (f : Rat -> Rat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => (r - p) * f r + rightEndpointSum f rest

/-- The matching finite left-endpoint rectangle sum on a supplied rational
partition.  Exposing both endpoint conventions lets concrete
change-of-variables calculations retain their literal finite mesh formula. -/
def leftEndpointSum (f : Rat -> Rat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => (r - p) * f p + leftEndpointSum f rest

private theorem foldl_add_initial {α : Type} (g : α -> Rat)
    (xs : List α) (initial : Rat) :
    xs.foldl (fun total x => total + g x) initial =
      initial + xs.foldl (fun total x => total + g x) 0 := by
  induction xs generalizing initial with
  | nil =>
      change initial = initial + 0
      grind
  | cons x xs ih =>
      change xs.foldl (fun total x => total + g x) (initial + g x) =
        initial + xs.foldl (fun total x => total + g x) (0 + g x)
      rw [ih (initial + g x)]
      rw [show (0 : Rat) + g x = g x by grind, ih (g x)]
      grind [Rat.add_assoc]

/-- The recursive presentation of a finite right sum agrees with the usual
left fold that adds its rectangles in mesh order. -/
theorem rightEndpointSum_eq_foldl (f : Rat -> Rat)
    (intervals : List (Rat × Rat)) :
    rightEndpointSum f intervals =
      intervals.foldl
        (fun total cell => total + (cell.2 - cell.1) * f cell.2) 0 := by
  induction intervals with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      change (r - p) * f r + rightEndpointSum f rest =
        rest.foldl
          (fun total cell => total + (cell.2 - cell.1) * f cell.2)
          (0 + (r - p) * f r)
      rw [show (0 : Rat) + (r - p) * f r = (r - p) * f r by grind]
      rw [ih]
      exact (foldl_add_initial
        (fun cell : Rat × Rat => (cell.2 - cell.1) * f cell.2)
        rest ((r - p) * f r)).symm

/-- The recursive presentation of a finite left sum agrees with the usual
left fold that adds its rectangles in mesh order. -/
theorem leftEndpointSum_eq_foldl (f : Rat -> Rat)
    (intervals : List (Rat × Rat)) :
    leftEndpointSum f intervals =
      intervals.foldl
        (fun total cell => total + (cell.2 - cell.1) * f cell.1) 0 := by
  induction intervals with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      change (r - p) * f p + leftEndpointSum f rest =
        rest.foldl
          (fun total cell => total + (cell.2 - cell.1) * f cell.1)
          (0 + (r - p) * f p)
      rw [show (0 : Rat) + (r - p) * f p = (r - p) * f p by grind]
      rw [ih]
      exact (foldl_add_initial
        (fun cell : Rat × Rat => (cell.2 - cell.1) * f cell.1)
        rest ((r - p) * f p)).symm

/-- The standard finite uniform right Riemann sum on `[0,1]`.  The `n = 0`
case is deliberately the empty finite computation; applications to an
integral use a positive mesh count. -/
def uniformRightEndpointSum (f : Rat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun total (k : Nat) =>
      total + (1 / (n : Rat)) *
        f ((Nat.succ k : Rat) / (n : Rat))) 0

/-- The matching literal uniform left Riemann sum on the unit interval.  At a
positive mesh count it differs from the right sum only in endpoint convention. -/
def uniformLeftEndpointSum (f : Rat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun total (k : Nat) =>
      total + (1 / (n : Rat)) * f ((k : Rat) / (n : Rat))) 0

/-- The literal inner left-rectangle sum through a specified number of cells
of a fixed uniform unit mesh.  Keeping the mesh denominator fixed while the
prefix grows is the finite object needed for a triangle/Fubini comparison. -/
def uniformLeftPrefixSum (f : Rat -> Rat) (mesh : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      uniformLeftPrefixSum f mesh terms +
        (1 / (mesh : Rat)) * f ((terms : Rat) / (mesh : Rat))

/-- The finite triangular rectangle sum: at outer mesh point `i+1`, use the
inner left sum through `i+1` cells and multiply it by the outer mesh width.
This is the exact finite precursor of
`∫₀¹ (∫₀ˣ f(t) dt) dx`. -/
def uniformTriangleRightSum (f : Rat -> Rat) (mesh terms : Nat) : Rat :=
  rightStieltjesSum
    (fun k => (k : Rat) / (mesh : Rat))
    (uniformLeftPrefixSum f mesh) terms

private theorem uniformLeftPrefixSum_eq_foldl (f : Rat -> Rat)
    (mesh terms : Nat) :
    uniformLeftPrefixSum f mesh terms =
      (List.range terms).foldl
        (fun total (k : Nat) =>
          total + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat))) 0 := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [uniformLeftPrefixSum, ih, List.range_succ, List.foldl_append]
      rfl

/-- At the full mesh length, the prefix presentation is exactly the public
uniform left Riemann sum. -/
theorem uniformLeftPrefixSum_at_mesh (f : Rat -> Rat) (mesh : Nat) :
    uniformLeftPrefixSum f mesh mesh = uniformLeftEndpointSum f mesh := by
  rw [uniformLeftPrefixSum_eq_foldl]
  rfl

/-- Pointwise splitting `f = x*f + (1-x)*f` survives every finite fixed-mesh
prefix.  This is finite rational algebra, not integral linearity. -/
private theorem uniformLeftPrefixSum_sub_coordinate (f : Rat -> Rat)
    (mesh : Nat) : forall terms,
      uniformLeftPrefixSum f mesh terms -
          uniformLeftPrefixSum (fun x => x * f x) mesh terms =
        uniformLeftPrefixSum (fun x => (1 - x) * f x) mesh terms
  | 0 => by
      simp only [uniformLeftPrefixSum]
      grind
  | terms + 1 => by
      simp only [uniformLeftPrefixSum]
      calc
        uniformLeftPrefixSum f mesh terms +
            (1 / (mesh : Rat)) * f ((terms : Rat) / (mesh : Rat)) -
            (uniformLeftPrefixSum (fun x => x * f x) mesh terms +
              (1 / (mesh : Rat)) *
                (((terms : Rat) / (mesh : Rat)) *
                  f ((terms : Rat) / (mesh : Rat)))) =
            (uniformLeftPrefixSum f mesh terms -
              uniformLeftPrefixSum (fun x => x * f x) mesh terms) +
              ((1 / (mesh : Rat)) * f ((terms : Rat) / (mesh : Rat)) -
                (1 / (mesh : Rat)) *
                  (((terms : Rat) / (mesh : Rat)) *
                    f ((terms : Rat) / (mesh : Rat)))) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ = uniformLeftPrefixSum (fun x => (1 - x) * f x) mesh terms +
              ((1 / (mesh : Rat)) * f ((terms : Rat) / (mesh : Rat)) -
                (1 / (mesh : Rat)) *
                  (((terms : Rat) / (mesh : Rat)) *
                    f ((terms : Rat) / (mesh : Rat)))) := by
              rw [uniformLeftPrefixSum_sub_coordinate f mesh terms]
        _ = uniformLeftPrefixSum (fun x => (1 - x) * f x) mesh terms +
              (1 / (mesh : Rat)) *
                ((1 - (terms : Rat) / (mesh : Rat)) *
                  f ((terms : Rat) / (mesh : Rat))) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The left Stieltjes strip of the fixed-mesh inner sums is exactly the
ordinary left Riemann prefix for `x*f(x)`. -/
private theorem leftStieltjes_uniformLeftPrefix_eq_coordinate (f : Rat -> Rat)
    (mesh : Nat) : forall terms,
      leftStieltjesSum
          (fun k => (k : Rat) / (mesh : Rat))
          (uniformLeftPrefixSum f mesh) terms =
        uniformLeftPrefixSum (fun x => x * f x) mesh terms
  | 0 => by
      simp only [leftStieltjesSum, uniformLeftPrefixSum]
  | terms + 1 => by
      change
        leftStieltjesSum
            (fun k => (k : Rat) / (mesh : Rat))
            (uniformLeftPrefixSum f mesh) terms +
          ((terms : Rat) / (mesh : Rat)) *
            ((uniformLeftPrefixSum f mesh terms +
                (1 / (mesh : Rat)) * f ((terms : Rat) / (mesh : Rat))) -
              uniformLeftPrefixSum f mesh terms) =
          uniformLeftPrefixSum (fun x => x * f x) mesh terms +
            (1 / (mesh : Rat)) *
              (((terms : Rat) / (mesh : Rat)) *
                f ((terms : Rat) / (mesh : Rat)))
      rw [leftStieltjes_uniformLeftPrefix_eq_coordinate f mesh terms]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite triangle/Fubini identity on a positive uniform unit mesh.
The outer right sum of the inner left sums equals the ordinary left sum of
the complementary kernel `(1-x)*f(x)`.  Its proof is the project’s literal
finite integration-by-parts rectangle identity, so no continuous Fubini or
integral-linearity theorem is being assumed. -/
theorem uniformTriangleRightSum_eq_complementUniformLeftEndpointSum
    (f : Rat -> Rat) (mesh : Nat) (hmesh : 0 < mesh) :
    uniformTriangleRightSum f mesh mesh =
      uniformLeftEndpointSum (fun x => (1 - x) * f x) mesh := by
  have hfinite := finiteIntegrationByParts
    (fun k => (k : Rat) / (mesh : Rat))
    (uniformLeftPrefixSum f mesh) mesh
  have hleft := leftStieltjes_uniformLeftPrefix_eq_coordinate f mesh mesh
  have hmeshRat : (mesh : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
  have hendpoint : ((mesh : Nat) : Rat) / (mesh : Rat) = 1 := by
    rw [Rat.div_def, Rat.mul_inv_cancel _ hmeshRat]
  have hzero : ((0 : Nat) : Rat) / (mesh : Rat) = 0 := by
    grind [Rat.div_def]
  have hprefzero : uniformLeftPrefixSum f mesh 0 = 0 := rfl
  have hsplit := uniformLeftPrefixSum_sub_coordinate f mesh mesh
  unfold uniformTriangleRightSum
  rw [hleft] at hfinite
  have htriangle :
      rightStieltjesSum
          (fun k => (k : Rat) / (mesh : Rat))
          (uniformLeftPrefixSum f mesh) mesh =
        uniformLeftPrefixSum f mesh mesh -
          uniformLeftPrefixSum (fun x => x * f x) mesh mesh := by
    rw [hendpoint, hzero, hprefzero] at hfinite
    grind [Rat.sub_eq_add_neg]
  rw [htriangle, hsplit, uniformLeftPrefixSum_at_mesh]

private theorem foldl_eq_of_pointwise {α : Type}
    (g h : Rat -> α -> Rat)
    (hgh : forall total x, g total x = h total x)
    (xs : List α) (initial : Rat) :
    xs.foldl g initial = xs.foldl h initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl]
      rw [hgh initial x]
      exact ih (h initial x)

/-- The finite dyadic Darboux box for a rational function with a certified
Lipschitz constant.  Stage `n` uses the `2^n` midpoint-refined cells of the
unit interval. -/
def compute (f : Rat -> Rat) (L stage : Nat) : QInterval :=
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  { lo := lowerSum f L cells, hi := upperSum f L cells }

/-- The whole finite Lipschitz--Darboux box scales exactly by a natural
rational factor.  This is a concrete box identity, valid stage by stage. -/
theorem compute_natScale (f : Rat -> Rat) (L scale stage : Nat) :
    compute (fun x => (scale : Rat) * f x) (scale * L) stage =
      { lo := (scale : Rat) * (compute f L stage).lo,
        hi := (scale : Rat) * (compute f L stage).hi } := by
  unfold compute
  dsimp
  rw [lowerSum_natScale, upperSum_natScale]

/-- Adding two Lipschitz lower rectangles is exactly the lower rectangle for
the pointwise sum, with the two rational constants added.  This finite cell
identity is the algebra needed to join independently certified integral
strips without postulating linearity of an integral. -/
private theorem lowerCell_add (f g : Rat -> Rat) (L M : Nat)
    (p r : Rat) :
    lowerCell (fun x => f x + g x) (L + M) p r =
      lowerCell f L p r + lowerCell g M p r := by
  unfold lowerCell Integral.lipschitzLowerCell
  rw [Rat.natCast_add]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The matching exact finite identity for upper Lipschitz rectangles. -/
private theorem upperCell_add (f g : Rat -> Rat) (L M : Nat)
    (p r : Rat) :
    upperCell (fun x => f x + g x) (L + M) p r =
      upperCell f L p r + upperCell g M p r := by
  unfold upperCell Integral.lipschitzUpperCell
  rw [Rat.natCast_add]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem lowerSum_add (f g : Rat -> Rat) (L M : Nat) :
    forall intervals,
      lowerSum (fun x => f x + g x) (L + M) intervals =
        lowerSum f L intervals + lowerSum g M intervals
  | [] => by
      simp only [lowerSum]
      grind
  | (p, r) :: rest => by
      rw [lowerSum, lowerSum, lowerSum, lowerCell_add, lowerSum_add]
      grind [Rat.add_assoc]

private theorem upperSum_add (f g : Rat -> Rat) (L M : Nat) :
    forall intervals,
      upperSum (fun x => f x + g x) (L + M) intervals =
        upperSum f L intervals + upperSum g M intervals
  | [] => by
      simp only [upperSum]
      grind
  | (p, r) :: rest => by
      rw [upperSum, upperSum, upperSum, upperCell_add, upperSum_add]
      grind [Rat.add_assoc]

/-- The literal finite Darboux box for a pointwise sum is exactly the
componentwise sum of the two boxes.  This is a stagewise rational identity;
the Lipschitz hypotheses needed to certify either side remain separate. -/
theorem compute_add (f g : Rat -> Rat) (L M stage : Nat) :
    compute (fun x => f x + g x) (L + M) stage =
      { lo := (compute f L stage).lo + (compute g M stage).lo,
        hi := (compute f L stage).hi + (compute g M stage).hi } := by
  unfold compute
  dsimp
  rw [lowerSum_add, upperSum_add]

/-- The two rational values used for a Lipschitz cell bound every value of the
kernel on that cell.  This is the local Darboux meaning of the rectangle
algorithm, before any limiting or completed-integral interpretation. -/
theorem cell_value_bounds {f : Rat -> Rat} {L : Nat} {p r x : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1)
    (hpx : p <= x) (hxr : x <= r) :
    f p - (L : Rat) * (r - p) <= f x /\
      f x <= f p + (L : Rat) * (r - p) := by
  have hL0 := hlip.1
  have hx0 : 0 <= x := Rat.le_trans hp0 hpx
  have hx1 : x <= 1 := Rat.le_trans hxr hr1
  have hxp0 : 0 <= x - p := by grind [Rat.sub_eq_add_neg]
  have hxpabs : qabs (x - p) = x - p :=
    qabs_eq_self_of_nonneg hxp0
  have hxpr : x - p <= r - p := by grind [Rat.sub_eq_add_neg]
  have hscaled : (L : Rat) * (x - p) <= (L : Rat) * (r - p) :=
    Rat.mul_le_mul_of_nonneg_left hxpr hL0
  have hlip_px := hlip.2 p x hp0 (Rat.le_trans hpr hr1) hx0 hx1
  have hforward : f p - f x <= (L : Rat) * (r - p) := by
    calc
      f p - f x <= qabs (f p - f x) := self_le_qabs _
      _ <= (L : Rat) * qabs (x - p) := hlip_px
      _ = (L : Rat) * (x - p) := by rw [hxpabs]
      _ <= (L : Rat) * (r - p) := hscaled
  have hreverse : f x - f p <= (L : Rat) * (r - p) := by
    calc
      f x - f p = -(f p - f x) := by
        grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(f p - f x)) := self_le_qabs _
      _ = qabs (f p - f x) := qabs_neg _
      _ <= (L : Rat) * (r - p) :=
        Rat.le_trans hlip_px (by simpa [hxpabs] using hscaled)
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- On one unit-interval cell, the Lipschitz lower rectangle lies below the
literal rectangle evaluated at the right endpoint. -/
private theorem lowerCell_le_rightEndpoint {f : Rat -> Rat} {L : Nat}
    {p r : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    lowerCell f L p r <= (r - p) * f r := by
  have hvalue := cell_value_bounds hlip hp0 hpr hr1 hpr Rat.le_refl
  have hwidth : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue.1 hwidth

/-- On one unit-interval cell, the literal right-endpoint rectangle lies
below the matching Lipschitz upper rectangle. -/
private theorem rightEndpoint_le_upperCell {f : Rat -> Rat} {L : Nat}
    {p r : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    (r - p) * f r <= upperCell f L p r := by
  have hvalue := cell_value_bounds hlip hp0 hpr hr1 hpr Rat.le_refl
  have hwidth : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue.2 hwidth

/-- On one unit-interval cell, the Lipschitz lower rectangle lies below the
literal rectangle evaluated at the left endpoint. -/
private theorem lowerCell_le_leftEndpoint {f : Rat -> Rat} {L : Nat}
    {p r : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    lowerCell f L p r <= (r - p) * f p := by
  have hvalue := cell_value_bounds hlip hp0 hpr hr1 Rat.le_refl hpr
  have hwidth : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue.1 hwidth

/-- On one unit-interval cell, the literal rectangle evaluated at the left
endpoint lies below the matching Lipschitz upper rectangle. -/
private theorem leftEndpoint_le_upperCell {f : Rat -> Rat} {L : Nat}
    {p r : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    (r - p) * f p <= upperCell f L p r := by
  have hvalue := cell_value_bounds hlip hp0 hpr hr1 Rat.le_refl hpr
  have hwidth : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_le_mul_of_nonneg_left hvalue.2 hwidth

private theorem lowerSum_le_rightEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    lowerSum f L intervals <= rightEndpointSum f intervals := by
  induction intervals with
  | nil => simp [lowerSum, rightEndpointSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [lowerSum, rightEndpointSum]
      exact rat_add_le_add
        (lowerCell_le_rightEndpoint hlip hp0 hpr hr1) (ih hrest)

private theorem rightEndpointSum_le_upperSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    rightEndpointSum f intervals <= upperSum f L intervals := by
  induction intervals with
  | nil => simp [rightEndpointSum, upperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [rightEndpointSum, upperSum]
      exact rat_add_le_add
        (rightEndpoint_le_upperCell hlip hp0 hpr hr1) (ih hrest)

/-- Summing the left-endpoint bounds cell by cell places the literal left
sum inside a Lipschitz--Darboux bracket on any rational unit partition. -/
private theorem lowerSum_le_leftEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    lowerSum f L intervals <= leftEndpointSum f intervals := by
  induction intervals with
  | nil => simp [lowerSum, leftEndpointSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [lowerSum, leftEndpointSum]
      exact rat_add_le_add
        (lowerCell_le_leftEndpoint hlip hp0 hpr hr1) (ih hrest)

/-- The matching cellwise upper estimate for a literal left sum. -/
private theorem leftEndpointSum_le_upperSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    leftEndpointSum f intervals <= upperSum f L intervals := by
  induction intervals with
  | nil => simp [leftEndpointSum, upperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      simp only [leftEndpointSum, upperSum]
      exact rat_add_le_add
        (leftEndpoint_le_upperCell hlip hp0 hpr hr1) (ih hrest)

/-- Each finite literal right-endpoint sum on the dyadic unit mesh lies in the
matching Lipschitz--Darboux box.  This is the finite bridge from a conventional
Riemann computation to the project's certified integral representation. -/
theorem compute_contains_rightEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).ContainsInterval
      { lo := rightEndpointSum f
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
        hi := rightEndpointSum f
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals } := by
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hunit : ArctanGeometry.UnitIntervals cells :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  change lowerSum f L cells <= rightEndpointSum f cells /\
    rightEndpointSum f cells <= upperSum f L cells
  exact ⟨lowerSum_le_rightEndpointSum hlip cells hunit,
    rightEndpointSum_le_upperSum hlip cells hunit⟩

/-- Each finite literal left-endpoint sum on the dyadic unit mesh lies in the
matching Lipschitz--Darboux box.  Together with the right-endpoint theorem,
this makes the endpoint convention a visible finite choice rather than an
implicit limit argument. -/
theorem compute_contains_leftEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).ContainsInterval
      { lo := leftEndpointSum f
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
        hi := leftEndpointSum f
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals } := by
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hunit : ArctanGeometry.UnitIntervals cells :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  change lowerSum f L cells <= leftEndpointSum f cells /\
    leftEndpointSum f cells <= upperSum f L cells
  exact ⟨lowerSum_le_leftEndpointSum hlip cells hunit,
    leftEndpointSum_le_upperSum hlip cells hunit⟩

/-- The right-endpoint sum on the actual midpoint-refined area-loop cells is
the ordinary uniform right Riemann sum with `2^stage` cells. -/
theorem dyadicRightEndpointSum_eq_uniform (f : Rat -> Rat) (stage : Nat) :
    rightEndpointSum f
      (ArctanGeometry.arctanAreaLoopState 1 stage).intervals =
      uniformRightEndpointSum f (2 ^ stage) := by
  rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform,
    rightEndpointSum_eq_foldl]
  simp only [List.foldl_map]
  unfold uniformRightEndpointSum
  apply foldl_eq_of_pointwise
  intro total k
  have hwidth := RationalCircle.Stage.parameter_succ_sub
    (RationalCircle.dyadicStage stage) k
  change
    ((k + 1 : Nat) : Rat) / ((2 ^ stage : Nat) : Rat) -
        (k : Rat) / ((2 ^ stage : Nat) : Rat) =
      1 / ((2 ^ stage : Nat) : Rat) at hwidth
  rw [hwidth]

/-- The left-endpoint sum on the midpoint-refined area-loop cells is the
ordinary uniform left Riemann sum with the same dyadic cell count. -/
theorem dyadicLeftEndpointSum_eq_uniform (f : Rat -> Rat) (stage : Nat) :
    leftEndpointSum f
      (ArctanGeometry.arctanAreaLoopState 1 stage).intervals =
      uniformLeftEndpointSum f (2 ^ stage) := by
  rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform,
    leftEndpointSum_eq_foldl]
  simp only [List.foldl_map]
  unfold uniformLeftEndpointSum
  apply foldl_eq_of_pointwise
  intro total k
  have hwidth := RationalCircle.Stage.parameter_succ_sub
    (RationalCircle.dyadicStage stage) k
  change
    ((k + 1 : Nat) : Rat) / ((2 ^ stage : Nat) : Rat) -
        (k : Rat) / ((2 ^ stage : Nat) : Rat) =
      1 / ((2 ^ stage : Nat) : Rat) at hwidth
  rw [hwidth]

/-- A conventional uniform right Riemann sum is enclosed by the corresponding
finite Lipschitz--Darboux box.  This is the reusable finite comparison used
to identify series computations with certified rational integrals. -/
theorem compute_contains_uniformRightEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).ContainsInterval
      { lo := uniformRightEndpointSum f (2 ^ stage)
        hi := uniformRightEndpointSum f (2 ^ stage) } := by
  have h := compute_contains_rightEndpointSum hlip stage
  rw [dyadicRightEndpointSum_eq_uniform] at h
  exact h

/-- A conventional uniform left Riemann sum is likewise enclosed by the
matching finite Lipschitz--Darboux box. -/
theorem compute_contains_uniformLeftEndpointSum {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).ContainsInterval
      { lo := uniformLeftEndpointSum f (2 ^ stage)
        hi := uniformLeftEndpointSum f (2 ^ stage) } := by
  have h := compute_contains_leftEndpointSum hlip stage
  rw [dyadicLeftEndpointSum_eq_uniform] at h
  exact h

/-- Two certified Lipschitz constants for the same rational evaluator produce
overlapping Darboux boxes at every stage.  The common finite left rectangle
sum is the witness; no canonical Lipschitz constant is selected. -/
theorem compute_overlap_of_lipschitz_bounds
    {f : Rat -> Rat} {L M : Nat}
    (hL : Integral.LipschitzOnUnit f (L : Rat))
    (hM : Integral.LipschitzOnUnit f (M : Rat)) (stage : Nat) :
    QInterval.Overlaps (compute f L stage) (compute f M stage) := by
  have hleftL := compute_contains_uniformLeftEndpointSum hL stage
  have hleftM := compute_contains_uniformLeftEndpointSum hM stage
  unfold QInterval.ContainsInterval at hleftL hleftM
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans hleftL.1 hleftM.2,
    Rat.le_trans hleftM.1 hleftL.2⟩

/-- Consequently, the two Lipschitz--Darboux raw representations are
equivalent whenever both constants are valid certificates for the same
evaluator. -/
private theorem cells_refine {f : Rat -> Rat} {L : Nat} {p r : Rat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    let q := (p + r) / 2
    lowerCell f L p r <= lowerCell f L p q + lowerCell f L q r /\
    upperCell f L p q + upperCell f L q r <= upperCell f L p r := by
  simpa [lowerCell, upperCell] using
    (Integral.lipschitzCells_refine hlip hp0 hpr hr1)

private theorem lowerSum_refineAux {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    lowerSum f L intervals <=
      lowerSum f L
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux, lowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := cells_refine hlip hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux, lowerSum] at htail ⊢
      calc
        lowerCell f L p r + lowerSum f L rest <=
            (lowerCell f L p ((p + r) / 2) +
              lowerCell f L ((p + r) / 2) r) + lowerSum f L rest :=
          rat_add_le_add hcell.1 Rat.le_refl
        _ <= (lowerCell f L p ((p + r) / 2) +
              lowerCell f L ((p + r) / 2) r) +
              lowerSum f L
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals := by
          exact rat_add_le_add Rat.le_refl htail
        _ = lowerCell f L p ((p + r) / 2) +
              (lowerCell f L ((p + r) / 2) r +
                lowerSum f L
                  (ArctanGeometry.AreaLoopState.refineAux
                    (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                    (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                    rest).intervals) := by
          grind [Rat.add_assoc]

private theorem upperSum_refineAux {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    upperSum f L
        (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals <=
      upperSum f L intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux, upperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hcell := cells_refine hlip hp0 hpr hr1
      have htail := ih
        (lo + ArctanGeometry.arctanAreaIncrement p q r)
        (hi - ArctanGeometry.arctanAreaDecrement p q r) hrest
      dsimp [q] at hcell
      dsimp [q] at htail ⊢
      simp [ArctanGeometry.AreaLoopState.refineAux, upperSum] at htail ⊢
      calc
        upperCell f L p ((p + r) / 2) +
            (upperCell f L ((p + r) / 2) r +
              upperSum f L
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals) =
            upperCell f L p ((p + r) / 2) +
              upperCell f L ((p + r) / 2) r + upperSum f L
                (ArctanGeometry.AreaLoopState.refineAux
                  (lo + ArctanGeometry.arctanAreaIncrement p ((p + r) / 2) r)
                  (hi - ArctanGeometry.arctanAreaDecrement p ((p + r) / 2) r)
                  rest).intervals := by
              grind [Rat.add_assoc]
        _ <= upperCell f L p ((p + r) / 2) +
              upperCell f L ((p + r) / 2) r + upperSum f L rest :=
          rat_add_le_add Rat.le_refl htail
        _ <= upperCell f L p r + upperSum f L rest :=
          rat_add_le_add hcell.2 Rat.le_refl

theorem compute_step_refines {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).lo <= (compute f L (stage + 1)).lo /\
      (compute f L (stage + 1)).hi <= (compute f L stage).hi := by
  unfold compute
  rw [show stage + 1 = Nat.succ stage by omega,
    ArctanGeometry.arctanAreaLoopState_succ]
  dsimp
  let state := ArctanGeometry.arctanAreaLoopState 1 stage
  have hunit : ArctanGeometry.UnitIntervals state.intervals :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  constructor
  · exact lowerSum_refineAux hlip state.lo state.hi state.intervals hunit
  · exact upperSum_refineAux hlip state.lo state.hi state.intervals hunit

private theorem lowerCell_le_upperCell {f : Rat -> Rat} {L : Nat}
    {p r : Rat} (hpr : p <= r) :
    lowerCell f L p r <= upperCell f L p r := by
  have hwidth : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hinner :
      f p - (L : Rat) * (r - p) <= f p + (L : Rat) * (r - p) := by
    have hL0 : 0 <= (L : Rat) := by
      exact_mod_cast Nat.zero_le L
    have hterm : 0 <= (L : Rat) * (r - p) :=
      Rat.mul_nonneg hL0 hwidth
    grind [Rat.sub_eq_add_neg]
  unfold lowerCell upperCell Integral.lipschitzLowerCell
    Integral.lipschitzUpperCell
  exact Rat.mul_le_mul_of_nonneg_left hinner hwidth

private theorem lowerSum_le_upperSum {f : Rat -> Rat} {L : Nat}
    (intervals : List (Rat × Rat))
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    lowerSum f L intervals <= upperSum f L intervals := by
  induction intervals with
  | nil => simp [lowerSum, upperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨_hp0, hpr, _hr1, hrest⟩
      simp [lowerSum, upperSum]
      exact rat_add_le_add (lowerCell_le_upperCell hpr) (ih hrest)

private theorem cell_width {f : Rat -> Rat} (L : Nat) (p r : Rat) :
    upperCell f L p r - lowerCell f L p r =
      (2 * (L : Rat)) * ((r - p) * (r - p)) := by
  change
    (r - p) * (f p + (L : Rat) * (r - p)) -
        (r - p) * (f p - (L : Rat) * (r - p)) =
      (2 * (L : Rat)) * ((r - p) * (r - p))
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem sum_width {f : Rat -> Rat} (L : Nat)
    (intervals : List (Rat × Rat)) :
    upperSum f L intervals - lowerSum f L intervals =
      (2 * (L : Rat)) * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [lowerSum, upperSum, ArctanGeometry.intervalSquareSum]
      decide +kernel
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      have hcell := cell_width (f := f) L p r
      simp [lowerSum, upperSum, ArctanGeometry.intervalSquareSum]
      calc
        upperCell f L p r + upperSum f L rest -
            (lowerCell f L p r + lowerSum f L rest) =
            (upperCell f L p r - lowerCell f L p r) +
              (upperSum f L rest - lowerSum f L rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ = (2 * (L : Rat)) * ((r - p) * (r - p)) +
              (2 * (L : Rat)) * ArctanGeometry.intervalSquareSum rest := by
              rw [hcell, ih]
        _ = (2 * (L : Rat)) * ((r - p) * (r - p) +
              ArctanGeometry.intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

private theorem lowerSum_left_margin {f : Rat -> Rat} (L : Nat)
    (intervals : List (Rat × Rat)) :
    lowerSum f L intervals =
      leftEndpointSum f intervals -
        (L : Rat) * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [lowerSum, leftEndpointSum, ArctanGeometry.intervalSquareSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [lowerSum, leftEndpointSum, ArctanGeometry.intervalSquareSum]
      rw [ih]
      unfold lowerCell Integral.lipschitzLowerCell
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem upperSum_left_margin {f : Rat -> Rat} (L : Nat)
    (intervals : List (Rat × Rat)) :
    upperSum f L intervals =
      leftEndpointSum f intervals +
        (L : Rat) * ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [upperSum, leftEndpointSum, ArctanGeometry.intervalSquareSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [upperSum, leftEndpointSum, ArctanGeometry.intervalSquareSum]
      rw [ih]
      unfold upperCell Integral.lipschitzUpperCell
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The dyadic Lipschitz box contains an explicit symmetric margin around its
left rectangle sum.  This is the useful computable form of the Darboux
certificate: a stage computation contains every value within its Lipschitz
error radius. -/
theorem compute_contains_uniformLeftEndpointSum_margin
    {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) (stage : Nat) :
    (compute f L stage).lo <=
        uniformLeftEndpointSum f (2 ^ stage) -
          (L : Rat) / (((2 ^ stage : Nat) : Rat)) /\
      uniformLeftEndpointSum f (2 ^ stage) +
          (L : Rat) / (((2 ^ stage : Nat) : Rat)) <=
        (compute f L stage).hi := by
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hsquare := ArctanGeometry.arctanAreaLoopState_one_squareSum stage
  have hmeshRat : 0 < (((2 ^ stage : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hmeshNe : (((2 ^ stage : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hmeshRat
  have hleft := dyadicLeftEndpointSum_eq_uniform f stage
  change lowerSum f L cells <=
      uniformLeftEndpointSum f (2 ^ stage) -
        (L : Rat) / (((2 ^ stage : Nat) : Rat)) /\
    uniformLeftEndpointSum f (2 ^ stage) +
        (L : Rat) / (((2 ^ stage : Nat) : Rat)) <= upperSum f L cells
  rw [lowerSum_left_margin, upperSum_left_margin, hleft, hsquare]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem compute_ordered {f : Rat -> Rat} {L : Nat} (stage : Nat) :
    0 <= (compute f L stage).width := by
  unfold compute QInterval.width
  dsimp
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hunit : ArctanGeometry.UnitIntervals cells :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := 1) (by decide +kernel) (by decide +kernel) stage
  have hsum := lowerSum_le_upperSum (f := f) (L := L) cells hunit
  grind [Rat.sub_eq_add_neg]

theorem compute_width {f : Rat -> Rat} (L stage : Nat) :
    (compute f L stage).width =
      (2 * (L : Rat)) * (1 / (((2 ^ stage : Nat) : Rat))) := by
  unfold compute QInterval.width
  dsimp
  rw [sum_width, ArctanGeometry.arctanAreaLoopState_one_squareSum]

theorem compute_nested {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat))
    (n m : Nat) (hnm : n <= m) :
    (compute f L n).lo <= (compute f L m).lo /\
      (compute f L m).lo <= (compute f L m).hi /\
      (compute f L m).hi <= (compute f L n).hi := by
  induction hnm with
  | refl =>
      have hordered := compute_ordered (f := f) (L := L) n
      unfold QInterval.width at hordered
      have hmid : (compute f L n).lo <= (compute f L n).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_refl, hmid, Rat.le_refl⟩
  | step hnm ih =>
      rename_i k
      have hstep := compute_step_refines hlip k
      have hordered := compute_ordered (f := f) (L := L) (k + 1)
      unfold QInterval.width at hordered
      have hmid : (compute f L (k + 1)).lo <= (compute f L (k + 1)).hi := by
        grind [Rat.sub_eq_add_neg]
      exact ⟨Rat.le_trans ih.1 hstep.1, hmid,
        Rat.le_trans hstep.2 ih.2.2⟩

private theorem succ_le_two_pow (n : Nat) : n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega

theorem compute_width_le_nat_over_succ {f : Rat -> Rat} (L stage : Nat) :
    (compute f L stage).width <=
      ((2 * L : Nat) : Rat) / (((stage + 1 : Nat) : Rat)) := by
  rw [compute_width]
  have hpow : stage + 1 <= 2 ^ stage := succ_le_two_pow stage
  have hinv :
      1 / (((2 ^ stage : Nat) : Rat)) <=
        1 / (((stage + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone (Nat.succ_pos stage)
      (Nat.pow_pos (by omega : 0 < 2)) hpow
  have hL0 : 0 <= (L : Rat) := by
    exact_mod_cast Nat.zero_le L
  have hscale : 0 <= 2 * (L : Rat) :=
    Rat.mul_nonneg (by decide +kernel) hL0
  have hcast : ((2 * L : Nat) : Rat) = 2 * (L : Rat) := by
    exact_mod_cast (by rfl : 2 * L = 2 * L)
  calc
    (2 * (L : Rat)) * (1 / (((2 ^ stage : Nat) : Rat))) <=
        (2 * (L : Rat)) * (1 / (((stage + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hinv hscale
    _ = (2 * (L : Rat)) / (((stage + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]
    _ = ((2 * L : Nat) : Rat) / (((stage + 1 : Nat) : Rat)) := by
      rw [hcast]

private theorem widthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealCompute.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega : C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem compute_widthsShrink {f : Rat -> Rat} (L : Nat) :
    RealCompute.WidthsShrinkToZero (compute f L) :=
  widthsShrink_of_natOverSuccBound (compute_width_le_nat_over_succ L)

/-- The raw real produced by finite unit-interval Lipschitz--Darboux boxes.
At stage `n` its width is exactly `2L / 2^n`. -/
def raw (f : Rat -> Rat) (L : Nat) : RealCompute where
  compute := compute f L

theorem raw_valid {f : Rat -> Rat} {L : Nat}
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) :
    (raw f L).Valid := by
  change RealCompute.ValidCompute (compute f L)
  exact ⟨compute_ordered, compute_nested hlip, compute_widthsShrink L⟩

/-/ Consequently, the two Lipschitz--Darboux raw representations are
equivalent whenever both constants are valid certificates for the same
evaluator. -/
theorem raw_equiv_of_lipschitz_bounds
    {f : Rat -> Rat} {L M : Nat}
    (hL : Integral.LipschitzOnUnit f (L : Rat))
    (hM : Integral.LipschitzOnUnit f (M : Rat)) :
    (raw f L).Equiv (raw f M) := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  exact (RealCompute.compareAt_overlap_iff (raw f L) (raw f M) stage stage).2
    (compute_overlap_of_lipschitz_bounds hL hM stage)

/-- The finite Lipschitz--Darboux sum is compatible with pointwise addition:
the box for `f + g` with bound `L + M` is the interval sum of the two
component boxes. -/
theorem raw_add_equiv
    (f g : Rat -> Rat) (L M : Nat) :
    (raw (fun x => f x + g x) (L + M)).Equiv
      (raw f L + raw g M) := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  apply (RealCompute.compareAt_overlap_iff
    (raw (fun x => f x + g x) (L + M)) (raw f L + raw g M) stage stage).2
  change QInterval.Overlaps
    (compute (fun x => f x + g x) (L + M) stage)
    (QInterval.addInterval (compute f L stage) (compute g M stage))
  rw [compute_add]
  unfold QInterval.Overlaps
  have hf := compute_ordered (f := f) (L := L) stage
  have hg := compute_ordered (f := g) (L := M) stage
  have hf' : (compute f L stage).lo <= (compute f L stage).hi := by
    unfold QInterval.width at hf
    grind [Rat.sub_eq_add_neg]
  have hg' : (compute g M stage).lo <= (compute g M stage).hi := by
    unfold QInterval.width at hg
    grind [Rat.sub_eq_add_neg]
  change
    (compute f L stage).lo + (compute g M stage).lo <=
        (compute f L stage).hi + (compute g M stage).hi /\
      (compute f L stage).lo + (compute g M stage).lo <=
        (compute f L stage).hi + (compute g M stage).hi
  constructor
  · grind [Rat.add_assoc, Rat.add_comm]
  · grind [Rat.add_assoc, Rat.add_comm]

/-- Nonnegative rational scaling is compatible with the Lipschitz--Darboux
raw representation. The natural bound scales with the same factor. -/
theorem raw_natScale_equiv
    (f : Rat -> Rat) (L scale : Nat) :
    (raw (fun x => (scale : Rat) * f x) (scale * L)).Equiv
      (RealCompute.scaleRat (scale : Rat) (raw f L)) := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  apply (RealCompute.compareAt_overlap_iff
    (raw (fun x => (scale : Rat) * f x) (scale * L))
    (RealCompute.scaleRat (scale : Rat) (raw f L)) stage stage).2
  change QInterval.Overlaps
    (compute (fun x => (scale : Rat) * f x) (scale * L) stage)
    (RealCompute.scaleRatCompute (scale : Rat) (raw f L) stage)
  rw [compute_natScale]
  simp only [raw, RealCompute.scaleRatCompute, if_pos Rat.natCast_nonneg]
  unfold QInterval.Overlaps
  have h := compute_ordered (f := f) (L := L) stage
  unfold QInterval.width at h
  have hscaled := Rat.mul_le_mul_of_nonneg_left
    (show (compute f L stage).lo <= (compute f L stage).hi by
      grind [Rat.sub_eq_add_neg]) (Rat.natCast_nonneg : 0 <= (scale : Rat))
  exact ⟨hscaled, hscaled⟩

/-- Package the finite Lipschitz--Darboux algorithm as a construction for the
exact rational kernel that its rectangles evaluate. -/
def construction (f : Rat -> Rat) (L : Nat)
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) :
    Integral.CandidateConstructionFor (FunctionOnInterval.exactRat f 0 1) where
  compute := compute f L
  certificate := raw_valid hlip

end LipschitzDyadic

/-- The identity function is the simplest nonconstant instance of the
finite Lipschitz--Darboux integral.  This witness is intentionally separate
from the exact affine FTC evaluator: it exercises the same rectangle
construction that will be used for less algebraically transparent
integrands. -/
def affineIdentity_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x) 1 := by
  constructor
  · decide +kernel
  · intro s t hs hs1 ht ht1
    rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]
    simpa using (le_refl (qabs (t - s)))

/-- A concrete nonconstant raw integral produced by the generic
Lipschitz--Darboux constructor. -/
def affineIdentityLipschitzConstruction :
    Integral.CandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x : Rat => x) 0 1) :=
  LipschitzDyadic.construction (fun x : Rat => x) 1
    affineIdentity_lipschitz_on_unit

theorem affineIdentityLipschitzConstruction_valid :
    (Integral.candidateValueFor
      (FunctionOnInterval.exactRat (fun x : Rat => x) 0 1)
      affineIdentityLipschitzConstruction).Valid := by
  exact Integral.candidateValueFor_valid _ _

theorem affineIdentity_uniformLeftEndpointSum_eq
    {n : Nat} (hn : 0 < n) :
    LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x) n =
      ((n : Rat) - 1) / (2 * (n : Rat)) := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              ((j : Rat) / (n : Rat))) 0 =
        ((k : Rat) * ((k : Rat) - 1)) / (2 * (n : Rat) ^ 2) := by
    intro k
    induction k with
    | zero =>
        simp [Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ]
  unfold LipschitzDyadic.uniformLeftEndpointSum
  rw [haux n]
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem affineIdentity_uniformRightEndpointSum_eq
    {n : Nat} (hn : 0 < n) :
    LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x) n =
      ((n : Rat) + 1) / (2 * (n : Rat)) := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((Nat.succ j : Nat) : Rat) / (n : Rat))) 0 =
        ((k : Rat) * ((k : Rat) + 1)) / (2 * (n : Rat) ^ 2) := by
    intro k
    induction k with
    | zero =>
        simp [Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        have ih' :
            (List.range k).foldl
                (fun total (j : Nat) =>
                  total + (1 / (n : Rat)) *
                    (((j : Rat) + 1) / (n : Rat))) 0 =
              ((k : Rat) * ((k : Rat) + 1)) / (2 * (n : Rat) ^ 2) := by
          simpa [Nat.succ_eq_add_one, Rat.natCast_add] using ih
        rw [ih']
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ]
  unfold LipschitzDyadic.uniformRightEndpointSum
  rw [haux n]
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem affineIdentityLipschitz_integral_equiv_half :
    (Integral.candidateValueFor
      (FunctionOnInterval.exactRat (fun x : Rat => x) 0 1)
      affineIdentityLipschitzConstruction).Equiv
      (RealCompute.ofRat (1 / 2)) := by
  intro stage
  apply (RealCompute.compareAt_overlap_iff _ _ stage stage).2
  change QInterval.Overlaps
    (LipschitzDyadic.compute (fun x : Rat => x) 1 stage)
    { lo := 1 / 2, hi := 1 / 2 }
  unfold QInterval.Overlaps
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    affineIdentity_lipschitz_on_unit stage
  have hr := LipschitzDyadic.compute_contains_uniformRightEndpointSum
    affineIdentity_lipschitz_on_unit stage
  rw [show 2 ^ stage = n by rfl,
    affineIdentity_uniformLeftEndpointSum_eq hn] at hl
  rw [show 2 ^ stage = n by rfl,
    affineIdentity_uniformRightEndpointSum_eq hn] at hr
  constructor
  · exact Rat.le_trans hl.1 (by
      apply Rat.le_of_mul_le_mul_right (c := 2 * (n : Rat))
      · rw [Rat.div_def]
        have hpos : 0 < 2 * (n : Rat) :=
          Rat.mul_pos (by decide +kernel) ((Rat.natCast_pos).2 hn)
        have hmul := Rat.mul_le_mul_of_nonneg_right
          (show (n : Rat) - 1 <= (n : Rat) by grind) (Rat.le_of_lt hpos)
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add]
      · exact Rat.mul_pos (by decide +kernel) ((Rat.natCast_pos).2 hn))
  · exact Rat.le_trans (by
      apply Rat.le_of_mul_le_mul_right (c := 2 * (n : Rat))
      · rw [Rat.div_def]
        have hpos : 0 < 2 * (n : Rat) :=
          Rat.mul_pos (by decide +kernel) ((Rat.natCast_pos).2 hn)
        have hmul := Rat.mul_le_mul_of_nonneg_right
          (show (n : Rat) <= (n : Rat) + 1 by grind) (Rat.le_of_lt hpos)
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add]
      · exact Rat.mul_pos (by decide +kernel) ((Rat.natCast_pos).2 hn)) hr.2

def arctanKernelLipschitzConstruction :
    Integral.CandidateConstructionFor
      (FunctionOnInterval.exactRat
        (fun x : Rat => 1 / (1 + x * x)) 0 1) :=
  LipschitzDyadic.construction (fun x : Rat => 1 / (1 + x * x)) 2
    oneOverOnePlusSquare_lipschitz_on_unit

def arctanKernelLipschitzIntegral : RealCompute :=
  Integral.candidateValueFor
    (FunctionOnInterval.exactRat (fun x : Rat => 1 / (1 + x * x)) 0 1)
    arctanKernelLipschitzConstruction

theorem arctanKernelLipschitzIntegral_valid :
    arctanKernelLipschitzIntegral.Valid :=
  Integral.candidateValueFor_valid
    (FunctionOnInterval.exactRat (fun x : Rat => 1 / (1 + x * x)) 0 1)
    arctanKernelLipschitzConstruction

theorem arctanKernelLipschitzIntegral_compute_eq (stage : Nat) :
    arctanKernelLipschitzIntegral.compute stage =
      LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage := rfl

theorem arctanKernelLipschitzIntegral_width (stage : Nat) :
    (arctanKernelLipschitzIntegral.compute stage).width =
      4 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  rw [arctanKernelLipschitzIntegral_compute_eq,
    LipschitzDyadic.compute_width]
  have hfour : (2 : Rat) * ((2 : Nat) : Rat) = 4 := by decide +kernel
  rw [hfour]

private theorem arctanKernel_rightEndpointSum_eq_integralLowerSum
    (intervals : List (Rat × Rat)) :
    LipschitzDyadic.rightEndpointSum
      (fun x : Rat => 1 / (1 + x * x)) intervals =
      ArctanGeometry.integralLowerSum intervals := by
  induction intervals with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      simp [LipschitzDyadic.rightEndpointSum,
        ArctanGeometry.integralLowerSum, ArctanGeometry.integralLowerStep,
        ArctanGeometry.integralKernel, ih]

theorem arctanKernelLipschitz_compute_overlaps_rectangle (stage : Nat) :
    QInterval.Overlaps
      (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage)
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne stage) := by
  let cells := (ArctanGeometry.arctanAreaLoopState 1 stage).intervals
  have hcommon := LipschitzDyadic.compute_contains_rightEndpointSum
    (f := fun x : Rat => 1 / (1 + x * x))
    oneOverOnePlusSquare_lipschitz_on_unit stage
  rw [arctanKernel_rightEndpointSum_eq_integralLowerSum] at hcommon
  have hrectangle :
      ArctanGeometry.integralLowerSum cells <=
        ArctanGeometry.integralUpperSum cells :=
    ArctanGeometry.integralLowerSum_le_integralUpperSum cells
      (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative
        (x := 1) (by decide +kernel) stage)
  change QInterval.Overlaps
    (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage)
    (ArctanGeometry.integralSumInterval cells)
  change
    (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage).lo <=
      ArctanGeometry.integralUpperSum cells /\
    ArctanGeometry.integralLowerSum cells <=
      (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage).hi
  change
    (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage).lo <=
      ArctanGeometry.integralLowerSum cells /\
    ArctanGeometry.integralLowerSum cells <=
      (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage).hi at hcommon
  exact ⟨Rat.le_trans hcommon.1 hrectangle, hcommon.2⟩

theorem arctanKernelLipschitzIntegral_equiv_rectangleForAtOne :
    arctanKernelLipschitzIntegral.Equiv
      arctanIntegralRectangleForAtOne := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  apply (RealCompute.compareAt_overlap_iff
    arctanKernelLipschitzIntegral arctanIntegralRectangleForAtOne stage stage).2
  change QInterval.Overlaps
    (LipschitzDyadic.compute (fun x : Rat => 1 / (1 + x * x)) 2 stage)
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne stage)
  exact arctanKernelLipschitz_compute_overlaps_rectangle stage

theorem arctanKernelLipschitzIntegral_equiv_arctanGeom_one :
    arctanKernelLipschitzIntegral.Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) := by
  exact RealCompute.equiv_trans
    arctanKernelLipschitzIntegral_valid
    arctanIntegralRectangleForAtOne_valid
    (ArctanGeometry.arctanGeom_one_valid)
    arctanKernelLipschitzIntegral_equiv_rectangleForAtOne
    arctanIntegralRectangleForAtOne_equiv_arctanGeom_one

theorem arctanKernelLipschitzIntegral_equiv_halfQuarterTurn :
    arctanKernelLipschitzIntegral.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hpi : piCircleArea.Valid := by
    change RealCompute.ValidCompute piCircleArea.compute
    have hcompute : piCircleArea.compute =
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealCompute).compute := by
      funext n
      exact (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm
    rw [hcompute]
    exact ArctanGeometry.four_arctanGeom_one_valid
  have hquarter :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid := by
    change (RealCompute.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
    exact RealCompute.scaleRat_valid_of_nonneg (by decide +kernel)
      hpi
  exact RealCompute.equiv_trans
    arctanKernelLipschitzIntegral_valid
    ArctanGeometry.arctanGeom_one_valid
    hquarter
    arctanKernelLipschitzIntegral_equiv_arctanGeom_one
    ArctanGeometry.arctanGeom_one_equiv_piCircleArea_quarter

/-!
## Finite tangent-chart substitution certificates

The following declarations are deliberately one level below a substitution
theorem. They transport a supplied finite rational partition cell by cell.
The two displayed factors are the exact endpoint Jacobian ratios for the
chart `p ↦ (u + p) / (1 - u*p)`. The final theorem records the resulting
endpoint sums and the interval enclosure; it makes no claim about a limit or
about a general integral substitution principle.
-/

/-- The lower-rectangle Jacobian factor for one admissible chart cell. -/
def chartAddLowerJacobian (u p r : Rat) : Rat :=
  RationalCircle.Trigonometry.chartAddDen u r /
    RationalCircle.Trigonometry.chartAddDen u p

/-- The upper-rectangle Jacobian factor for one admissible chart cell. -/
def chartAddUpperJacobian (u p r : Rat) : Rat :=
  RationalCircle.Trigonometry.chartAddDen u p /
    RationalCircle.Trigonometry.chartAddDen u r

/-- Fold the source lower cells with their explicit chart Jacobian factors. -/
def chartAddLowerTransportSum (u : Rat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      ArctanGeometry.integralLowerStep p r *
          chartAddLowerJacobian u p r +
        chartAddLowerTransportSum u rest

/-- Fold the source upper cells with their explicit chart Jacobian factors. -/
def chartAddUpperTransportSum (u : Rat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      ArctanGeometry.integralUpperStep p r *
          chartAddUpperJacobian u p r +
        chartAddUpperTransportSum u rest

/-- The charted lower-cell sum is exactly the source lower-cell sum with the
explicit right-over-left endpoint Jacobian inserted in every cell. -/
theorem chartAddLowerTransportSum_eq_charted
    (u : Rat) (intervals : List (Rat × Rat))
    (hden : ArctanGeometry.ChartAddPositiveDenominators u intervals) :
    ArctanGeometry.integralLowerSum
        (ArctanGeometry.chartAddIntervals u intervals) =
      chartAddLowerTransportSum u intervals := by
  induction intervals with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      have hpne :
          RationalCircle.Trigonometry.chartAddDen u p ≠ 0 :=
        Rat.ne_of_gt hpden
      have hrne :
          RationalCircle.Trigonometry.chartAddDen u r ≠ 0 :=
        Rat.ne_of_gt hrden
      simp only [ArctanGeometry.chartAddIntervals,
        ArctanGeometry.integralLowerSum,
        chartAddLowerTransportSum]
      rw [ArctanGeometry.integralLowerStep_chartAddParameter_eq
        hpne hrne]
      rw [ih hdenrest]
      rfl

/-- The charted upper-cell sum is exactly the source upper-cell sum with the
explicit left-over-right endpoint Jacobian inserted in every cell. -/
theorem chartAddUpperTransportSum_eq_charted
    (u : Rat) (intervals : List (Rat × Rat))
    (hden : ArctanGeometry.ChartAddPositiveDenominators u intervals) :
    ArctanGeometry.integralUpperSum
        (ArctanGeometry.chartAddIntervals u intervals) =
      chartAddUpperTransportSum u intervals := by
  induction intervals with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨p, r⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      have hpne :
          RationalCircle.Trigonometry.chartAddDen u p ≠ 0 :=
        Rat.ne_of_gt hpden
      have hrne :
          RationalCircle.Trigonometry.chartAddDen u r ≠ 0 :=
        Rat.ne_of_gt hrden
      simp only [ArctanGeometry.chartAddIntervals,
        ArctanGeometry.integralUpperSum,
        chartAddUpperTransportSum]
      rw [ArctanGeometry.integralUpperStep_chartAddParameter_eq
        hpne hrne]
      rw [ih hdenrest]
      rfl

/-- A checked finite rational substitution/partition certificate for the
arctangent kernel. It exposes both endpoint-weighted cell sums, their exact
Jacobian-factor folds, and the fact that the transported rectangle bracket
contains the source bracket. This is a finite partition statement only. -/
theorem chartAddPartition_transport_certificate
    (u : Rat) (intervals : List (Rat × Rat))
    (hu : 0 <= u)
    (hintervals : ArctanGeometry.NonnegativeIntervals intervals)
    (hden : ArctanGeometry.ChartAddPositiveDenominators u intervals) :
    ArctanGeometry.integralLowerSum
        (ArctanGeometry.chartAddIntervals u intervals) =
        chartAddLowerTransportSum u intervals /\
      ArctanGeometry.integralUpperSum
        (ArctanGeometry.chartAddIntervals u intervals) =
        chartAddUpperTransportSum u intervals /\
      (ArctanGeometry.integralSumInterval
        (ArctanGeometry.chartAddIntervals u intervals)).ContainsInterval
        (ArctanGeometry.integralSumInterval intervals) := by
  refine ⟨chartAddLowerTransportSum_eq_charted u intervals hden,
    chartAddUpperTransportSum_eq_charted u intervals hden, ?_⟩
  exact ArctanGeometry.chartAddIntervals_integralSum_contains
    u intervals hu hintervals hden

end IntegralIdentities

/-! Public dot-qualified arctangent integral presentations.

These aliases sit outside `IntegralIdentities` so the names used throughout
the blueprint are useful Lean entry points as well.  The longer names above
remain the implementation-facing constructions and theorems. -/
namespace arctan
namespace integral

/-- Arctangent as the certified rectangle integral of `1 / (1 + x^2)` on the
rational unit branch. -/
def rectangle : Elementary.Arctan.FunctionRepresentation :=
  IntegralIdentities.arctanIntegralRectangleRepresentation

theorem rectangle_raw_eq :
    rectangle.raw = IntegralIdentities.arctanIntegralRectangleFunctionRaw := rfl

/-- The monotone-integral packaging of the same unit-branch rectangle
construction. -/
def rectangleMonotone : Elementary.Arctan.FunctionRepresentation :=
  IntegralIdentities.arctanIntegralRectangleMonotoneRepresentation

theorem rectangleMonotone_raw_eq :
    rectangleMonotone.raw =
      IntegralIdentities.arctanIntegralRectangleMonotoneFunctionRaw := rfl

end integral
end arctan

end ComputableAnalysis


