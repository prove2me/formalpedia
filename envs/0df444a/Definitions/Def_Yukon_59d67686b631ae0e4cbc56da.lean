-- Prove2me | Definitions.Def_Yukon_59d67686b631ae0e4cbc56da
-- name    : Yukon_59d67686b631ae0e4cbc56da
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T03:52:33.160452+00:00
-- url     : https://prove2.me/theorems/6476bc09-ed24-4d0a-aab0-54ff0ae406a7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceHybridCount6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceHybridCount6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceHybridCount6814.lean
--
--   yukon-proof-operation:certificate-b56-217e527cb1405ab9fce1af63568b9f396387760a9ab5b56e91b2995625b2b4d6-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjFmNmNjNGYyMjVlNWIxNGU0ZjNkMzc0ZmQ5ZjVlYmI3ZDhhMGU4MWYwYjI5ZTE1MjcxYzhhNzQzMzVlZTJjMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni0yMTdlNTI3Y2IxNDA1YWI5ZmNlMWFmNjM1NjhiOWYzOTYzODc3NjBhOWFiNWI1NmU5MWIyOTk1NjI1YjJiNGQ2LXBhcnNlci1yZXRyeSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzU5ZDY3Njg2YjYzMWFlMGU0Y2JjNTZkYSIsInYiOjJ9]

import Definitions.Def_Yukon_ba2ee1ab868a502d09acf5a7
















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Keep the old Z-source estimate on the SAME projections as the new
proper pair, then bound actual isolated zeros. No desired Z estimate is
assumed: it is supplied by the existing source-sensitive degree theorem. -/
namespace ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
open scoped BigOperators
open RCN002 RCN037 RCN042 RCN046 RCN072 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN341 RCN344
open SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811 MovingFiberThreeSources6811 MovingFiberNativeBudget6811

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local notation "Poly3" => MvPolynomial (Fin 3) Ω

theorem old_z_bound_on_new_projections
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (S : Source F)
    (carrier : Poly3) (p : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all)<c)
    (h2 : (2 : Ω)≠0) (hfact : (S.k.factorial : Ω)≠0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (R : Poly3)
    (hH : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      surfaceMap phi (RCN313.polyH K F)∉C.1)
    (hL : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      S.leading phi∉C.1)
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      SeparableLiteralCoordinate C.1)
    (pNew qNew : FlagDegree) (unit : AdaptiveUnitProjectionFamily base pNew qNew) :
    S.d*(∑ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      coordinateDegree Ω (CoordinateField Ω C.1) (unit.zProjection C)) ≤
      flagMixed p unitZFlag S.flag := by
  classical
  let H := surfaceMap phi (RCN313.polyH K F)
  let M := movingEquation H (surfaceMap phi (RCN313.polyG K F)) Q A target
  let Family := RegularComponent Ω carrier M R
  let forget (C : Family) : RegularComponent Ω carrier M (H*S.leading phi) :=
    ⟨C.1,(mem_regularComponents Ω).mpr ⟨regularComponent_mem Ω carrier M R C,by
      intro hz
      exact ((inferInstance : C.1.IsPrime).mem_or_mem hz).elim (hH C) (hL C)⟩⟩
  have hinj : Function.Injective forget := by
    intro C D h
    exact Subtype.ext (congrArg (fun C0 : RegularComponent Ω carrier M (H*S.leading phi) => C0.1) h)
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext)≠0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfe : (S.k.factorial : Ext)≠0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne hfact
  exact sum_coordinate_projection_degrees (E:=Ext) phi F carrier p unitZFlag hcarrier hcarrierF hflag
    linearZ linearZ_flag c (by omega) (by simpa [unitZFlag] using hunit)
    S.P S.B S.U S.T S.s S.k S.n0 S.hS S.hshape S.hBU S.hUT S.hdn S.hB S.hn S.hdiv
    h2e hfe Q A target hQ hA forget hinj unit.zProjection unit.zValue

/-- Actual isolated points are counted against the mixed old-Z/new-U/V
budget. The Z inequality is a separate intermediate premise here, with
its non-conditional source supplier immediately above. -/
theorem hybrid_isolated_points
    {G M R : Poly3}
    (base : ∀ C : RegularComponent Ω G M R, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (d zCap : ℕ)
    (hZ : d*(∑ C : RegularComponent Ω G M R,
      coordinateDegree Ω (CoordinateField Ω C.1) (unit.zProjection C))≤zCap)
    (W : FlagDegree) (cut : Poly3) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hG : ∀ x ∈ points, MvPolynomial.eval x G=0)
    (hM : ∀ x ∈ points, MvPolynomial.eval x M=0)
    (hR : ∀ x ∈ points, MvPolynomial.eval x R≠0)
    (hzero : ∀ x ∈ points, MvPolynomial.aeval x cut=0)
    (hisolated : ∀ x ∈ points, IsolatedPoint G M cut x) :
    d*points.card ≤ W.zOnly*zCap+
      d*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag) := by
  classical
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card≤∑ C : RegularComponent Ω G M R, budget.weightedCost W C := by
    apply (card_le_sum_componentSeeds Ω G M R points id hG hM hR).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he : (componentSeeds Ω G M R points id C).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω G M R points id C hx
      have hxC := componentSeeds_on_prime Ω G M R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (regularComponent_ne_point Ω G M R C)
          hxC (regularComponent_G_mem Ω G M R C) (regularComponent_T_mem Ω G M R C))
      · intro y hy
        exact componentSeeds_on_prime Ω G M R points id C y hy
      · intro y hy
        exact hzero y (componentSeeds_subset Ω G M R points id C hy)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have heq : d*(∑ C : RegularComponent Ω G M R, budget.weightedCost W C)=
      W.zOnly*(d*∑ C : RegularComponent Ω G M R,
        coordinateDegree Ω (CoordinateField Ω C.1) (unit.zProjection C))+
      d*(W.yz*(∑ C : RegularComponent Ω G M R,
        coordinateDegree Ω (CoordinateField Ω C.1) (unit.yzProjection C))+
        W.all*(∑ C : RegularComponent Ω G M R,
          coordinateDegree Ω (CoordinateField Ω C.1) (unit.allProjection C))) := by
    simp only [budget,PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
      RCN340.AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget,
      Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  calc
    d*points.card ≤ d*(∑ C : RegularComponent Ω G M R, budget.weightedCost W C) :=
      Nat.mul_le_mul_left d hcard
    _ = _ := heq
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left W.zOnly hZ)
      (Nat.mul_le_mul_left d (Nat.add_le_add
        (Nat.mul_le_mul_left W.yz unit.sum_yzDegree_le)
        (Nat.mul_le_mul_left W.all unit.sum_allDegree_le)))





end
end ProximityPrize.SubmissionLower.MovingSourceHybridCount6814


