-- Prove2me | Definitions.Def_Yukon_dfafa1981f6a18298a70edfc
-- name    : Yukon_dfafa1981f6a18298a70edfc
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T01:01:03.877437+00:00
-- url     : https://prove2.me/theorems/ed0e3fe7-9376-4e7e-86c2-0871d9761d4d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceFrameZeroCount6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-15ff28b36691d7ba5a4bfba3037f058aaf386f8fb0f59f8adc8c1fa702533c9e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmZiZjM5MjJhYmE4YTRiZmNhMzJkYWNiNWY2YjI0Y2E3NDJhMTRmNDA0NTg4MGM3MDA0MjM5ZjdiMzlhZTA5ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtMTVmZjI4YjM2NjkxZDdiYTVhNGJmYmEzMDM3ZjA1OGFhZjM4NmY4ZmIwZjU5ZjhhZGM4YzFmYTcwMjUzM2M5ZSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2RmYWZhMTk4MWY2YTE4Mjk4YTcwZWRmYyIsInYiOjJ9]

import Definitions.Def_Yukon_89b17c85954a108661049f02















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The constructed frame really bounds zeros of a proper cut on each
prime. The budget below is proved from poles, not assumed as a supplier. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators WithZero
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN114 RCN165 RCN295 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814
open MovingSourceLinearCycleFamily6814

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {A : Type} [Fintype A]
variable {P : A → Ideal (MvPolynomial (Fin 3) Ω)} [∀ a,(P a).IsPrime]
variable {surface : MvPolynomial (Fin 3) Ω}
variable (D : GammaFrame P surface)
variable (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
variable (hgate : ∀ a,
  (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
  (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))

include hgate in
theorem frame_unit_poles (axis : Axis) (a : A)
    (W : Finset (Place Ω (CoordinateField Ω (P a)))) :
    (∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag)) ≤
      (frameCost D hz axis a : ℤ) := by
  let projection := coordinateOfGate
    (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_gate D hz hgate axis a)
  have he : coordinateDegree Ω (CoordinateField Ω (P a)) projection=frameCost D hz axis a :=
    coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  have hp (v : Place Ω (CoordinateField Ω (P a))) :
      exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag)=
        RCN346.poleOrder Ω (CoordinateField Ω (P a)) v
          (coordinateValue Ω (CoordinateField Ω (P a)) projection) := by
    dsimp only [projection]
    rw [coordinateOfGate_value]
    change _=RCN187.poleOrder v.val _
    cases axis with
    | z => simp only [Axis.flag,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,
        flagEvaluation_X_two,exponentSetPoleWeight_unitZ]
    | u =>
      simp only [Axis.flag,Axis.order,RCN125.uOrder,Equiv.refl_apply,
        flagEvaluation_X_zero,exponentSetPoleWeight_unitYZ]
      exact (D.uPole a v).symm
    | v =>
      simp only [Axis.flag,Axis.order,RCN125.vOrder,Equiv.swap_apply_left,
        flagEvaluation_X_one,exponentSetPoleWeight_unitAll]
      exact (D.vPole a v).symm
  calc
    _=∑ v∈W, RCN346.poleOrder Ω (CoordinateField Ω (P a)) v
        (coordinateValue Ω (CoordinateField Ω (P a)) projection) :=
      Finset.sum_congr rfl (fun v _ => hp v)
    _≤(coordinateDegree Ω (CoordinateField Ω (P a)) projection : ℤ) :=
      finite_sum_coordinate_pole_le_degree Ω (CoordinateField Ω (P a)) projection W
    _= _ := by rw [he]

def frameFlagCost (a : A) (r : FlagDegree) : ℕ :=
  r.zOnly*frameCost D hz .z a+r.yz*frameCost D hz .u a+r.all*frameCost D hz .v a

def frame_prime_budget (a : A) : PrimeFlagZeroBudget (P a) (frameFlagCost D hz a) := by
  classical
  let base : SeparableLiteralCoordinate (P a) := ⟨2,hz a,(hgate a).1,(hgate a).2⟩
  refine ⟨?_⟩
  intro r N hN hproper points hpointsP hpointsN
  have hpole : ∀ W : Finset (Place Ω (CoordinateField Ω (P a))),
      (∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport r)) ≤
        (frameFlagCost D hz a r : ℤ) := by
    intro W
    have hz' := frame_unit_poles D hz hgate .z a W
    have hu' := frame_unit_poles D hz hgate .u a W
    have hv' := frame_unit_poles D hz hgate .v a W
    calc
      _≤∑ v∈W, ((r.zOnly : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag)+
          (r.yz : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag)+
          (r.all : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)) :=
        Finset.sum_le_sum (fun v _ => exponentSetPoleWeight_flagSupport_le_three v.val (coordinate Ω (P a)) r)
      _=(r.zOnly : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag))+
          (r.yz : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag))+
          (r.all : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _≤(r.zOnly : ℤ)*(frameCost D hz .z a : ℤ)+
          (r.yz : ℤ)*(frameCost D hz .u a : ℤ)+(r.all : ℤ)*(frameCost D hz .v a : ℤ) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hz' (by positivity))
          (mul_le_mul_of_nonneg_left hu' (by positivity)))
          (mul_le_mul_of_nonneg_left hv' (by positivity))
      _= _ := by simp only [frameFlagCost,Nat.cast_add,Nat.cast_mul]
  exact finite_zero_points_le_exponentSet_of_literalCoordinate (P a) base
    (flagSupport r) (frameFlagCost D hz a r) hpole N
    ((support_subset_flagSupport_iff r N).mpr hN) hproper points hpointsP hpointsN



end
end ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814


