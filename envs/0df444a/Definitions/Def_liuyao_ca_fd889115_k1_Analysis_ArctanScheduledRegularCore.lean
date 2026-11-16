-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanScheduledRegularCore
-- name    : liuyao_ca_fd889115_k1_Analysis_ArctanScheduledRegularCore
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:05:35.41778+00:00
-- url     : https://prove2.me/theorems/a5402b79-f46c-4e65-911f-d89fed883bfb
-- title:
--   Computable analysis · ArctanScheduledRegularCore · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ArctanScheduledRegularCore.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanGeometry
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus

set_option autoImplicit true

/-!
# A scheduled interval-regular arctangent branch

The geometric arctangent raw already has the desired mathematical meaning, but
its native rectangle evaluator uses a fixed finite stage schedule.  This file
packages a rescheduled version whose output precision is chosen from the
requested interval precision.  It is a separate representation; a later
equivalence theorem can transport inverse-search results to the geometric raw.
-/

namespace ComputableAnalysis

/-- Keep the executable schedule opaque to routine elaboration: unfolding it
inside a rectangle projection can expand dozens of refinements before any
interval lemma is applied. Arithmetic proofs unfold it explicitly. -/
@[irreducible] def arctanScheduledStage (n : Nat) : Nat := Nat.log2 (32*(n+1))+1

def arctanScheduledStageSchedule : RealCompute.StageSchedule where
  stage := arctanScheduledStage
  monotone := by
    intro i j hij
    unfold arctanScheduledStage
    have hi : 32*(i+1) ≠ 0 := by omega
    have hj : 32*(j+1) ≠ 0 := by omega
    have hm : 32*(i+1) ≤ 32*(j+1) := by omega
    have hl := (Nat.le_log2 hj).2 (Nat.le_trans (Nat.log2_self_le hi) hm)
    omega
  cofinal := by
    intro target
    refine ⟨2^target, ?_⟩
    unfold arctanScheduledStage
    have hn : (32*(2^target+1):Nat) ≠ 0 :=
      Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.succ_pos (2^target)))
    have hl := (Nat.le_log2 hn).2 (by omega : 2^target ≤ 32*(2^target+1))
    omega

def arctanScheduledRectangleRaw (x : Rat) : RealCompute where
  compute := fun n =>
    ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)

theorem arctanScheduledRectangleRaw_eq_schedule (x : Rat) :
    arctanScheduledRectangleRaw x =
      RealCompute.schedule arctanScheduledStageSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  rfl

theorem arctanScheduledRectangleRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledRectangleRaw x).Valid := by
  rw [arctanScheduledRectangleRaw_eq_schedule]
  exact RealCompute.schedule_valid
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
    arctanScheduledStageSchedule

theorem arctanScheduledRectangleRaw_equiv_arctanGeom
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledRectangleRaw x).Equiv
      (ArctanGeometry.arctanGeom x) := by
  rw [arctanScheduledRectangleRaw_eq_schedule]
  have hraw :
      (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hscheduled :
      (RealCompute.schedule arctanScheduledStageSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)).Valid :=
    RealCompute.schedule_valid _ hraw arctanScheduledStageSchedule
  have hgeom : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealCompute.equiv_trans hscheduled hraw hgeom
    (RealCompute.equiv_symm (RealCompute.schedule_equiv _ hraw
      arctanScheduledStageSchedule))
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0)

def arctanScheduledRectangleOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx n =>
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n)
    rate := fun _ _ => .unknown
  }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact arctanScheduledRectangleRaw_valid hx.1 hx.2

theorem arctanScheduledRectangleOnUnit_compute_eq
    (x : Rat) (hx : inDomainInterval 0 1 x) (n : Nat) :
    arctanScheduledRectangleOnUnit.compute x hx n =
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n) := by
  rfl

theorem arctanScheduledRectangleOnUnit_width_le
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanScheduledRectangleOnUnit.compute x
      ⟨hx0, hx1⟩ n).width <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
  change (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)).width <=
    1 / (((16 * (n + 1) : Nat) : Rat))
  let k := arctanScheduledStage n
  have hmesh := ArctanGeometry.integralSumInterval_width_le_two_squareSum
    (ArctanGeometry.arctanAreaLoopState x k).intervals
    (ArctanGeometry.arctanAreaLoopState_intervals_unit hx0 hx1 k)
  rw [ArctanGeometry.arctanAreaLoopState_squareSum] at hmesh
  have hx2 : x*x ≤ 1 := by
    simpa using rat_mul_le_mul_of_nonneg hx0 hx1 hx0 hx1
  have hden : 0 < ((2^k:Nat):Rat) := by exact_mod_cast Nat.pow_pos (by omega : 0<2)
  have hscale := Rat.mul_le_mul_of_nonneg_right hx2 (Rat.le_of_lt (Rat.inv_pos.mpr hden))
  have h : (ArctanGeometry.arctanIntegralRectangleCompute x k).width ≤ 2/((2^k:Nat):Rat) := by
    change (ArctanGeometry.arctanIntegralRectangleCompute x k).width ≤ 2*(x*x/((2^k:Nat):Rat)) at hmesh
    rw [Rat.div_def] at hmesh ⊢
    have hm := Rat.mul_le_mul_of_nonneg_left hscale (by decide : (0:Rat)≤2)
    grind only
  have hk : 32*(n+1) ≤ 2^k := by
    have ht := Nat.lt_log2_self (n := 32*(n+1))
    dsimp [k]; unfold arctanScheduledStage; omega
  let A : Rat := ((2^k:Nat):Rat)
  let B : Rat := ((16*(n+1):Nat):Rat)
  have hA : 0 < A := hden
  have hB : 0 < B := by dsimp [B]; exact_mod_cast (by omega : 0 < 16*(n+1))
  have hAB : 2*B ≤ A := by
    dsimp [A,B]
    exact_mod_cast (by omega : 2*(16*(n+1)) ≤ 2^k)
  have hmain : 2/A ≤ 1/B := by
    apply Rat.le_of_mul_le_mul_right (c := A*B)
    · calc
        (2/A)*(A*B) = 2*B := by rw [←Rat.mul_assoc,Rat.div_mul_cancel (Rat.ne_of_gt hA)]
        _ ≤ A := hAB
        _ = (1/B)*(A*B) := by
          rw [Rat.mul_comm A B,←Rat.mul_assoc,Rat.div_mul_cancel (Rat.ne_of_gt hB),Rat.one_mul]
    · exact Rat.mul_pos hA hB
  exact Rat.le_trans h hmain

theorem arctanScheduledRectangleOnUnit_nondecreasing :
    NondecreasingOnInterval arctanScheduledRectangleOnUnit := by
  intro x y hx hy hxy n
  change
    (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)).lo <=
      (ArctanGeometry.arctanIntegralRectangleCompute y
        (arctanScheduledStage n)).hi
  exact ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
    hx.1 hxy (arctanScheduledStage n)

def arctanScheduledRectangleOnUnit_monotone :
    MonotoneOnInterval arctanScheduledRectangleOnUnit :=
  MonotoneOnInterval.ofNondecreasing
    arctanScheduledRectangleOnUnit_nondecreasing

theorem arctanScheduledRectangleOnUnit_strict_separation
    {x y : Rat} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (n : Nat) (hsep : x+1/((n+1:Nat):Rat) ≤ y) :
    ((arctanScheduledRectangleRaw x).compute n).hi < ((arctanScheduledRectangleRaw y).compute n).lo := by
  let k := arctanScheduledStage n
  let delta : Rat := 1/((n+1:Nat):Rat)
  have hd : 0 < delta := one_div_nat_pos (Nat.succ_pos n)
  have hxy : x ≤ y := by change x+delta ≤ y at hsep; grind only
  let left := (ArctanGeometry.arctanAreaLoopState x k).intervals
  let right := (ArctanGeometry.arctanAreaLoopState y k).intervals
  have hleft := ArctanGeometry.arctanAreaLoopState_intervals_covers hx0 k
  have hright := ArctanGeometry.arctanAreaLoopState_intervals_covers hy0 k
  have hcover := ArctanGeometry.CoversInterval.extend_right hleft hxy
  have hc := ArctanGeometry.integralLowerSum_le_integralUpperSum_of_covers
    (by decide : (0:Rat)≤0) (left++[(x,y)]) right hcover hright
  rw [ArctanGeometry.integralLowerSum_append] at hc
  simp only [ArctanGeometry.integralLowerSum,ArctanGeometry.integralLowerStep,Rat.add_zero] at hc
  change (ArctanGeometry.arctanIntegralRectangleCompute x k).lo+
    (y-x)*ArctanGeometry.integralKernel y ≤ (ArctanGeometry.arctanIntegralRectangleCompute y k).hi at hc
  have hy2 : y*y ≤ 1 := by simpa using rat_mul_le_mul_of_nonneg hy0 hy1 hy0 hy1
  have hp := RationalCircle.Stage.one_add_square_pos y
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hinv := Rat.mul_inv_cancel (1+y*y) (Rat.ne_of_gt hp)
  have hkernel : (1:Rat)/2 ≤ ArctanGeometry.integralKernel y := by
    unfold ArctanGeometry.integralKernel
    rw [Rat.div_def,Rat.one_mul]
    apply Rat.le_of_mul_le_mul_right (c := 1+y*y)
    · have hc2 := Rat.mul_le_mul_of_nonneg_left hy2 (by decide +kernel : (0:Rat)≤1/2)
      grind only
    · exact hp
  have hgap : delta ≤ y-x := by change x+delta ≤ y at hsep; grind only
  have hg := Rat.mul_le_mul_of_nonneg_left hkernel (by grind only : 0≤y-x)
  have ht := Rat.mul_le_mul_of_nonneg_right hgap (by decide +kernel : (0:Rat)≤1/2)
  have hwx := arctanScheduledRectangleOnUnit_width_le x hx0 hx1 n
  have hwy := arctanScheduledRectangleOnUnit_width_le y hy0 hy1 n
  have heq : 1/((16*(n+1):Nat):Rat)=delta/16 := by
    rw [Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
    dsimp [delta]; rw [Rat.div_def]
    grind only
  rw [heq] at hwx hwy
  change (ArctanGeometry.arctanIntegralRectangleCompute x k).width ≤ delta/16 at hwx
  change (ArctanGeometry.arctanIntegralRectangleCompute y k).width ≤ delta/16 at hwy
  change (ArctanGeometry.arctanIntegralRectangleCompute x k).hi <
    (ArctanGeometry.arctanIntegralRectangleCompute y k).lo
  unfold QInterval.width at hwx hwy
  have hc16 : (16:Rat)⁻¹=1/16 := by decide +kernel
  have hc2 : (2:Rat)⁻¹=1/2 := by decide +kernel
  rw [Rat.div_def,hc16] at hwx hwy
  grind only

def arctanScheduledRectangleOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation arctanScheduledRectangleOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun n => n
  separated := fun _ _ hx hy n hsep => arctanScheduledRectangleOnUnit_strict_separation hx.1 hx.2 hy.1 hy.2 n hsep

/-! The endpoint-expanded image of a small cell is the interval-level
regularity witness.  This helper isolates the finite width arithmetic from the
record constructor below, which keeps dependent domain proofs out of the main
calculation. -/

def arctanScheduledRectangleOnUnit_evalInterval
    (I : QInterval) (n : Nat) : QInterval :=
  { lo :=
      (ArctanGeometry.arctanIntegralRectangleCompute I.lo
        (arctanScheduledStage n)).lo -
        1 / (((16 * (n + 1) : Nat) : Rat))
    hi :=
      (ArctanGeometry.arctanIntegralRectangleCompute I.hi
        (arctanScheduledStage n)).hi +
        1 / (((16 * (n + 1) : Nat) : Rat)) }

private theorem paddedEndpointImage_width_le
    {A B : QInterval} {n : Nat} {d : Rat}
    (hcross : B.lo <= A.hi)
    (hAwidth : A.width <= 1 / (((16 * (n + 1) : Nat) : Rat)))
    (hBwidth : B.width <= 1 / (((16 * (n + 1) : Nat) : Rat)))
    (hbase : A.lo - B.hi <= d)
    (hstep : d <= 1 / (((2 * (n + 1) : Nat) : Rat))) :
    0 <=
        (A.hi + 1 / (((16 * (n + 1) : Nat) : Rat))) -
          (B.lo - 1 / (((16 * (n + 1) : Nat) : Rat))) /\
      (A.hi + 1 / (((16 * (n + 1) : Nat) : Rat))) -
          (B.lo - 1 / (((16 * (n + 1) : Nat) : Rat))) <=
        1 / (((n + 1 : Nat) : Rat)) := by
  have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hAwidth' : A.hi - A.lo <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    simpa [QInterval.width] using hAwidth
  have hBwidth' : B.hi - B.lo <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    simpa [QInterval.width] using hBwidth
  have hbound : A.hi - B.lo <=
      d + 1 / (((16 * (n + 1) : Nat) : Rat)) * 2 := by
    calc
      A.hi - B.lo = (A.hi - A.lo) + (A.lo - B.hi) + (B.hi - B.lo) := by
        grind only
      _ <= 1 / (((16 * (n + 1) : Nat) : Rat)) + d +
          1 / (((16 * (n + 1) : Nat) : Rat)) := by
        exact rat_add_le_add (rat_add_le_add hAwidth' hbase) hBwidth'
      _ = d + 1 / (((16 * (n + 1) : Nat) : Rat)) * 2 := by
        grind only
  have hsum :
      1 / (((2 * (n + 1) : Nat) : Rat)) +
          1 / (((16 * (n + 1) : Nat) : Rat)) * 4 <=
        1 / (((n + 1 : Nat) : Rat)) := by
    rw [Rat.natCast_mul, Rat.natCast_mul,Rat.div_def,Rat.div_def,Rat.div_def,
      Rat.inv_mul_rev,Rat.inv_mul_rev]
    have h2 : (2:Rat)⁻¹=1/2 := by decide +kernel
    have h16 : (16:Rat)⁻¹=1/16 := by decide +kernel
    change 1*(((n+1:Nat):Rat)⁻¹*(2:Rat)⁻¹)+1*(((n+1:Nat):Rat)⁻¹*(16:Rat)⁻¹)*4 ≤
      1*((n+1:Nat):Rat)⁻¹
    rw [h2,h16]
    have hn := Rat.le_of_lt (Rat.inv_pos.mpr hNpos)
    grind only

  have hbound' := (Rat.add_le_add_right
      (c := 2 * (1 / (((16 * (n + 1) : Nat) : Rat))))).2 hbound
  have hstepSum :
      d + 1 / (((16 * (n + 1) : Nat) : Rat)) * 4 <=
        1 / (((2 * (n + 1) : Nat) : Rat)) +
          1 / (((16 * (n + 1) : Nat) : Rat)) * 4 := by
    exact (Rat.add_le_add_right
      (c := 1 / (((16 * (n + 1) : Nat) : Rat)) * 4)).2 hstep
  have hfinal := Rat.le_trans hstepSum hsum
  constructor
  · have hcross' : 0 <= A.hi - B.lo := by
      grind only
    have heps : 0 <=
        1 / (((16 * (n + 1) : Nat) : Rat)) := by
      exact Rat.le_of_lt (one_div_nat_pos (by omega))
    rw [show
        A.hi + 1 / (((16 * (n + 1) : Nat) : Rat)) -
            (B.lo - 1 / (((16 * (n + 1) : Nat) : Rat))) =
          A.hi - B.lo +
            1 / (((16 * (n + 1) : Nat) : Rat)) * 2 by
        grind only]
    exact Rat.add_nonneg hcross'
      (Rat.mul_nonneg heps (by decide +kernel : (0 : Rat) <= 2))
  · calc
      A.hi + 1 / (((16 * (n + 1) : Nat) : Rat)) -
          (B.lo - 1 / (((16 * (n + 1) : Nat) : Rat))) =
        A.hi - B.lo + 2 * (1 / (((16 * (n + 1) : Nat) : Rat))) := by
          grind only
      _ <= d + 1 / (((16 * (n + 1) : Nat) : Rat)) * 2 +
          2 * (1 / (((16 * (n + 1) : Nat) : Rat))) := hbound'
      _ <= 1 / (((n + 1 : Nat) : Rat)) := by
        apply Rat.le_trans (b := d +
          1 / (((16 * (n + 1) : Nat) : Rat)) * 4)
        · grind only
        · exact hfinal

private theorem arctanScheduledRectangleOnUnit_evalInterval_width_eq
    (I : QInterval) (n : Nat) :
    (arctanScheduledRectangleOnUnit_evalInterval I n).width =
      (ArctanGeometry.arctanIntegralRectangleCompute I.hi
          (arctanScheduledStage n)).hi +
          1 / (((16 * (n + 1) : Nat) : Rat)) -
        ((ArctanGeometry.arctanIntegralRectangleCompute I.lo
          (arctanScheduledStage n)).lo -
          1 / (((16 * (n + 1) : Nat) : Rat))) := by
  rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 2000 in
theorem arctanScheduledRectangleOnUnit_endpointImage_width_le
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat)
    (hLo : inDomainInterval 0 1 I.lo)
    (hHi : inDomainInterval 0 1 I.hi)
    (hsmall : I.width <= 1 / (((2 * (n + 1) : Nat) : Rat)))
    (hpos : 0 < I.hi - I.lo) :
    0 <= (arctanScheduledRectangleOnUnit_evalInterval I n).width /\
      (arctanScheduledRectangleOnUnit_evalInterval I n).width <=
        1 / (((n + 1 : Nat) : Rat)) := by
  have hstep : I.hi - I.lo <=
      1 / (((2 * (n + 1) : Nat) : Rat)) := by
    simpa [QInterval.width] using hsmall
  have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  let A := ArctanGeometry.arctanIntegralRectangleCompute I.hi
        (arctanScheduledStage n)
  let B := ArctanGeometry.arctanIntegralRectangleCompute I.lo
        (arctanScheduledStage n)
  have hboxLo : B.width <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    change (ArctanGeometry.arctanIntegralRectangleCompute I.lo
      (arctanScheduledStage n)).width <= _
    exact arctanScheduledRectangleOnUnit_width_le I.lo hLo.1 hLo.2 n
  have hboxHi : A.width <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    change (ArctanGeometry.arctanIntegralRectangleCompute I.hi
      (arctanScheduledStage n)).width <= _
    exact arctanScheduledRectangleOnUnit_width_le I.hi hHi.1 hHi.2 n
  have hAwidth : A.hi - A.lo <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    simpa [A, QInterval.width] using hboxHi
  have hBwidth : B.hi - B.lo <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
    simpa [B, QInterval.width] using hboxLo
  have hforward :=
    ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
      (x := I.lo) (h := I.hi - I.lo)
      hI.1 hLo.2 hpos (by
        rw [show I.lo + (I.hi - I.lo) = I.hi by grind]
        exact hI.2.2)
      (arctanScheduledStage n)
  rw [show I.lo+(I.hi-I.lo)=I.hi by grind only] at hforward
  change A.lo - B.hi <= I.hi - I.lo at hforward
  have hbase : A.lo - B.hi <= I.hi - I.lo := by
    simpa [A, B] using hforward
  have hpad := paddedEndpointImage_width_le
    (A := A) (B := B) (n := n)
    (ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
      hLo.1 (by exact hI.2.1) (arctanScheduledStage n))
    hAwidth hBwidth hbase hstep
  rw [arctanScheduledRectangleOnUnit_evalInterval_width_eq]
  exact hpad

set_option maxHeartbeats 20000000 in
def arctanScheduledRectangleOnUnit_intervalRegular :
    IntervalRegularOn arctanScheduledRectangleOnUnit where
  evalInterval := fun I _hI n =>
    arctanScheduledRectangleOnUnit_evalInterval I n
  inputPrecision := fun n => 2 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    change 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 at hI
    let hLo : inDomainInterval 0 1 I.lo :=
      ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
    let hHi : inDomainInterval 0 1 I.hi :=
      ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
    by_cases hzero : I.lo = I.hi
    · have hbox := arctanScheduledRectangleOnUnit_width_le I.lo hLo.1 hLo.2 n
      have horder := arctanScheduledRectangleOnUnit.valid_on I.lo hLo
      have hgeomorder :=
        ArctanGeometry.arctanIntegralRectangleCompute_ordered hLo.1
          (arctanScheduledStage n)
      unfold arctanScheduledRectangleOnUnit_evalInterval QInterval.width
      have hEq : I.hi = I.lo := hzero.symm
      rw [hEq]
      dsimp
      change 0 <= _ ∧ _ <= 1 / (((n + 1 : Nat) : Rat))
      constructor
      · have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
          (Rat.natCast_pos).2 (Nat.succ_pos n)
        have hw : 0 <=
            1 / (((16 * (n + 1) : Nat) : Rat)) := by
          exact Rat.le_of_lt (one_div_nat_pos (by omega))
        have hrewrite :
            (ArctanGeometry.arctanIntegralRectangleCompute I.lo
              (arctanScheduledStage n)).hi +
                1 / (((16 * (n + 1) : Nat) : Rat)) -
              ((ArctanGeometry.arctanIntegralRectangleCompute I.lo
                (arctanScheduledStage n)).lo -
                1 / (((16 * (n + 1) : Nat) : Rat))) =
            (ArctanGeometry.arctanIntegralRectangleCompute I.lo
              (arctanScheduledStage n)).hi -
              (ArctanGeometry.arctanIntegralRectangleCompute I.lo
                (arctanScheduledStage n)).lo +
              1 / (((16 * (n + 1) : Nat) : Rat)) * 2 := by
          grind only
        rw [hrewrite]
        exact Rat.add_nonneg hgeomorder
          (Rat.mul_nonneg hw (by decide +kernel))
      · have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
          (Rat.natCast_pos).2 (Nat.succ_pos n)
        have hbox' :
            (ArctanGeometry.arctanIntegralRectangleCompute I.lo
              (arctanScheduledStage n)).hi -
              (ArctanGeometry.arctanIntegralRectangleCompute I.lo
                (arctanScheduledStage n)).lo <=
              1 / (((16 * (n + 1) : Nat) : Rat)) := by
          change (ArctanGeometry.arctanIntegralRectangleCompute I.lo
            (arctanScheduledStage n)).width <= _ at hbox
          simpa [QInterval.width] using hbox
        have hthree :
            1 / (((16 * (n + 1) : Nat) : Rat)) * 3 <=
              1 / (((n + 1 : Nat) : Rat)) := by
          rw [Rat.natCast_mul,Rat.div_def,Rat.div_def,Rat.inv_mul_rev]
          have h16 : (16:Rat)⁻¹=1/16 := by decide +kernel
          change 1*(((n+1:Nat):Rat)⁻¹*(16:Rat)⁻¹)*3 ≤ 1*((n+1:Nat):Rat)⁻¹
          rw [h16]
          have hn := Rat.le_of_lt (Rat.inv_pos.mpr hNpos)
          grind only

        have hrewrite :
            (ArctanGeometry.arctanIntegralRectangleCompute I.lo
              (arctanScheduledStage n)).hi +
                1 / (((16 * (n + 1) : Nat) : Rat)) -
              ((ArctanGeometry.arctanIntegralRectangleCompute I.lo
                (arctanScheduledStage n)).lo -
                1 / (((16 * (n + 1) : Nat) : Rat))) =
            (ArctanGeometry.arctanIntegralRectangleCompute I.lo
              (arctanScheduledStage n)).hi -
              (ArctanGeometry.arctanIntegralRectangleCompute I.lo
                (arctanScheduledStage n)).lo +
              1 / (((16 * (n + 1) : Nat) : Rat)) * 2 := by
          grind only
        rw [hrewrite]
        have hsum := (Rat.add_le_add_right
          (c := 1 / (((16 * (n + 1) : Nat) : Rat)) * 2)).2 hbox'
        exact Rat.le_trans hsum (by
          grind only)
    · exact arctanScheduledRectangleOnUnit_endpointImage_width_le I ⟨hI.1, hI.2.1, hI.2.2⟩ n
        hLo hHi hsmall (by grind only)
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    change 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 at hI
    have hpoint := arctanScheduledRectangleOnUnit_width_le x hx.1 hx.2 n
    unfold arctanScheduledRectangleOnUnit_evalInterval QInterval.ContainsInterval
    change
      (ArctanGeometry.arctanIntegralRectangleCompute I.lo
        (arctanScheduledStage n)).lo -
          1 / (((16 * (n + 1) : Nat) : Rat)) <=
        (ArctanGeometry.arctanIntegralRectangleCompute x
          (arctanScheduledStage n)).lo ∧
      (ArctanGeometry.arctanIntegralRectangleCompute x
          (arctanScheduledStage n)).hi <=
        (ArctanGeometry.arctanIntegralRectangleCompute I.hi
          (arctanScheduledStage n)).hi +
          1 / (((16 * (n + 1) : Nat) : Rat))
    change (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)).width <= _ at hpoint
    unfold QInterval.width at hpoint
    have hleft :=
      ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        hI.1 hIlo (arctanScheduledStage n)
    have hright :=
      ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        (Rat.le_trans hI.1 hIlo) hIhi
        (arctanScheduledStage n)
    constructor
    · grind only
    · grind only

/-- The scheduled rectangle branch now has all data required by the inverse
search interface: interval regularity, weak monotonicity, and strict finite
separation. -/
def arctanScheduledRectangleOnUnit_invertible :
    InvertibleFunctionOnInterval where
  continuous :=
    { function := arctanScheduledRectangleOnUnit
      regular := arctanScheduledRectangleOnUnit_intervalRegular }
  source_ordered := by decide +kernel
  monotone := arctanScheduledRectangleOnUnit_monotone
  separation := arctanScheduledRectangleOnUnit_effectiveInverseSeparation
  orientation := trivial

end ComputableAnalysis


