-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanSecantFoundation
-- name    : liuyao_ca_fd889115_k1_Analysis_ArctanSecantFoundation
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:08:26.40125+00:00
-- url     : https://prove2.me/theorems/3697bd06-47a0-421f-8a8e-845a94dad0fc
-- title:
--   Computable analysis · ArctanSecantFoundation · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ArctanSecantFoundation.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanScheduledRegularCore
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_SecantFoundation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteDerivativeLimit
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneIntegralBounds

set_option autoImplicit true

/-! The geometric unit arctangent, its concrete secant bounds and derivative.
The primary evaluations are at rational slopes. No inverse or derivative
existence theorem is used to obtain the finite estimates. -/
namespace ComputableAnalysis.ArctanSecantFoundation
open ArctanGeometry
set_option maxHeartbeats 2000000

def value := arctanScheduledRectangleRaw
def function := arctanScheduledRectangleOnUnit
def kernelFunction : FunctionOnInterval := FunctionOnInterval.exactRat integralKernel 0 1

theorem value_valid {x : Rat} (hx : 0 ≤ x ∧ x ≤ 1) : (value x).Valid :=
  arctanScheduledRectangleRaw_valid hx.1 hx.2

/-- Finite rectangle comparison bounds the actual geometric increment. -/
theorem increment_bounds {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y)
    (n : Nat) :
    (y-x)*integralKernel y ≤ ((value y).compute n).hi-((value x).compute n).lo ∧
    ((value y).compute n).lo-((value x).compute n).hi ≤ (y-x)*integralKernel x := by
  let k := arctanScheduledStage n
  let left := (arctanAreaLoopState x k).intervals
  let right := (arctanAreaLoopState y k).intervals
  have hcL := CoversInterval.extend_right (arctanAreaLoopState_intervals_covers hx k) hxy
  have hcR := arctanAreaLoopState_intervals_covers (Rat.le_trans hx hxy) k
  have hl := integralLowerSum_le_integralUpperSum_of_covers
    (by decide +kernel : (0:Rat)≤0) (left++[(x,y)]) right hcL hcR
  have hu := integralLowerSum_le_integralUpperSum_of_covers
    (by decide +kernel : (0:Rat)≤0) right (left++[(x,y)]) hcR hcL
  rw [integralLowerSum_append] at hl
  rw [integralUpperSum_append] at hu
  simp only [integralLowerSum,integralUpperSum,integralLowerStep,integralUpperStep,Rat.add_zero] at hl hu
  change (arctanIntegralRectangleCompute x k).lo+(y-x)*integralKernel y ≤
    (arctanIntegralRectangleCompute y k).hi at hl
  change (arctanIntegralRectangleCompute y k).lo ≤
    (arctanIntegralRectangleCompute x k).hi+(y-x)*integralKernel x at hu
  constructor <;> change _ ≤ _ <;> dsimp [value,arctanScheduledRectangleRaw] <;> grind

theorem kernel_bounds {x : Rat} (hx : 0 ≤ x ∧ x ≤ 1) :
    (1:Rat)/2 ≤ integralKernel x ∧ integralKernel x ≤ 1 := by
  have hp := RationalCircle.Stage.one_add_square_pos x
  have hn := Rat.mul_inv_cancel (1+x*x) (Rat.ne_of_gt hp)
  have hsq : 0 ≤ x*x := Rat.mul_nonneg hx.1 hx.1
  have hsq1 : x*x ≤ 1 := by simpa using rat_mul_le_mul_of_nonneg hx.1 hx.2 hx.1 hx.2
  unfold integralKernel
  simp only [Rat.div_def,Rat.one_mul]
  constructor
  · apply Rat.le_of_mul_le_mul_right (c:=1+x*x) _ hp
    grind
  · apply Rat.le_of_mul_le_mul_right (c:=1+x*x) _ hp
    grind

theorem kernel_variation {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    0 ≤ integralKernel x-integralKernel y ∧
    integralKernel x-integralKernel y ≤ 2*(y-x) := by
  have hm := integralKernel_antitone_nonneg hx hxy
  have hy0 := Rat.le_trans hx hxy
  have hx1 := Rat.le_trans hxy hy
  have hp := RationalCircle.Stage.one_add_square_pos x
  have hq := RationalCircle.Stage.one_add_square_pos y
  have hc := Rat.mul_inv_cancel (1+x*x) (Rat.ne_of_gt hp)
  have hd := Rat.mul_inv_cancel (1+y*y) (Rat.ne_of_gt hq)
  have hi := (kernel_bounds ⟨hx,hx1⟩).2
  have hj := (kernel_bounds ⟨hy0,hy⟩).2
  have hip : 0 ≤ (1+x*x)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hjp : 0 ≤ (1+y*y)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hq)
  have he : integralKernel x-integralKernel y =
      (y-x)*(y+x)*((1+x*x)⁻¹*(1+y*y)⁻¹) := by
    unfold integralKernel
    simp only [Rat.div_def,Rat.one_mul]
    grind
  have hsum : 0 ≤ y+x ∧ y+x ≤ 2 := by grind
  simp only [integralKernel,Rat.div_def,Rat.one_mul] at hi
  simp only [integralKernel,Rat.div_def,Rat.one_mul] at hj
  have hprod := rat_mul_le_mul_of_nonneg hip hi hjp hj
  have hterm := rat_mul_le_mul_of_nonneg (by grind : 0 ≤ y+x) hsum.2
    (Rat.mul_nonneg hip hjp) (by simpa using hprod)
  have hfinal := Rat.mul_le_mul_of_nonneg_left hterm (by grind : 0 ≤ y-x)
  constructor
  · grind
  · rw [he]; grind

def tolerance (h : Rat) (n : Nat) : QPos :=
  if hh : 0 < qabs h then
    ⟨qabs h*(precisionAtStage n).val/8,by
      rw [Rat.div_def]
      exact Rat.mul_pos (Rat.mul_pos hh (precisionAtStage n).property)
        (Rat.inv_pos.mpr (by decide +kernel))⟩
  else ⟨1,by decide +kernel⟩

def evalPrecision (h : Rat) (n : Nat) : Nat := RationalMajorant.natRateStage 1 (tolerance h n)
def stepPrecision (n : Nat) : Nat := 8*(n+1)

theorem source_width {x h : Rat} (hx : 0 ≤ x ∧ x ≤ 1) (hh : h≠0) (n : Nat) :
    ((value x).compute (evalPrecision h n)).width ≤ qabs h*(precisionAtStage n).val/8 := by
  have ha : 0 < qabs h := qabs_pos_of_ne hh
  have hb := RationalMajorant.natRateStage_spec_of_le (bound:=1)
    (by decide +kernel) (tolerance h n) (Nat.le_refl (evalPrecision h n))
  have hw := arctanScheduledRectangleOnUnit_width_le x hx.1 hx.2 (evalPrecision h n)
  have hden : 0 < ((evalPrecision h n+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos _
  have hs : 1/((16*(evalPrecision h n+1):Nat):Rat) ≤ 1/((evalPrecision h n+1:Nat):Rat) := by
    rw [Rat.natCast_mul,Rat.div_def,Rat.div_def,Rat.inv_mul_rev]
    have hp := Rat.mul_le_mul_of_nonneg_right (by decide +kernel : (16:Rat)⁻¹≤1)
      (Rat.le_of_lt (Rat.inv_pos.mpr hden))
    have hcast : ((16:Nat):Rat) = 16 := by decide +kernel
    rw [hcast,Rat.mul_comm]
    simpa only [Rat.mul_one,Rat.one_mul,Rat.mul_comm] using hp
  change ((value x).compute (evalPrecision h n)).width ≤ _ at hw
  have ht : (tolerance h n).val = qabs h*(precisionAtStage n).val/8 := by
    simp only [tolerance,dif_pos ha]
  rw [ht] at hb
  exact Rat.le_trans hw (Rat.le_trans hs hb)

theorem step_budget {h : Rat} (n : Nat)
    (hs : qabs h ≤ 1/(stepPrecision n:Rat)) :
    2*qabs h ≤ (precisionAtStage n).val/2 := by
  have hp : 0 < ((n+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos n
  have hc := Rat.mul_inv_cancel ((n+1:Nat):Rat) (Rat.ne_of_gt hp)
  have he : 1/(stepPrecision n:Rat) = (1/((n+1:Nat):Rat))/8 := by
    simp only [stepPrecision,Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
    grind
  rw [he] at hs
  by_cases hn : n=0
  · subst n; simp only [precisionAtStage,if_pos rfl] at *; grind
  · have hpN : 0 < (n:Rat) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcN := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hpN)
    have hmono : 1/((n+1:Nat):Rat) ≤ 1/(n:Rat) := by
      apply Rat.le_of_mul_le_mul_right (c:=(n:Rat)*((n+1:Nat):Rat)) _ (Rat.mul_pos hpN hp)
      simp only [Rat.div_def,Rat.one_mul]
      have hcast : (n:Rat) ≤ ((n+1:Nat):Rat) := by exact_mod_cast Nat.le_succ n
      grind [Rat.mul_assoc,Rat.mul_comm]
    simp only [precisionAtStage,if_neg hn]
    have hm := Rat.mul_le_mul_of_nonneg_right hmono (by decide +kernel : (0:Rat)≤(8:Rat)⁻¹)
    rw [Rat.div_def] at hs
    grind

def hasDerivative : HasDerivativeOnInterval function kernelFunction where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := stepPrecision
  evalPrecision := fun _ h n => evalPrecision h n
  close := by
    intro x h n hx hxh _ hh hs
    change 0 ≤ x ∧ x ≤ 1 at hx
    change 0 ≤ x+h ∧ x+h ≤ 1 at hxh
    let p := evalPrecision h n
    let Q := QInterval.differenceQuotient ((value (x+h)).compute p) ((value x).compute p) h
    let e := (precisionAtStage n).val
    have hwx := source_width hx hh n
    have hwy := source_width hxh hh n
    have ha := qabs_pos_of_ne hh
    have hac := Rat.mul_inv_cancel (qabs h) (Rat.ne_of_gt ha)
    have hw : Q.width ≤ e/4 := by
      rw [QInterval.differenceQuotient_width,SecantFoundation.abs_div 1 h hh,show qabs (1:Rat)=1 by decide +kernel,Rat.div_def,Rat.one_mul]
      have hm := Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hwy hwx)
        (Rat.le_of_lt (Rat.inv_pos.mpr ha))
      change (qabs h)⁻¹*(((value (x+h)).compute p).width+((value x).compute p).width) ≤ _
      dsimp [e]; grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]
    have hb := step_budget n hs
    have hc := Rat.mul_inv_cancel h hh
    have hnear : Q.lo ≤ integralKernel x+e ∧ integralKernel x ≤ Q.hi+e := by
      by_cases hp : 0 < h
      · have hi := increment_bounds hx.1 (by grind : x≤x+h) p
        have hv := kernel_variation hx.1 (by grind : x≤x+h) hxh.2
        have hlo : integralKernel (x+h) ≤ Q.hi := by
          have hm := Rat.mul_le_mul_of_nonneg_left hi.1 (Rat.le_of_lt (Rat.inv_pos.mpr hp))
          dsimp [Q,QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat]
          simp only [Rat.div_def,Rat.one_mul,if_pos (Rat.le_of_lt (Rat.inv_pos.mpr hp)),QInterval.sub]
          grind [Rat.mul_assoc,Rat.mul_comm]
        have hhi : Q.lo ≤ integralKernel x := by
          have hm := Rat.mul_le_mul_of_nonneg_left hi.2 (Rat.le_of_lt (Rat.inv_pos.mpr hp))
          dsimp [Q,QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat]
          simp only [Rat.div_def,Rat.one_mul,if_pos (Rat.le_of_lt (Rat.inv_pos.mpr hp)),QInterval.sub]
          grind [Rat.mul_assoc,Rat.mul_comm]
        rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hp)] at hb
        constructor <;> grind
      · have hn : h<0 := by grind
        have hinv : ¬ 0≤h⁻¹ := by
          intro hi
          have hm := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hn) hi
          grind
        have hcneg := Rat.mul_inv_cancel (-h) (by grind : -h≠0)
        have hineg : (-h)⁻¹ = -h⁻¹ := by
          have hpneg : 0 < -h := by grind
          apply Rat.le_antisymm
          · apply Rat.le_of_mul_le_mul_right (c := -h) _ hpneg
            grind [Rat.mul_assoc,Rat.mul_comm]
          · apply Rat.le_of_mul_le_mul_right (c := -h) _ hpneg
            grind [Rat.mul_assoc,Rat.mul_comm]
        have hi := increment_bounds hxh.1 (by grind : x+h≤x) p
        have hv := kernel_variation hxh.1 (by grind : x+h≤x) hx.2
        have hlo : integralKernel x ≤ Q.hi := by
          have hm := Rat.mul_le_mul_of_nonneg_right hi.1
            (Rat.le_of_lt (Rat.inv_pos.mpr (by grind : 0 < -h)))
          dsimp [Q,QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat]
          simp only [Rat.div_def,Rat.one_mul,if_neg hinv,QInterval.sub,hineg] at *
          grind [Rat.mul_assoc,Rat.mul_comm]
        have hhi : Q.lo ≤ integralKernel (x+h) := by
          have hm := Rat.mul_le_mul_of_nonneg_right hi.2
            (Rat.le_of_lt (Rat.inv_pos.mpr (by grind : 0 < -h)))
          dsimp [Q,QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat]
          simp only [Rat.div_def,Rat.one_mul,if_neg hinv,QInterval.sub,hineg] at *
          grind [Rat.mul_assoc,Rat.mul_comm]
        rw [qabs_eq_neg_of_nonpos (Rat.le_of_lt hn)] at hb
        constructor <;> grind
    change QInterval.NearAt Q (({lo:=integralKernel x,hi:=integralKernel x}:QInterval)) (precisionAtStage n)
    unfold QInterval.NearAt
    exact ⟨hnear.1,hnear.2,Rat.le_trans hw (by dsimp [e]; have := (precisionAtStage n).property; grind),by
      unfold QInterval.width; have := (precisionAtStage n).property; grind⟩

def derivative (x radius : Rat) : RealCompute :=
  SecantFoundation.derivative hasDerivative x radius (fun _ => 0)

theorem derivative_valid_and_equiv (x radius : Rat)
    (hr : 0<radius) (hr1 : radius≤1)
    (hl : 0≤x-radius) (hu : x+radius≤1) :
    (derivative x radius).Valid ∧
      (derivative x radius).Equiv (RealCompute.ofRat (integralKernel x)) := by
  have hx : inDomainInterval function.lower function.upper x := by
    change 0≤x ∧ x≤1; grind
  have h := SecantFoundation.derivative_valid_and_equiv hasDerivative
    (fun n => by change 0<8*(n+1); omega) x radius hr hr1 hx hl hu
    (fun _ => 0) (fun n => by
      rw [SecantFoundation.value_compute kernelFunction x hx]
      change integralKernel x-integralKernel x≤0; grind)
    (fun eps => ⟨0,fun _ _ => Rat.le_of_lt eps.property⟩)
  refine ⟨h.1,?_⟩
  intro n
  have hh := h.2 n
  unfold RealCompute.compareAt at hh ⊢
  rw [SecantFoundation.value_compute kernelFunction x hx] at hh
  exact hh

theorem cellBounds : Integral.CellDerivativeBounds kernelFunction (SecantFoundation.value function) :=
  SecantFoundation.cellDerivativeBounds hasDerivative
    (fun n => by change 0<8*(n+1); omega) 1 (fun x hx n => by
      have h := kernel_bounds hx
      change -1≤integralKernel x ∧ integralKernel x≤1
      constructor <;> grind)

theorem tight : Integral.HasTightBounds kernelFunction := by
  apply MonotoneIntegralBounds.tight kernelFunction (by decide +kernel)
    (fun x y hx hy hxy => ?_) 1 (by decide +kernel)
    (fun x hx n => ?_) (fun _ _ => 0) (fun x hx eps => ?_)
  · intro n m
    rw [SecantFoundation.value_compute kernelFunction y hy,
      SecantFoundation.value_compute kernelFunction x hx]
    exact integralKernel_antitone_nonneg hx.1 hxy
  · rw [SecantFoundation.value_compute kernelFunction x hx]
    have h := kernel_bounds hx
    change 0≤integralKernel x ∧ integralKernel x≤1
    constructor <;> grind
  · rw [SecantFoundation.value_compute kernelFunction x hx]
    change integralKernel x-integralKernel x≤eps.val
    have := eps.property; grind

theorem hasIntegral : Integral.HasIntegral kernelFunction
    (SecantFoundation.value function 1-SecantFoundation.value function 0) :=
  cellBounds.hasIntegral (by decide +kernel) tight

theorem ftc {I : RealCompute} (hI : Integral.HasIntegral kernelFunction I) :
    I.Equiv (SecantFoundation.value function 1-SecantFoundation.value function 0) :=
  hI.ftc cellBounds

end ComputableAnalysis.ArctanSecantFoundation


