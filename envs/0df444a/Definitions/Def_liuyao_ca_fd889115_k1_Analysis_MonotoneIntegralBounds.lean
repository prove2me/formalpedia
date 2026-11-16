-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneIntegralBounds
-- name    : liuyao_ca_fd889115_k1_Analysis_MonotoneIntegralBounds
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:16.196209+00:00
-- url     : https://prove2.me/theorems/6a968138-b6f5-4ddd-922e-6d513d0abb40
-- title:
--   Computable analysis · MonotoneIntegralBounds · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/MonotoneIntegralBounds.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_SecantFoundation

set_option autoImplicit true

/-! Concrete endpoint rectangles for a nonnegative decreasing rational-input
computation. The finite bounds do not assume an integral or an endpoint law. -/
namespace ComputableAnalysis.MonotoneIntegralBounds
open Integral SecantFoundation
set_option maxHeartbeats 2000000

private theorem sum_sub (f g : Nat → Rat) (n : Nat) :
    rectangleSum f n-rectangleSum g n = rectangleSum (fun k => f k-g k) n := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum,←ih]; grind

private theorem sum_add (f g : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => f k+g k) n = rectangleSum f n+rectangleSum g n := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum,ih]; grind

private theorem sum_const (c : Rat) (n : Nat) : rectangleSum (fun _ => c) n = (n:Rat)*c := by
  induction n with
  | zero => simp only [rectangleSum]; change (0:Rat)=0*c; rw [Rat.zero_mul]
  | succ n ih => simp only [rectangleSum,ih,Rat.natCast_add]; grind

def partitionEndpointBounds (F : FunctionOnInterval)
    (mono : ∀ x y, inDomainInterval F.lower F.upper x →
      inDomainInterval F.lower F.upper y → x ≤ y → (value F y).Le (value F x))
    (P : RationalPartition F.lower F.upper) (stage : Rat → Nat) : Bounds F where
  partition := P
  lower k := ((value F (P.point (k+1))).compute
    (stage (P.point (k+1)))).lo
  upper k := ((value F (P.point k)).compute
    (stage (P.point k))).hi
  lower_le := by
    intro k hk x hx n
    have hd := (P.cell k hk).contains_inDomain hx
    have hy := P.point_in_bounds (Nat.succ_le_of_lt hk)
    have h := mono x (P.point (k+1)) hd hy hx.2
      (stage (P.point (k+1))) n
    simpa only [value_compute F x hd] using h
  upper_ge := by
    intro k hk x hx n
    have hd := (P.cell k hk).contains_inDomain hx
    have hy := P.point_in_bounds (Nat.le_of_lt hk)
    have h := mono (P.point k) x hy hd hx.1 n (stage (P.point k))
    simpa only [value_compute F x hd] using h

def endpointBounds (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (mono : ∀ x y, inDomainInterval F.lower F.upper x →
      inDomainInterval F.lower F.upper y → x ≤ y → (value F y).Le (value F x))
    (pieces : Nat) (hp : 0 < pieces) (stage : Rat → Nat) : Bounds F :=
  partitionEndpointBounds F mono (RationalPartition.uniform F.lower F.upper pieces hp hab) stage

theorem endpointBounds_gap (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (mono : ∀ x y, inDomainInterval F.lower F.upper x →
      inDomainInterval F.lower F.upper y → x ≤ y → (value F y).Le (value F x))
    (pieces : Nat) (hp : 0 < pieces) (stage : Rat → Nat) (tol bound : Rat)
    (htol : 0 ≤ tol)
    (hwidth : ∀ x (hx : inDomainInterval F.lower F.upper x),
      ((value F x).compute (stage x)).width ≤ tol)
    (hbound : ∀ x (hx : inDomainInterval F.lower F.upper x) n,
      0 ≤ ((value F x).compute n).lo ∧ ((value F x).compute n).hi ≤ bound) :
    (endpointBounds F hab mono pieces hp stage).upperSum-
      (endpointBounds F hab mono pieces hp stage).lowerSum ≤
        (F.upper-F.lower)/(pieces:Rat)*bound+(F.upper-F.lower)*tol := by
  let P := RationalPartition.uniform F.lower F.upper pieces hp hab
  let step := (F.upper-F.lower)/(pieces:Rat)
  let hi k := ((value F (P.point k)).compute (stage (P.point k))).hi
  let lo k := ((value F (P.point k)).compute (stage (P.point k))).lo
  have hs : 0 ≤ step := by
    dsimp [step]; rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast hp)))
  have hmesh : mesh F.lower F.upper pieces = step := by
    simp only [mesh,if_neg (Nat.ne_of_gt hp)]; rfl
  have hgap : (endpointBounds F hab mono pieces hp stage).upperSum-
      (endpointBounds F hab mono pieces hp stage).lowerSum =
      rectangleSum (fun k => step*(hi k-lo (k+1))) pieces := by
    rw [Bounds.upperSum,Bounds.lowerSum,sum_sub]
    apply congrArg (fun f => rectangleSum f pieces)
    funext k
    change (P.point (k+1)-P.point k)*hi k-(P.point (k+1)-P.point k)*lo (k+1) = _
    have he := leftPoint_step F.lower F.upper pieces k
    change P.point (k+1)-P.point k = mesh F.lower F.upper pieces at he
    rw [he,hmesh]; grind
  have hm := rectangleSum_mono (fun k => step*(hi k-lo (k+1)))
    (fun k => step*((hi k-hi (k+1))+tol)) pieces (by
      intro k hk
      have hw := hwidth (P.point (k+1)) (P.point_in_bounds (Nat.succ_le_of_lt hk))
      change hi (k+1)-lo (k+1) ≤ tol at hw
      exact Rat.mul_le_mul_of_nonneg_left (by grind) hs)
  have hsum : rectangleSum (fun k => step*((hi k-hi (k+1))+tol)) pieces =
      step*(hi 0-hi pieces+(pieces:Rat)*tol) := by
    have hscale := rectangleSum_scale (fun k => (hi k-hi (k+1))+tol) step pieces
    have htel := rectangleSum_telescope hi pieces
    have hneg : rectangleSum (fun k => hi k-hi (k+1)) pieces = hi 0-hi pieces := by
      have h := sum_sub (fun _ => 0) (fun k => hi (k+1)-hi k) pieces
      rw [htel] at h
      have hz : rectangleSum (fun _ => (0:Rat)) pieces = 0 := by rw [sum_const,Rat.mul_zero]
      rw [hz] at h
      have he : (fun k => 0-(hi (k+1)-hi k)) = (fun k => hi k-hi (k+1)) := by funext k; grind
      rw [he] at h
      grind
    have hadd := sum_add (fun k => hi k-hi (k+1)) (fun _ => tol) pieces
    rw [hneg,sum_const] at hadd
    have he : (fun k => step*((hi k-hi (k+1))+tol)) =
      (fun k => ((hi k-hi (k+1))+tol)*step) := by funext k; exact Rat.mul_comm _ _
    rw [he,hscale,hadd,Rat.mul_comm]
  have h0 := hbound (P.point 0) (P.point_in_bounds (Nat.zero_le pieces)) (stage (P.point 0))
  have hN := hbound (P.point pieces) (P.point_in_bounds (Nat.le_refl pieces)) (stage (P.point pieces))
  have ho := RealCompute.interval_order_of_valid (value F (P.point pieces)) (value_valid F _) (stage (P.point pieces))
  have hend : hi 0-hi pieces ≤ bound := by dsimp [hi] at *; grind
  have hb := Rat.mul_le_mul_of_nonneg_left hend hs
  have hc := Rat.inv_mul_cancel (pieces:Rat) (by exact_mod_cast Nat.ne_of_gt hp)
  rw [hgap]
  rw [hsum] at hm
  dsimp [step] at *
  grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

/-- The shrinking rectangle gap is established by telescoping the endpoint
ranges. The width selector is the concrete evaluator's own algorithm. -/
theorem tight (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (mono : ∀ x y, inDomainInterval F.lower F.upper x →
      inDomainInterval F.lower F.upper y → x ≤ y → (value F y).Le (value F x))
    (bound : Rat) (hb : 0 ≤ bound)
    (hbound : ∀ x (hx : inDomainInterval F.lower F.upper x) n,
      0 ≤ ((value F x).compute n).lo ∧ ((value F x).compute n).hi ≤ bound)
    (widthStage : Rat → QPos → Nat)
    (hwidth : ∀ x (hx : inDomainInterval F.lower F.upper x) eps,
      ((value F x).compute (widthStage x eps)).width ≤ eps.val) : HasTightBounds F := by
  intro eps
  let len := F.upper-F.lower
  have hl : 0 ≤ len := by dsimp [len]; grind
  let halfE : QPos := ⟨eps.val/2,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let tol : QPos := ⟨eps.val/(2*(len+1)),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))⟩
  let pieces := RationalMajorant.natRateStage (len*bound) halfE+1
  have hp : 0<pieces := by dsimp [pieces]; omega
  let B := endpointBounds F hab mono pieces hp (fun x => widthStage x tol)
  refine ⟨B,?_⟩
  have hgap := endpointBounds_gap F hab mono pieces hp (fun x => widthStage x tol)
    tol.val bound (Rat.le_of_lt tol.property) (fun x hx => hwidth x hx tol) hbound
  have hmain := RationalMajorant.natRateStage_spec_of_le (Rat.mul_nonneg hl hb)
    halfE (Nat.le_refl (pieces-1))
  change len*bound/(pieces:Rat) ≤ eps.val/2 at hmain
  have ht : len*tol.val ≤ eps.val/2 := by
    have hd : 0 < 2*(len+1) := by grind
    have hc := Rat.mul_inv_cancel (2*(len+1)) (Rat.ne_of_gt hd)
    have he := Rat.mul_le_mul_of_nonneg_left
      (show 2*len ≤ 2*(len+1) by grind) (Rat.le_of_lt eps.property)
    apply Rat.le_of_mul_le_mul_right (c:=2*(len+1)) _ hd
    dsimp [tol]
    simp only [Rat.div_def]
    grind [Rat.mul_assoc,Rat.mul_comm]
  dsimp [B] at hgap ⊢
  change _ ≤ len/(pieces:Rat)*bound+len*tol.val at hgap
  have heq : len/(pieces:Rat)*bound = len*bound/(pieces:Rat) := by
    simp only [Rat.div_def]; grind
  rw [heq] at hgap
  grind

end ComputableAnalysis.MonotoneIntegralBounds


