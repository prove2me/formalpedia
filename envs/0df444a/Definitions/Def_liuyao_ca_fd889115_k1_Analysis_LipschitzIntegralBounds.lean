-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzIntegralBounds
-- name    : liuyao_ca_fd889115_k1_Analysis_LipschitzIntegralBounds
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:03:21.463601+00:00
-- url     : https://prove2.me/theorems/b2f93640-37e8-48b5-8ac5-d5358612c613
-- title:
--   Computable analysis · LipschitzIntegralBounds · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/LipschitzIntegralBounds.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BoundsQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ConvexFTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealExtension

set_option autoImplicit true

/-! Tight rectangle bounds for a supplied represented sampler with a proved
Lipschitz bound. This is one sufficient construction route, not an integrand
class imposed on the integral specification. -/
namespace ComputableAnalysis.LipschitzIntegralBounds
open ComputableCoefficient RealApproximationOrder Integral
set_option maxHeartbeats 500000

def Lipschitz (f : Rat → Value) (a b L : Rat) : Prop :=
  ∀ u v, a≤u → u≤v → v≤b → Small (sub (f v) (f u)) (L*(v-u))

def onInterval (f : Rat → Value) (a b : Rat) : FunctionOnInterval :=
  ConvexFTC.onInterval (fun q => (f q).real.preferred) a b (fun q _ => (f q).real.valid)

/-- Pad each left sample by a proved bound on the cell's variation. -/
private def partitionRectangles (f : Rat → Value) (a b L : Rat)
    (lip : Lipschitz f a b L) (hL : 0≤L) (P : RationalPartition a b)
    (spacing : Rat) (steps : ∀ k, k < P.pieces → P.point (k+1) - P.point k ≤ spacing)
    (stage : Rat → Nat) : Bounds (onInterval f a b) where
  partition := P
  lower k := ((f (P.point k)).real.compute (stage (P.point k))).lo-L*spacing
  upper k := ((f (P.point k)).real.compute (stage (P.point k))).hi+L*spacing
  lower_le := by
    intro k hk x hx n
    change P.point k≤x ∧ x≤P.point (k+1) at hx
    have hl := (P.point_in_bounds (Nat.le_of_lt hk)).1
    have hh := (P.cell k hk).upper_mem
    have hs := steps k hk
    have hpad : L*(x-P.point k)≤L*spacing :=
      Rat.mul_le_mul_of_nonneg_left (by grind only) hL
    have H := (lip (P.point k) x hl hx.1 (Rat.le_trans hx.2 hh)).mono hpad
    have cover := LipschitzRealExtension.translated_enclosure (f (P.point k)).real.valid (f x).real.valid
      (L*spacing) H (stage (P.point k))
    exact cover.1 0 n
  upper_ge := by
    intro k hk x hx n
    change P.point k≤x ∧ x≤P.point (k+1) at hx
    have hl := (P.point_in_bounds (Nat.le_of_lt hk)).1
    have hh := (P.cell k hk).upper_mem
    have hs := steps k hk
    have hpad : L*(x-P.point k)≤L*spacing :=
      Rat.mul_le_mul_of_nonneg_left (by grind only) hL
    have H := (lip (P.point k) x hl hx.1 (Rat.le_trans hx.2 hh)).mono hpad
    have cover := LipschitzRealExtension.translated_enclosure (f (P.point k)).real.valid (f x).real.valid
      (L*spacing) H (stage (P.point k))
    exact cover.2 n 0

def rectangles (f : Rat → Value) (a b L : Rat) (hab : a≤b)
    (lip : Lipschitz f a b L) (hL : 0≤L) (N : Nat) (hN : 0<N) (stage : Rat → Nat) :
    Bounds (onInterval f a b) :=
  partitionRectangles f a b L lip hL (RationalPartition.uniform a b N hN hab) (mesh a b N)
    (fun k _ => by
      change leftPoint a b N (k+1)-leftPoint a b N k ≤ mesh a b N
      rw [leftPoint_step]
      exact Rat.le_refl) stage

private theorem sum_sub (f g : Nat → Rat) (n : Nat) :
    rectangleSum f n-rectangleSum g n=rectangleSum (fun k => f k-g k) n := by
  induction n with
  | zero => simp only [rectangleSum]; grind only
  | succ n ih => simp only [rectangleSum,←ih]; grind only

private theorem sum_const (c : Rat) (n : Nat) : rectangleSum (fun _ => c) n=(n:Rat)*c := by
  induction n with
  | zero => simp only [rectangleSum]; change (0:Rat)=0*c; rw [Rat.zero_mul]
  | succ n ih => simp only [rectangleSum,ih,Rat.natCast_add]; grind only

theorem rectangles_gap (f : Rat → Value) (a b L : Rat) (hab : a≤b)
    (lip : Lipschitz f a b L) (hL : 0≤L) (N : Nat) (hN : 0<N) (stage : Rat → Nat)
    (tol : Rat) (widths : ∀ q, a≤q → q≤b → ((f q).real.compute (stage q)).width≤tol) :
    (rectangles f a b L hab lip hL N hN stage).upperSum-
      (rectangles f a b L hab lip hL N hN stage).lowerSum≤
      (b-a)*tol+2*L*(b-a)*(b-a)/(N:Rat) := by
  let P := RationalPartition.uniform a b N hN hab
  let h := mesh a b N
  have hp : 0≤h := mesh_nonneg_of_le hN hab
  rw [Bounds.upperSum,Bounds.lowerSum,sum_sub]
  have hs := rectangleSum_mono
    (fun k => (P.point (k+1)-P.point k)*
      (((f (P.point k)).real.compute (stage (P.point k))).hi+L*h)-
      (P.point (k+1)-P.point k)*
      (((f (P.point k)).real.compute (stage (P.point k))).lo-L*h))
    (fun _ => h*(tol+2*L*h)) N (by
      intro k hk
      have hk' : k≤P.pieces := by change k≤N; omega
      have hw := widths (P.point k) (P.point_in_bounds hk').1 (P.point_in_bounds hk').2
      have he := leftPoint_step a b N k
      change P.point (k+1)-P.point k=h at he
      rw [he]
      unfold QInterval.width at hw
      have hh := Rat.mul_le_mul_of_nonneg_left hw hp
      grind only)
  apply Rat.le_trans hs
  rw [sum_const]
  have he := natCast_mul_mesh_eq_sub (a := a) (b := b) hN
  change (N:Rat)*h=b-a at he
  have hh : h=(b-a)/(N:Rat) := by unfold h mesh; rw [if_neg (Nat.ne_of_gt hN)]
  calc
    (N:Rat)*(h*(tol+2*L*h))=((N:Rat)*h)*(tol+2*L*h)  := (Rat.mul_assoc (N:Rat) h (tol+2*L*h)).symm
    _ = (b-a)*(tol+2*L*h) := by rw [he]
    _ = (b-a)*tol+2*L*(b-a)*(b-a)/(N:Rat) := by
      rw [hh]
      simp only [Rat.div_def]
      grind only
    _ ≤ (b-a)*tol+2*L*(b-a)*(b-a)/(N:Rat) := Rat.le_refl

private theorem ratio_budget (E R : Rat) (hE : 0<E) (hR : 0≤R) :
    R*(E/(2*(R+1)))≤E/2 := by
  have hd : 0<2*(R+1) := by grind only
  have hc : (E/(2*(R+1)))*(2*(R+1))=E := Rat.div_mul_cancel (Rat.ne_of_gt hd)
  have htwo : (E/2)*2=E := Rat.div_mul_cancel (by decide +kernel)
  apply Rat.le_of_mul_le_mul_right (c := 2*(R+1)) _ hd
  rw [Rat.mul_assoc,hc,←Rat.mul_assoc,htwo]
  grind only

def bounds (f : Rat → Value) (a b L : Rat) (hab : a≤b)
    (lip : Lipschitz f a b L) (hL : 0≤L) (eps : QPos) : Bounds (onInterval f a b) :=
  let len := b-a
  let halfE : QPos := ⟨eps.val/2,by have := eps.property; grind only⟩
  let tol : QPos := ⟨eps.val/(2*(len+1)),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by dsimp [len]; grind only))⟩
  let N := RationalMajorant.natRateStage (2*L*len*len) halfE+1
  rectangles f a b L hab lip hL N (by dsimp [N]; omega)
    (fun q => ConvexFTC.WidthSearch.stage (f q).real.preferred (f q).real.valid tol)

theorem bounds_gap (f : Rat → Value) (a b L : Rat) (hab : a≤b)
    (lip : Lipschitz f a b L) (hL : 0≤L) (eps : QPos) :
    (bounds f a b L hab lip hL eps).upperSum-(bounds f a b L hab lip hL eps).lowerSum≤eps.val := by
  let len := b-a
  have hlen : 0≤len := by dsimp [len]; grind only
  let halfE : QPos := ⟨eps.val/2,by have := eps.property; grind only⟩
  let tol : QPos := ⟨eps.val/(2*(len+1)),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind only))⟩
  let N := RationalMajorant.natRateStage (2*L*len*len) halfE+1
  have hN : 0<N := by dsimp [N]; omega
  have hC : 0≤2*L*len*len := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hL) hlen) hlen
  have hm := RationalMajorant.natRateStage_spec_of_le hC halfE (Nat.le_refl (N-1))
  change 2*L*len*len/(N:Rat)≤eps.val/2 at hm
  have ht : len*tol.val≤eps.val/2 := ratio_budget eps.val len eps.property hlen
  have h := rectangles_gap f a b L hab lip hL N hN
    (fun q => ConvexFTC.WidthSearch.stage (f q).real.preferred (f q).real.valid tol) tol.val
    (fun q _ _ => ConvexFTC.WidthSearch.stage_spec (f q).real.preferred (f q).real.valid tol)
  change (bounds f a b L hab lip hL eps).upperSum-(bounds f a b L hab lip hL eps).lowerSum≤
    len*tol.val+2*L*len*len/(N:Rat) at h
  grind only

theorem tight (f : Rat → Value) (a b L : Rat) (hab : a≤b)
    (lip : Lipschitz f a b L) (hL : 0≤L) : HasTightBounds (onInterval f a b) :=
  fun eps => ⟨bounds f a b L hab lip hL eps,bounds_gap f a b L hab lip hL eps⟩

private def dyadicSampleStage (f : Rat → Value) (n : Nat) (q : Rat) : Nat :=
  ConvexFTC.WidthSearch.stage (f q).real.preferred (f q).real.valid
    ⟨BoundsQuadrature.dyadicSpacing n, BoundsQuadrature.dyadicSpacing_pos n⟩

/-- The grid level is independent of the precision of each point evaluation. -/
def dyadicBounds (f : Rat → Value) (a b L : Rat) (hab : a ≤ b)
    (lip : Lipschitz f a b L) (hL : 0 ≤ L) (n : Nat) : Bounds (onInterval f a b) :=
  partitionRectangles f a b L lip hL (BoundsQuadrature.dyadicPartition a b hab n)
    (BoundsQuadrature.dyadicSpacing n)
    (fun k _ => BoundsQuadrature.dyadicPartition_step_le a b hab n k) (dyadicSampleStage f n)

theorem dyadicBounds_gap (f : Rat → Value) (a b L : Rat) (hab : a ≤ b)
    (lip : Lipschitz f a b L) (hL : 0 ≤ L) (n : Nat) :
    (dyadicBounds f a b L hab lip hL n).upperSum -
      (dyadicBounds f a b L hab lip hL n).lowerSum ≤
      ((b-a)*(1+2*L)) * BoundsQuadrature.dyadicSpacing n := by
  let B := dyadicBounds f a b L hab lip hL n
  let d := BoundsQuadrature.dyadicSpacing n
  let P := B.partition
  let w k := P.point (k+1)-P.point k
  change B.upperSum-B.lowerSum ≤ ((b-a)*(1+2*L))*d
  rw [BoundsQuadrature.width_sum]
  have H := rectangleSum_mono (fun k => w k * (B.upper k - B.lower k))
    (fun k => w k * ((1+2*L)*d)) P.pieces (by
      intro k hk
      have hp := P.monotone k (k+1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
      apply Rat.mul_le_mul_of_nonneg_left _ (show 0 ≤ w k by dsimp [w]; grind only)
      let q := P.point k
      let I := (f q).real.compute (dyadicSampleStage f n q)
      have hw : I.width ≤ d := ConvexFTC.WidthSearch.stage_spec
        (f q).real.preferred (f q).real.valid ⟨d, BoundsQuadrature.dyadicSpacing_pos n⟩
      change I.hi-I.lo ≤ d at hw
      change (I.hi+L*d)-(I.lo-L*d) ≤ (1+2*L)*d
      grind only)
  rw [rectangleSum_scale, show rectangleSum w P.pieces = b-a from by
    dsimp only [w]
    rw [rectangleSum_telescope, P.right_endpoint, P.left_endpoint]
    rfl] at H
  exact Rat.le_trans H (by grind only)

def dyadicData (f : Rat → Value) (a b L : Rat) (hab : a ≤ b)
    (lip : Lipschitz f a b L) (hL : 0 ≤ L) : BoundsQuadrature.DyadicData (onInterval f a b) where
  ordered := hab
  tests := dyadicBounds f a b L hab lip hL
  onGrid _ := rfl
  shrinks := by
    intro eps
    let C := (b-a)*(1+2*L)
    have hC : 0 ≤ C := Rat.mul_nonneg (by grind only) (by grind only)
    refine ⟨RationalMajorant.halfDecayShift C eps, fun n hn => ?_⟩
    exact Rat.le_trans (dyadicBounds_gap f a b L hab lip hL n)
      (RationalMajorant.halfDecayShift_spec_of_le hC eps hn)

end ComputableAnalysis.LipschitzIntegralBounds


