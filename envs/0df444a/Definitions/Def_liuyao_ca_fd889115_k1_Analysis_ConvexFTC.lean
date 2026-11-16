-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ConvexFTC
-- name    : liuyao_ca_fd889115_k1_Analysis_ConvexFTC
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:00:48.940576+00:00
-- url     : https://prove2.me/theorems/77f39a41-40a4-42a3-97cd-ade335ba8e30
-- title:
--   Computable analysis · ConvexFTC · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ConvexFTC.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneIntegralBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotonicityConvexity
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealSecantDerivative

set_option autoImplicit true

/-!
# FTC from constructed convex or concave secants

Order bounds and shrinking evidence have separate roles. The derivative is
the actual outer-secant computation, identified by the covered derivative
bridge. Signed monotone endpoint rectangles supply tight integral bounds;
finite telescoping certifies the endpoint difference without assuming FTC.
This is a sufficient construction route, not a universal integral definition.
-/
namespace ComputableAnalysis.ConvexFTC
open Integral SecantFoundation BracketDerivative
set_option maxHeartbeats 4000000

namespace WidthSearch

private noncomputable def cutoff (x : RealCompute) (hx : x.Valid) (eps : QPos) : Nat :=
  Classical.choose (hx.2.2 eps)

private theorem cutoff_spec (x : RealCompute) (hx : x.Valid) (eps : QPos) :
    ∀ n, cutoff x hx eps ≤ n → (x.compute n).width ≤ eps.val :=
  Classical.choose_spec (hx.2.2 eps)

/-- Executable rational search. The existential validity bound occurs only
in the erased termination proof, not in the runtime computation. -/
def searchFrom (x : RealCompute) (hx : x.Valid) (eps : QPos) (n : Nat) : Nat :=
  if (x.compute n).width ≤ eps.val then n else searchFrom x hx eps (n+1)
termination_by cutoff x hx eps - n
decreasing_by
  have hn : n < cutoff x hx eps := by
    by_cases h : n < cutoff x hx eps
    · exact h
    · have := cutoff_spec x hx eps n (by omega)
      contradiction
  omega

theorem from_spec (x : RealCompute) (hx : x.Valid) (eps : QPos) (n : Nat) :
    n ≤ searchFrom x hx eps n ∧ (x.compute (searchFrom x hx eps n)).width ≤ eps.val := by
  rw [searchFrom]
  split
  · exact ⟨Nat.le_refl _, ‹_›⟩
  · have h := from_spec x hx eps (n+1)
    exact ⟨by omega, h.2⟩
termination_by cutoff x hx eps - n
decreasing_by
  have hn : n < cutoff x hx eps := by
    by_cases h : n < cutoff x hx eps
    · exact h
    · have := cutoff_spec x hx eps n (by omega)
      contradiction
  omega

def stage (x : RealCompute) (hx : x.Valid) (eps : QPos) : Nat := searchFrom x hx eps 0

theorem stage_spec (x : RealCompute) (hx : x.Valid) (eps : QPos) :
    (x.compute (stage x hx eps)).width ≤ eps.val := (from_spec x hx eps 0).2

end WidthSearch

/-- Exact value order; no sign restriction on the monotone function. -/
def Monotone (F : FunctionOnInterval) (increasing : Bool) : Prop :=
  ∀ x y, inDomainInterval F.lower F.upper x →
    inDomainInterval F.lower F.upper y → x ≤ y →
    if increasing then (value F x).Le (value F y) else (value F y).Le (value F x)

def rectangles (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (increasing : Bool) (mono : Monotone F increasing)
    (N : Nat) (hN : 0 < N) (stage : Rat → Nat) : Bounds F where
  partition := RationalPartition.uniform F.lower F.upper N hN hab
  lower j :=
    let P := RationalPartition.uniform F.lower F.upper N hN hab
    ((value F (P.point (if increasing then j else j+1))).compute
      (stage (P.point (if increasing then j else j+1)))).lo
  upper j :=
    let P := RationalPartition.uniform F.lower F.upper N hN hab
    ((value F (P.point (if increasing then j+1 else j))).compute
      (stage (P.point (if increasing then j+1 else j)))).hi
  lower_le := by
    intro j hj x hx n
    let P := RationalPartition.uniform F.lower F.upper N hN hab
    have hxD := (P.cell j hj).contains_inDomain hx
    cases increasing
    · have h := mono x (P.point (j+1)) hxD
        (P.point_in_bounds (Nat.succ_le_of_lt hj)) hx.2
      simpa only [Bool.false_eq_true, ↓reduceIte, value_compute F x hxD] using
        h (stage (P.point (j+1))) n
    · have h := mono (P.point j) x (P.point_in_bounds (Nat.le_of_lt hj)) hxD hx.1
      simpa only [↓reduceIte, value_compute F x hxD] using h (stage (P.point j)) n
  upper_ge := by
    intro j hj x hx n
    let P := RationalPartition.uniform F.lower F.upper N hN hab
    have hxD := (P.cell j hj).contains_inDomain hx
    cases increasing
    · have h := mono (P.point j) x (P.point_in_bounds (Nat.le_of_lt hj)) hxD hx.1
      simpa only [Bool.false_eq_true, ↓reduceIte, value_compute F x hxD] using h n (stage (P.point j))
    · have h := mono x (P.point (j+1)) hxD
        (P.point_in_bounds (Nat.succ_le_of_lt hj)) hx.2
      simpa only [↓reduceIte, value_compute F x hxD] using h n (stage (P.point (j+1)))

private theorem sum_sub (f g : Nat → Rat) (n : Nat) :
    rectangleSum f n-rectangleSum g n = rectangleSum (fun k => f k-g k) n := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum, ←ih]; grind

private theorem sum_add (f g : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => f k+g k) n = rectangleSum f n+rectangleSum g n := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum, ih]; grind

private theorem sum_const (c : Rat) (n : Nat) :
    rectangleSum (fun _ => c) n = (n:Rat)*c := by
  induction n with
  | zero => simp only [rectangleSum]; change (0:Rat)=0*c; rw [Rat.zero_mul]
  | succ n ih => simp only [rectangleSum, ih, Rat.natCast_add]; grind

private theorem sum_forward (h : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => h (k+1)-h k) n = h n-h 0 :=
  rectangleSum_telescope h n

private theorem sum_backward (h : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => h k-h (k+1)) n = h 0-h n := by
  have he := sum_sub (fun _ => 0) (fun k => h (k+1)-h k) n
  rw [sum_forward, sum_const, Rat.mul_zero] at he
  have hf : (fun k => 0-(h (k+1)-h k)) = (fun k => h k-h (k+1)) := by
    funext k; grind
  rw [hf] at he
  grind

/-- A sign-independent endpoint budget for all selected evaluator stages. -/
def spread (F : FunctionOnInterval) : Rat :=
  qabs ((value F F.lower).compute 0).lo +
    qabs ((value F F.lower).compute 0).hi +
    qabs ((value F F.upper).compute 0).lo +
    qabs ((value F F.upper).compute 0).hi

theorem spread_nonneg (F : FunctionOnInterval) : 0 ≤ spread F := by
  unfold spread
  have := qabs_nonneg ((value F F.lower).compute 0).lo
  have := qabs_nonneg ((value F F.lower).compute 0).hi
  have := qabs_nonneg ((value F F.upper).compute 0).lo
  have := qabs_nonneg ((value F F.upper).compute 0).hi
  grind

/-- Mesh error and value-evaluation error are controlled separately. -/
theorem rectangles_gap (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) (N : Nat) (hN : 0 < N)
    (stage : Rat → Nat) (tol : Rat)
    (hw : ∀ x, inDomainInterval F.lower F.upper x →
      ((value F x).compute (stage x)).width ≤ tol) :
    (rectangles F hab inc mono N hN stage).upperSum-
      (rectangles F hab inc mono N hN stage).lowerSum ≤
        (F.upper-F.lower)/(N:Rat)*spread F+(F.upper-F.lower)*tol := by
  let P := RationalPartition.uniform F.lower F.upper N hN hab
  let step := (F.upper-F.lower)/(N:Rat)
  let hi k := ((value F (P.point k)).compute (stage (P.point k))).hi
  let lo k := ((value F (P.point k)).compute (stage (P.point k))).lo
  have hs : 0 ≤ step := by
    dsimp [step]; rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast hN)))
  have hmesh : ∀ k, P.point (k+1)-P.point k = step := by
    intro k
    have he := leftPoint_step F.lower F.upper N k
    change leftPoint F.lower F.upper N (k+1)-leftPoint F.lower F.upper N k = step
    simpa only [step, mesh, if_neg (Nat.ne_of_gt hN)] using he
  have hwidth : ∀ k, k ≤ N → hi k-lo k ≤ tol := by
    intro k hk; exact hw _ (P.point_in_bounds hk)
  have hend : hi N-hi 0 ≤ spread F ∧ hi 0-hi N ≤ spread F := by
    have h0 := RealCompute.le_refl _ (value_valid F F.lower) 0 (stage F.lower)
    have h1 := (value_valid F F.lower).2.1 0 (stage F.lower) (Nat.zero_le _)
    have h2 := RealCompute.le_refl _ (value_valid F F.upper) 0 (stage F.upper)
    have h3 := (value_valid F F.upper).2.1 0 (stage F.upper) (Nat.zero_le _)
    have ha := self_le_qabs ((value F F.lower).compute 0).hi
    have hb := neg_qabs_le_self ((value F F.lower).compute 0).lo
    have hc := self_le_qabs ((value F F.upper).compute 0).hi
    have hd := neg_qabs_le_self ((value F F.upper).compute 0).lo
    have he := qabs_nonneg ((value F F.lower).compute 0).hi
    have hf := qabs_nonneg ((value F F.lower).compute 0).lo
    have hg := qabs_nonneg ((value F F.upper).compute 0).hi
    have hh := qabs_nonneg ((value F F.upper).compute 0).lo
    dsimp [hi, spread]
    have hright : P.point N = F.upper := P.right_endpoint
    rw [P.left_endpoint, hright]
    constructor <;> grind
  have hcancel : step*(N:Rat) = F.upper-F.lower := by
    dsimp [step]; rw [Rat.div_def]
    have := Rat.inv_mul_cancel (N:Rat) (by exact_mod_cast Nat.ne_of_gt hN)
    grind [Rat.mul_assoc]
  have hgap : (rectangles F hab inc mono N hN stage).upperSum-
      (rectangles F hab inc mono N hN stage).lowerSum =
      rectangleSum (fun k => step*((if inc then hi (k+1) else hi k)-
        (if inc then lo k else lo (k+1)))) N := by
    rw [Bounds.upperSum, Bounds.lowerSum, sum_sub]
    apply congrArg (fun f => rectangleSum f N)
    funext k
    change (P.point (k+1)-P.point k)*_-(P.point (k+1)-P.point k)*_ = _
    rw [hmesh]
    cases inc
    · change step*hi k-step*lo (k+1) = step*(hi k-lo (k+1))
      grind only
    · change step*hi (k+1)-step*lo k = step*(hi (k+1)-lo k)
      grind only
  rw [hgap]
  cases inc
  · have hle := rectangleSum_mono
      (fun k => step*(hi k-lo (k+1)))
      (fun k => step*((hi k-hi (k+1))+tol)) N (by
        intro k hk
        exact Rat.mul_le_mul_of_nonneg_left (by have := hwidth (k+1) (by omega); grind) hs)
    have heq : rectangleSum (fun k => step*((hi k-hi (k+1))+tol)) N =
        step*(hi 0-hi N)+(F.upper-F.lower)*tol := by
      have he := rectangleSum_scale (fun k => (hi k-hi (k+1))+tol) step N
      have hf : (fun k => step*((hi k-hi (k+1))+tol)) =
          (fun k => ((hi k-hi (k+1))+tol)*step) := by funext k; grind
      rw [hf, he, sum_add, sum_backward, sum_const]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
    rw [heq] at hle
    have := Rat.mul_le_mul_of_nonneg_left hend.2 hs
    simpa only [Bool.false_eq_true, step, ↓reduceIte] using (by grind :
      rectangleSum (fun k => step*(hi k-lo (k+1))) N ≤ step*spread F+(F.upper-F.lower)*tol)
  · have hle := rectangleSum_mono
      (fun k => step*(hi (k+1)-lo k))
      (fun k => step*((hi (k+1)-hi k)+tol)) N (by
        intro k hk
        exact Rat.mul_le_mul_of_nonneg_left (by have := hwidth k (by omega); grind) hs)
    have heq : rectangleSum (fun k => step*((hi (k+1)-hi k)+tol)) N =
        step*(hi N-hi 0)+(F.upper-F.lower)*tol := by
      have he := rectangleSum_scale (fun k => (hi (k+1)-hi k)+tol) step N
      have hf : (fun k => step*((hi (k+1)-hi k)+tol)) =
          (fun k => ((hi (k+1)-hi k)+tol)*step) := by funext k; grind
      rw [hf, he, sum_add, sum_forward, sum_const]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
    rw [heq] at hle
    have := Rat.mul_le_mul_of_nonneg_left hend.1 hs
    simpa only [Bool.false_eq_true, step, ↓reduceIte] using (by grind :
      rectangleSum (fun k => step*(hi (k+1)-lo k)) N ≤ step*spread F+(F.upper-F.lower)*tol)

/-- Finite endpoint rectangles at a requested rational tolerance. The mesh
and all evaluator stages are chosen internally by executable arithmetic/search. -/
def boundsAtTolerance (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) (eps : QPos) : Bounds F :=
  let len := F.upper-F.lower
  let halfE : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let tol : QPos := ⟨eps.val/(2*(len+1)), by
    have hl : 0 ≤ len := by dsimp [len]; grind
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))⟩
  let N := RationalMajorant.natRateStage (len*spread F) halfE+1
  rectangles F hab inc mono N (by dsimp [N]; omega)
    (fun x => WidthSearch.stage (value F x) (value_valid F x) tol)

/-- Construct tight signed monotone rectangles. Sampling precision is searched
internally, independently of the spatial mesh. No integral is assumed. -/
theorem boundsAtTolerance_gap (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) (eps : QPos) :
    (boundsAtTolerance F hab inc mono eps).upperSum-
      (boundsAtTolerance F hab inc mono eps).lowerSum ≤ eps.val := by
  let len := F.upper-F.lower
  have hl : 0 ≤ len := by dsimp [len]; grind
  let halfE : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let tol : QPos := ⟨eps.val/(2*(len+1)), by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))⟩
  let N := RationalMajorant.natRateStage (len*spread F) halfE+1
  have hN : 0 < N := by dsimp [N]; omega
  let s := fun x => WidthSearch.stage (value F x) (value_valid F x) tol
  let B := rectangles F hab inc mono N hN s
  change B.upperSum-B.lowerSum ≤ eps.val
  have hgap := rectangles_gap F hab inc mono N hN s tol.val
    (fun x _ => WidthSearch.stage_spec (value F x) (value_valid F x) tol)
  have hm := RationalMajorant.natRateStage_spec_of_le
    (Rat.mul_nonneg hl (spread_nonneg F)) halfE (Nat.le_refl (N-1))
  change len*spread F/(N:Rat) ≤ eps.val/2 at hm
  have ht : len*tol.val ≤ eps.val/2 := by
    have hd : 0 < 2*(len+1) := by grind
    have hc := Rat.mul_inv_cancel (2*(len+1)) (Rat.ne_of_gt hd)
    have he := Rat.mul_le_mul_of_nonneg_left
      (show 2*len ≤ 2*(len+1) by grind) (Rat.le_of_lt eps.property)
    apply Rat.le_of_mul_le_mul_right (c:=2*(len+1)) _ hd
    dsimp [tol]
    simp only [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  change _ ≤ eps.val
  change B.upperSum-B.lowerSum ≤ len/(N:Rat)*spread F+len*tol.val at hgap
  have he : len/(N:Rat)*spread F = len*spread F/(N:Rat) := by
    simp only [Rat.div_def]; grind
  rw [he] at hgap
  grind

theorem tight (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) : HasTightBounds F :=
  fun eps => ⟨boundsAtTolerance F hab inc mono eps, boundsAtTolerance_gap F hab inc mono eps⟩

def onInterval (d : Rat → RealCompute) (a b : Rat)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid) : FunctionOnInterval where
  raw := { definedAt := inDomainInterval a b, compute := fun x _ => (d x).compute }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := fun x hx => hd x hx

theorem value_onInterval (d : Rat → RealCompute) (a b : Rat)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid)
    {x : Rat} (hx : inDomainInterval a b x) (n : Nat) :
    (value (onInterval d a b hd) x).compute n = (d x).compute n := by
  rw [value_compute _ _ hx]
  rfl

/-- Supporting slopes for a convex function, or the reversed inequalities for
a concave function. This contains no integral or endpoint-integral identity. -/
def Supports (f d : Rat → RealCompute) (a b : Rat) (inc : Bool) : Prop :=
  ∀ u v, inDomainInterval a b u → inDomainInterval a b v → u < v →
    if inc then (d u).Le (secant f u v) ∧ (secant f u v).Le (d v)
    else (d v).Le (secant f u v) ∧ (secant f u v).Le (d u)

theorem supports_monotone {f d : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (hf : ∀ x, inDomainInterval a b x → (f x).Valid)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid)
    (hs : Supports f d a b inc) : Monotone (onInterval d a b hd) inc := by
  intro x y hx hy hxy
  by_cases he : x = y
  · subst y
    cases inc <;> intro i j <;>
      simpa only [value_onInterval d a b hd hx] using RealCompute.le_refl _ (hd x hx) i j
  · have hlt : x < y := by grind
    have h := hs x y hx hy hlt
    have hv := BracketDerivative.secant_valid (hf x hx) (hf y hy)
    cases inc
    · have hle := RealCompute.le_trans hv h.1 h.2
      intro i j
      simpa only [value_onInterval d a b hd hy, value_onInterval d a b hd hx] using hle i j
    · have hle := RealCompute.le_trans hv h.1 h.2
      intro i j
      simpa only [value_onInterval d a b hd hy, value_onInterval d a b hd hx] using hle i j

/-- Multiplying a secant inequality back by the positive cell length. -/
private theorem lower_increment {f : Rat → RealCompute} {u v l : Rat}
    (huv : u < v) (h : (RealCompute.ofRat l).Le (secant f u v)) :
    (RealCompute.ofRat ((v-u)*l)).Le (f v-f u) := by
  intro _ n
  have hvu : 0 < v-u := by grind
  have hrec : 0 ≤ 1/(v-u) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hvu)
  have hh := h 0 n
  change l ≤ ((RealCompute.scaleRat (1/(v-u)) (f v-f u)).compute n).hi at hh
  simp only [RealCompute.scaleRat, RealCompute.scaleRatCompute, if_pos hrec] at hh
  change (v-u)*l ≤ ((f v-f u).compute n).hi
  have hm := Rat.mul_le_mul_of_nonneg_left hh (Rat.le_of_lt hvu)
  have hc := Rat.mul_inv_cancel (v-u) (Rat.ne_of_gt hvu)
  simp only [Rat.div_def, Rat.one_mul] at hm
  rw [← Rat.mul_assoc, hc, Rat.one_mul] at hm
  exact hm

private theorem upper_increment {f : Rat → RealCompute} {u v r : Rat}
    (huv : u < v) (h : (secant f u v).Le (RealCompute.ofRat r)) :
    (f v-f u).Le (RealCompute.ofRat ((v-u)*r)) := by
  intro n _
  have hvu : 0 < v-u := by grind
  have hrec : 0 ≤ 1/(v-u) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hvu)
  have hh := h n 0
  change ((RealCompute.scaleRat (1/(v-u)) (f v-f u)).compute n).lo ≤ r at hh
  simp only [RealCompute.scaleRat, RealCompute.scaleRatCompute, if_pos hrec] at hh
  change ((f v-f u).compute n).lo ≤ (v-u)*r
  have hm := Rat.mul_le_mul_of_nonneg_left hh (Rat.le_of_lt hvu)
  have hc := Rat.mul_inv_cancel (v-u) (Rat.ne_of_gt hvu)
  simp only [Rat.div_def, Rat.one_mul] at hm
  rw [← Rat.mul_assoc, hc, Rat.one_mul] at hm
  exact hm

theorem supports_cellBounds {f d : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (hf : ∀ x, inDomainInterval a b x → (f x).Valid)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid)
    (hs : Supports f d a b inc) : CellDerivativeBounds (onInterval d a b hd) f := by
  refine ⟨hf, ?_, ?_⟩
  · intro u v l hu huv hv hl
    change a ≤ u at hu
    change v ≤ b at hv
    have huD : inDomainInterval a b u := ⟨hu, by grind⟩
    have hvD : inDomainInterval a b v := ⟨by grind, hv⟩
    by_cases he : u = v
    · subst v
      intro _ n
      have ho := (hf u huD).1 n
      change (u-u)*l ≤ ((f u).compute n).hi - ((f u).compute n).lo
      grind [QInterval.width]
    · have hlt : u < v := by grind
      have h := hs u v huD hvD hlt
      apply lower_increment hlt
      cases inc
      · have hb : (RealCompute.ofRat l).Le (d v) := fun _ n => hl v hvD huv Rat.le_refl n
        exact RealCompute.le_trans (hd v hvD) hb h.1
      · have hb : (RealCompute.ofRat l).Le (d u) := fun _ n => hl u huD Rat.le_refl huv n
        exact RealCompute.le_trans (hd u huD) hb h.1
  · intro u v r hu huv hv hr
    change a ≤ u at hu
    change v ≤ b at hv
    have huD : inDomainInterval a b u := ⟨hu, by grind⟩
    have hvD : inDomainInterval a b v := ⟨by grind, hv⟩
    by_cases he : u = v
    · subst v
      intro n _
      have ho := (hf u huD).1 n
      change ((f u).compute n).lo - ((f u).compute n).hi ≤ (u-u)*r
      grind [QInterval.width]
    · have hlt : u < v := by grind
      have h := hs u v huD hvD hlt
      apply upper_increment hlt
      cases inc
      · have hb : (d u).Le (RealCompute.ofRat r) := fun n _ => hr u huD Rat.le_refl huv n
        exact RealCompute.le_trans (hd u huD) h.2 hb
      · have hb : (d v).Le (RealCompute.ofRat r) := fun n _ => hr v hvD huv Rat.le_refl n
        exact RealCompute.le_trans (hd v hvD) h.2 hb

/-- Existence and FTC: the executable endpoint difference is certified as the
integral, using derived monotone rectangle bounds and finite secant order. -/
theorem hasIntegral_of_supports {f d : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (hab : a ≤ b) (hf : ∀ x, inDomainInterval a b x → (f x).Valid)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid)
    (hs : Supports f d a b inc) : HasIntegral (onInterval d a b hd) (f b-f a) :=
  (supports_cellBounds hf hd hs).hasIntegral hab
    (tight _ hab inc (supports_monotone hf hd hs))

theorem ftc_of_supports {f d : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (hab : a ≤ b) (hf : ∀ x, inDomainInterval a b x → (f x).Valid)
    (hd : ∀ x, inDomainInterval a b x → (d x).Valid)
    (hs : Supports f d a b inc) {I : RealCompute}
    (hI : HasIntegral (onInterval d a b hd) I) : I.Equiv (f b-f a) :=
  hI.unique (hasIntegral_of_supports hab hf hd hs)

/-- Ordered disjoint secants: convex when `inc = true`, concave otherwise.
This is a value-level law for the primary rational-input computation. -/
def Curved (domain : Rat → Prop) (f : Rat → RealCompute) (inc : Bool) : Prop :=
  ∀ w u v r, domain w → domain u → domain v → domain r →
    w < u → u ≤ v → v < r →
    if inc then (secant f w u).Le (secant f v r)
    else (secant f v r).Le (secant f w u)

/-- Function-specific finite proof data for the actual derivative algorithm.
The fields concern rational sampling, coverage, and shrinking validity;
no derivative identity or integral agreement is assumed. -/
structure OuterSecants (domain : Rat → Prop) (f : Rat → RealCompute) (x : RealCompute) where
  left : Nat → Rat
  innerLeft : Nat → Rat
  innerRight : Nat → Rat
  right : Nat → Rat
  precision : Nat → Nat
  valid : (outerDerivative f left innerLeft innerRight right precision).Valid
  points : ∀ n, domain (left n) ∧ domain (innerLeft n) ∧
    domain (innerRight n) ∧ domain (right n)
  brackets : ∃ A, Admissible domain x A
  neighborhood : ∀ n, left n < innerLeft n ∧ innerRight n < right n ∧
    ∃ k, innerLeft n < (x.compute k).lo ∧ (x.compute k).hi < innerRight n

namespace OuterSecants

def raw {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) : RealCompute :=
  outerDerivative f C.left C.innerLeft C.innerRight C.right C.precision

theorem raw_valid {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) : C.raw.Valid := C.valid

theorem point_valid {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) : x.Valid := by
  obtain ⟨A, hA⟩ := C.brackets
  exact hA.1

/-- The same constructed derivative is identified at every valid represented
input for which the local construction is supplied, including irrational ones. -/
theorem hasDerivative {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    {inc : Bool} (C : OuterSecants domain f x)
    (hf : ∀ q, domain q → (f q).Valid) (hc : Curved domain f inc) :
    RealSecantDerivative.HasDerivativeAt domain f x C.raw := by
  cases inc
  · exact RealSecantDerivative.concave_outerDerivative_hasDerivative
      C.left C.innerLeft C.innerRight C.right C.precision C.point_valid hf
      C.brackets C.valid C.points (fun w u v r hw hu hv hr hwu huv hvr =>
        hc w u v r hw hu hv hr hwu huv hvr) C.neighborhood
  · exact RealSecantDerivative.outerDerivative_hasDerivative
      C.left C.innerLeft C.innerRight C.right C.precision C.point_valid hf
      C.brackets C.valid C.points (fun w u v r hw hu hv hr hwu huv hvr =>
        hc w u v r hw hu hv hr hwu huv hvr) C.neighborhood

/-- Different enclosures, precisions, and equivalent input names determine
the same derivative value. -/
theorem equiv {domain : Rat → Prop} {f : Rat → RealCompute} {x y : RealCompute}
    {inc : Bool} (C : OuterSecants domain f x) (E : OuterSecants domain f y)
    (hf : ∀ q, domain q → (f q).Valid) (hc : Curved domain f inc)
    (hxy : x.Equiv y) : C.raw.Equiv E.raw :=
  RealSecantDerivative.unique
    (RealSecantDerivative.congr_point (C.hasDerivative hf hc) E.point_valid hxy)
    (E.hasDerivative hf hc)

/-- Convexity/concavity turns the actual outer-secant computation into the
finite supporting-slope inequalities needed by FTC. -/
theorem supports_pair {domain : Rat → Prop} {f : Rat → RealCompute}
    {u v : Rat} {inc : Bool}
    (C : OuterSecants domain f (RealCompute.ofRat u))
    (E : OuterSecants domain f (RealCompute.ofRat v))
    (hc : Curved domain f inc) (hu : domain u) (hv : domain v) (huv : u < v) :
    if inc then C.raw.Le (secant f u v) ∧ (secant f u v).Le E.raw
    else E.raw.Le (secant f u v) ∧ (secant f u v).Le C.raw := by
  cases inc
  · constructor
    · intro i j
      obtain ⟨hleft, hright, k, huk, hkv⟩ := E.neighborhood i
      change E.innerLeft i < v at huk
      change v < E.innerRight i at hkv
      have ho := hc u v (E.innerRight i) (E.right i) hu hv
        (E.points i).2.2.1 (E.points i).2.2.2 huv (Rat.le_of_lt hkv) hright
        (E.precision i) j
      dsimp [raw, outerDerivative, QInterval.hull]
      grind
    · intro i j
      obtain ⟨hleft, hright, k, huk, hkv⟩ := C.neighborhood j
      change C.innerLeft j < u at huk
      change u < C.innerRight j at hkv
      have ho := hc (C.left j) (C.innerLeft j) u v
        (C.points j).1 (C.points j).2.1 hu hv hleft (Rat.le_of_lt huk) huv
        i (C.precision j)
      dsimp [raw, outerDerivative, QInterval.hull]
      grind
  · constructor
    · intro i j
      obtain ⟨hleft, hright, k, huk, hkv⟩ := C.neighborhood i
      change C.innerLeft i < u at huk
      change u < C.innerRight i at hkv
      have ho := hc (C.left i) (C.innerLeft i) u v
        (C.points i).1 (C.points i).2.1 hu hv hleft (Rat.le_of_lt huk) huv
        (C.precision i) j
      dsimp [raw, outerDerivative, QInterval.hull]
      grind
    · intro i j
      obtain ⟨hleft, hright, k, huk, hkv⟩ := E.neighborhood j
      change E.innerLeft j < v at huk
      change v < E.innerRight j at hkv
      have ho := hc u v (E.innerRight j) (E.right j) hu hv
        (E.points j).2.2.1 (E.points j).2.2.2 huv (Rat.le_of_lt hkv) hright
        i (E.precision j)
      dsimp [raw, outerDerivative, QInterval.hull]
      grind

end OuterSecants

/-- The rational-input derivative algorithm; the domain decision is rational
and executable. Internal secant and value precisions are packaged in `C`. -/
def derivative {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (q : Rat) : RealCompute :=
  if hq : a ≤ q ∧ q ≤ b then (C q hq).raw else RealCompute.ofRat 0

theorem derivative_compute {domain : Rat → Prop} {f : Rat → RealCompute} {a b q : Rat}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hq : inDomainInterval a b q) (n : Nat) :
    ((derivative C q).compute n) = ((C q hq).raw.compute n) := by
  change a ≤ q ∧ q ≤ b at hq
  simp only [derivative, dif_pos hq]

theorem derivative_valid {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (q : Rat) : (derivative C q).Valid := by
  unfold derivative
  split
  · exact (C q ‹_›).raw_valid
  · exact RealCompute.ofRat_valid 0

theorem derivative_hasDerivative {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b q : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hf : ∀ q, domain q → (f q).Valid) (hc : Curved domain f inc)
    (hq : inDomainInterval a b q) :
    RealSecantDerivative.HasDerivativeAt domain f (RealCompute.ofRat q) (derivative C q) := by
  change a ≤ q ∧ q ≤ b at hq
  simpa only [derivative, dif_pos hq] using (C q hq).hasDerivative hf hc

theorem derivative_supports {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    Supports f (derivative C) a b inc := by
  intro u v hu hv huv
  have ho := (C u hu).supports_pair (C v hv) hc (inside u hu) (inside v hv) huv
  cases inc
  · constructor
    · intro i j
      simpa only [derivative_compute C hu, derivative_compute C hv] using ho.1 i j
    · intro i j
      simpa only [derivative_compute C hu, derivative_compute C hv] using ho.2 i j
  · constructor
    · intro i j
      simpa only [derivative_compute C hu, derivative_compute C hv] using ho.1 i j
    · intro i j
      simpa only [derivative_compute C hu, derivative_compute C hv] using ho.2 i j

def derivativeOnInterval {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q)) :
    FunctionOnInterval :=
  onInterval (derivative C) a b (fun q _ => derivative_valid C q)

/-- Constructed convex/concave FTC. The endpoint difference is a valid
executable integral witness, not a conclusion stored in the construction. -/
theorem hasIntegral {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    HasIntegral (derivativeOnInterval C) (f b-f a) :=
  hasIntegral_of_supports hab (fun q hq => hf q (inside q hq))
    (fun q _ => derivative_valid C q) (derivative_supports C inside hc)

/-- Exact FTC for every supplied integral of the computed derivative. -/
theorem ftc {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc)
    {I : RealCompute} (hI : HasIntegral (derivativeOnInterval C) I) : I.Equiv (f b-f a) :=
  hI.unique (hasIntegral C hab hf inside hc)

theorem derivative_monotone {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    Monotone (derivativeOnInterval C) inc :=
  supports_monotone (fun q hq => hf q (inside q hq)) (fun q _ => derivative_valid C q)
    (derivative_supports C inside hc)

/-- Negation commutes with a positively oriented rational secant. -/
theorem neg_secant_compute (f : Rat → RealCompute) {u v : Rat} (huv : u < v) (n : Nat) :
    (secant (fun q => -(f q)) u v).compute n =
      (-(secant f u v)).compute n := by
  have hh : 0 ≤ 1/(v-u) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (by grind))
  change (RealCompute.scaleRat (1/(v-u))
    (RealCompute.sub (RealCompute.neg (f v)) (RealCompute.neg (f u)))).compute n =
    (RealCompute.neg (RealCompute.scaleRat (1/(v-u)) (RealCompute.sub (f v) (f u)))).compute n
  simp only [RealCompute.scaleRat, RealCompute.scaleRatCompute, RealCompute.sub, RealCompute.subCompute,
    RealCompute.neg, RealCompute.negCompute, if_pos hh]
  congr 1 <;> grind only

theorem curved_neg {domain : Rat → Prop} {f : Rat → RealCompute} {inc : Bool}
    (hc : Curved domain f inc) : Curved domain (fun q => -(f q)) (!inc) := by
  intro w u v r hw hu hv hr hwu huv hvr
  have h := hc w u v r hw hu hv hr hwu huv hvr
  cases inc <;> intro i j <;>
    rw [neg_secant_compute f hwu, neg_secant_compute f hvr] <;>
    exact RealCompute.le_neg_le_neg h i j

namespace OuterSecants

private theorem neg_compute {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) (n : Nat) :
    (outerDerivative (fun q => -(f q)) C.left C.innerLeft C.innerRight C.right C.precision).compute n =
      (-C.raw).compute n := by
  have h := C.neighborhood n
  dsimp only [outerDerivative]
  rw [neg_secant_compute f h.1, neg_secant_compute f h.2.1]
  change QInterval.hull
      {lo := -((secant f (C.left n) (C.innerLeft n)).compute (C.precision n)).hi,
       hi := -((secant f (C.left n) (C.innerLeft n)).compute (C.precision n)).lo}
      {lo := -((secant f (C.innerRight n) (C.right n)).compute (C.precision n)).hi,
       hi := -((secant f (C.innerRight n) (C.right n)).compute (C.precision n)).lo} =
    {lo := -(C.raw.compute n).hi, hi := -(C.raw.compute n).lo}
  change QInterval.hull _ _ =
    {lo := -(QInterval.hull _ _).hi, hi := -(QInterval.hull _ _).lo}
  dsimp [QInterval.hull]
  congr 1 <;> grind

/-- The concave mirror preserves the same executable rational sample schedule. -/
def neg {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) : OuterSecants domain (fun q => -(f q)) x where
  left := C.left
  innerLeft := C.innerLeft
  innerRight := C.innerRight
  right := C.right
  precision := C.precision
  valid := by
    have he : (outerDerivative (fun q => -(f q)) C.left C.innerLeft C.innerRight C.right C.precision).compute =
        (-C.raw).compute := funext (neg_compute C)
    change RealCompute.ValidCompute _
    rw [he]
    exact RealCompute.neg_valid C.raw_valid
  points := C.points
  brackets := C.brackets
  neighborhood := C.neighborhood

theorem neg_raw_compute {domain : Rat → Prop} {f : Rat → RealCompute} {x : RealCompute}
    (C : OuterSecants domain f x) (n : Nat) : C.neg.raw.compute n = (-C.raw).compute n :=
  neg_compute C n

end OuterSecants

def quadratureBox (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) (n : Nat) : QInterval :=
  let B := boundsAtTolerance F hab inc mono ⟨allowance n, allowance_pos n⟩
  {lo := B.lowerSum, hi := B.upperSum}

private def intersectPrefix (boxes : Nat → QInterval) : Nat → QInterval
  | 0 => boxes 0
  | n+1 => QInterval.intersection (intersectPrefix boxes n) (boxes (n+1))

/-- Independent endpoint quadrature with finite-prefix nesting repair.
The algorithm never reads an antiderivative endpoint difference. -/
def quadrature (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) : RealCompute where
  compute := intersectPrefix (quadratureBox F hab inc mono)

private theorem prefix_encloses (boxes : Nat → QInterval) (I : RealCompute)
    (h : ∀ n m, (boxes n).lo ≤ (I.compute m).hi ∧
      (I.compute m).lo ≤ (boxes n).hi) (n m : Nat) :
    (intersectPrefix boxes n).lo ≤ (I.compute m).hi ∧
      (I.compute m).lo ≤ (intersectPrefix boxes n).hi := by
  induction n with
  | zero => exact h 0 m
  | succ n ih =>
    have hn := h (n+1) m
    dsimp [intersectPrefix, QInterval.intersection]
    constructor <;> grind

private theorem prefix_current (boxes : Nat → QInterval) (n : Nat) :
    (boxes n).ContainsInterval (intersectPrefix boxes n) := by
  cases n with
  | zero => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n => exact QInterval.intersection_contained_right _ _

/-- Validity uses a justified common value only in the proof. Rectangle
evaluation and nesting repair themselves are independent computations. -/
theorem quadrature_valid (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) {I : RealCompute} (hI : HasIntegral F I) :
    (quadrature F hab inc mono).Valid := by
  let boxes := quadratureBox F hab inc mono
  have hb : ∀ n m, (boxes n).lo ≤ (I.compute m).hi ∧
      (I.compute m).lo ≤ (boxes n).hi := by
    intro n m
    exact hI.bounds (boundsAtTolerance F hab inc mono ⟨allowance n, allowance_pos n⟩) m
  have hp := prefix_encloses boxes I hb
  have ordered (n : Nat) : (intersectPrefix boxes n).lo ≤ (intersectPrefix boxes n).hi := by
    exact RealCompute.le_trans (x := RealCompute.ofRat (intersectPrefix boxes n).lo)
      (z := RealCompute.ofRat (intersectPrefix boxes n).hi) hI.valid
      (fun _ m => (hp n m).1) (fun m _ => (hp n m).2) 0 0
  refine ⟨fun n => by
    change 0 ≤ (intersectPrefix boxes n).hi - (intersectPrefix boxes n).lo
    have := ordered n
    grind only, ?_, ?_⟩
  · intro n m hnm
    change (intersectPrefix boxes n).lo ≤ (intersectPrefix boxes m).lo ∧
      (intersectPrefix boxes m).lo ≤ (intersectPrefix boxes m).hi ∧
      (intersectPrefix boxes m).hi ≤ (intersectPrefix boxes n).hi
    induction hnm with
    | refl => exact ⟨Rat.le_refl, ordered n, Rat.le_refl⟩
    | @step m hnm ih =>
      have hs := QInterval.intersection_contained_left (intersectPrefix boxes m) (boxes (m+1))
      exact ⟨Rat.le_trans ih.1 hs.1, ordered (m+1), Rat.le_trans hs.2 ih.2.2⟩
  · intro eps
    obtain ⟨N, hN⟩ := allowance_shrinks eps
    refine ⟨N, fun n hn => ?_⟩
    have hc := prefix_current boxes n
    have hw := boundsAtTolerance_gap F hab inc mono ⟨allowance n, allowance_pos n⟩
    have ha := hN n hn
    change (intersectPrefix boxes n).hi-(intersectPrefix boxes n).lo ≤ eps.val
    change (boxes n).hi-(boxes n).lo ≤ allowance n at hw
    unfold QInterval.ContainsInterval at hc
    grind only

theorem quadrature_equiv (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) {I : RealCompute} (hI : HasIntegral F I) :
    (quadrature F hab inc mono).Equiv I := by
  have hb : ∀ n m, (quadratureBox F hab inc mono n).lo ≤ (I.compute m).hi ∧
      (I.compute m).lo ≤ (quadratureBox F hab inc mono n).hi := by
    intro n m
    exact hI.bounds (boundsAtTolerance F hab inc mono ⟨allowance n, allowance_pos n⟩) m
  intro n
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr (prefix_encloses _ I hb n n)

theorem quadrature_hasIntegral (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (inc : Bool) (mono : Monotone F inc) {I : RealCompute} (hI : HasIntegral F I) :
    HasIntegral F (quadrature F hab inc mono) :=
  hI.congr (quadrature_valid F hab inc mono hI)
    (RealCompute.equiv_symm (quadrature_equiv F hab inc mono hI))

/-- The actual computed derivative integral. Neither endpoint value appears
in this algorithm except through local rational secant samples. -/
def integral {domain : Rat → Prop} {f : Rat → RealCompute} {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) : RealCompute :=
  quadrature (derivativeOnInterval C) hab inc (derivative_monotone C hf inside hc)

theorem integral_hasIntegral {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    HasIntegral (derivativeOnInterval C) (integral C hab hf inside hc) :=
  quadrature_hasIntegral _ hab inc _ (hasIntegral C hab hf inside hc)

/-- FTC compares an independently evaluated quadrature with the endpoint
difference. The conclusion is derived, not assumed in the input evidence. -/
theorem integral_ftc {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b : Rat} {inc : Bool}
    (C : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    (integral C hab hf inside hc).Equiv (f b-f a) :=
  quadrature_equiv _ hab inc _ (hasIntegral C hab hf inside hc)

/-- Changing the supplied valid secant schedules leaves the integral value
unchanged. The endpoint difference is derived separately for both computations. -/
theorem integral_equiv {domain : Rat → Prop} {f : Rat → RealCompute}
    {a b : Rat} {inc : Bool}
    (C E : ∀ q, inDomainInterval a b q → OuterSecants domain f (RealCompute.ofRat q))
    (hab : a ≤ b) (hf : ∀ q, domain q → (f q).Valid)
    (inside : ∀ q, inDomainInterval a b q → domain q) (hc : Curved domain f inc) :
    (integral C hab hf inside hc).Equiv (integral E hab hf inside hc) :=
  RealCompute.equiv_trans (integral_hasIntegral C hab hf inside hc).valid
    (RealCompute.sub_valid (hf b (inside b ⟨hab, Rat.le_refl⟩))
      (hf a (inside a ⟨Rat.le_refl, hab⟩)))
    (integral_hasIntegral E hab hf inside hc).valid
    (integral_ftc C hab hf inside hc)
    (RealCompute.equiv_symm (integral_ftc E hab hf inside hc))

end ComputableAnalysis.ConvexFTC


