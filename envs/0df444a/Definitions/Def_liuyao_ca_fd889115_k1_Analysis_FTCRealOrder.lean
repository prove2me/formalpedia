-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealOrder
-- name    : liuyao_ca_fd889115_k1_Analysis_FTCRealOrder
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:02:15.193212+00:00
-- url     : https://prove2.me/theorems/49a6b284-a786-4088-806b-7db5748f6166
-- title:
--   Computable analysis · FTCRealOrder · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ConvexFTC

set_option autoImplicit true

/-! Finite real first-order bounds imply the local order law used by FTC.
No integral identity is assumed. Subdivision removes the quadratic error. -/
namespace ComputableAnalysis.FTCRealOrder
open ComputableCoefficient RealApproximationOrder RawLimit Integral
set_option maxHeartbeats 600000

abbrev LE (x y : Value) : Prop := x.real.preferred.Le y.real.preferred

theorem le_congr {x y X Y : Value} (h : LE x y)
    (hx : x.real.preferred.Equiv X.real.preferred)
    (hy : y.real.preferred.Equiv Y.real.preferred) : LE X Y :=
  RealCompute.le_trans x.real.valid
    (RealCompute.le_of_equiv X.real.valid x.real.valid (RealCompute.equiv_symm hx))
    (RealCompute.le_trans y.real.valid h (RealCompute.le_of_equiv y.real.valid Y.real.valid hy))

theorem le_scale {x y : Value} (h : LE x y) {c : Rat} (hc : 0≤c) : LE (scale c x) (scale c y) :=
  RealCompute.le_scaleRat_le_scaleRat hc h

theorem le_add {x y X Y : Value} (h : LE x y) (H : LE X Y) :
    LE (Value.add x X) (Value.add y Y) := RealCompute.le_add_le_add h H

/-- Finite secant evidence on a supplied rational interval. -/
def FirstOrder (f d : Rat → Value) (a b M delta : Rat) : Prop :=
  ∀ u v, a≤u → u<v → v≤b → v-u≤delta →
    Small (sub (sub (f v) (f u)) (scale (v-u) (d u))) (M*(v-u)*(v-u))

theorem increment_lower {f d : Rat → Value} {a b M delta u v l : Rat}
    (H : FirstOrder f d a b M delta) (ha : a≤u) (huv : u<v) (hb : v≤b)
    (hstep : v-u≤delta) (hl : LE (Value.rational l) (d u)) :
    LE (Value.rational ((v-u)*l-M*(v-u)*(v-u))) (sub (f v) (f u)) := by
  have he : LE (Value.rational (-(M*(v-u)*(v-u))))
      (sub (sub (f v) (f u)) (scale (v-u) (d u))) := (H u v ha huv hb hstep).1
  have hd := le_scale hl (show 0≤v-u by grind only)
  have hh := le_add he hd
  apply le_congr hh
  · apply arithmetic_identity
    intro s
    simp only [Value.add,Value.rational,scale]
    grind only
  · apply arithmetic_identity
    intro s
    simp only [Value.add,sub,scale]
    grind only

theorem lower_dyadic {f d : Rat → Value} {a b M delta l : Rat}
    (H : FirstOrder f d a b M delta)
    (hl : ∀ t, a≤t → t≤b → LE (Value.rational l) (d t))
    (k : Nat) {u v : Rat} (ha : a≤u) (huv : u≤v) (hb : v≤b)
    (hstep : (v-u)*((1:Rat)/2)^k≤delta) :
    LE (Value.rational ((v-u)*l-M*(v-u)*(v-u)*((1:Rat)/2)^k)) (sub (f v) (f u)) := by
  induction k generalizing u v with
  | zero =>
    simp only [Rat.pow_zero,Rat.mul_one] at hstep ⊢
    by_cases he : u=v
    · subst v
      intro i j
      have ho := RealCompute.interval_order_of_valid _ (f u).real.valid j
      change (u-u)*l-M*(u-u)*(u-u)≤((f u).real.preferred.compute j).hi-((f u).real.preferred.compute j).lo
      grind only
    · exact increment_lower H ha (by grind only) hb hstep (hl u ha (by grind only))
  | succ k ih =>
    let c : Rat := (u+v)/2
    have hac : a≤c := by dsimp [c]; grind only
    have huc : u≤c := by dsimp [c]; grind only
    have hcv : c≤v := by dsimp [c]; grind only
    have hcb : c≤b := by dsimp [c]; grind only
    have hL : (c-u)*((1:Rat)/2)^k≤delta := by
      rw [Rat.pow_succ] at hstep
      dsimp [c]; grind only
    have hR : (v-c)*((1:Rat)/2)^k≤delta := by
      rw [Rat.pow_succ] at hstep
      dsimp [c]; grind only
    have h := le_add (ih ha huc hcb hL) (ih hac hcv hb hR)
    apply le_congr h
    · apply arithmetic_identity
      intro s
      simp only [Value.add,Value.rational]
      rw [Rat.pow_succ]
      dsimp [c]
      grind only
    · apply arithmetic_identity
      intro s
      simp only [Value.add,sub]
      grind only

theorem lower {f d : Rat → Value} {a b M delta l u v : Rat}
    (H : FirstOrder f d a b M delta) (hM : 0≤M) (hdelta : 0<delta)
    (hl : ∀ t, u≤t → t≤v → LE (Value.rational l) (d t))
    (ha : a≤u) (huv : u≤v) (hb : v≤b) :
    LE (Value.rational ((v-u)*l)) (sub (f v) (f u)) := by
  let e : Nat → Rat := fun n => M*(v-u)*(v-u)*((1:Rat)/2)^n
  have hE : 0≤M*(v-u)*(v-u) := Rat.mul_nonneg (Rat.mul_nonneg hM (by grind only)) (by grind only)
  have shrinks : ShrinksToZero e := by
    intro eps
    exact ⟨RationalMajorant.halfDecayShift _ eps,fun n hn =>
      RationalMajorant.halfDecayShift_spec_of_le hE eps hn⟩
  let N := RationalMajorant.halfDecayShift (v-u) ⟨delta,hdelta⟩
  have hN : ∀ n, N≤n → (v-u)*((1:Rat)/2)^n≤delta :=
    fun n hn => RationalMajorant.halfDecayShift_spec_of_le (by grind only) ⟨delta,hdelta⟩ hn
  apply constant_le_of_shrinking_errors _ _ e shrinks _ (sub (f v) (f u)).real.valid
  intro n
  let k := max N n
  have hk := lower_dyadic (a := u) (b := v)
    (fun x y hx hxy hy hs => H x y (by grind only) hxy (by grind only) hs) hl k
    (Rat.le_refl : u≤u) huv (Rat.le_refl : v≤v) (hN k (Nat.le_max_left _ _))
  have powers {i j : Nat} (hij : i≤j) : ((1:Rat)/2)^j≤((1:Rat)/2)^i := by
    induction hij with
    | refl => exact Rat.le_refl
    | @step j hij ih =>
      rw [Rat.pow_succ]
      have hp := Rat.pow_nonneg (by decide +kernel : (0:Rat)≤1/2) (n := j)
      grind only
  have hm := powers (show n≤k by dsimp [k]; omega)
  have hbnd := Rat.mul_le_mul_of_nonneg_left hm hE
  have hh := hk 0 n
  change (v-u)*l-e k≤_ at hh
  change (v-u)*l-e n≤_
  dsimp [e] at *
  grind only

theorem negate {f d : Rat → Value} {a b M delta : Rat}
    (H : FirstOrder f d a b M delta) :
    FirstOrder (fun q => Value.neg (f q)) (fun q => Value.neg (d q)) a b M delta := by
  intro u v ha huv hb hs
  apply (H u v ha huv hb hs).neg.congr
  apply arithmetic_identity
  intro s
  simp only [Value.neg,sub,scale]
  grind only

theorem upper {f d : Rat → Value} {a b M delta l u v : Rat}
    (H : FirstOrder f d a b M delta) (hM : 0≤M) (hdelta : 0<delta)
    (hl : ∀ t, u≤t → t≤v → LE (d t) (Value.rational l))
    (ha : a≤u) (huv : u≤v) (hb : v≤b) :
    LE (sub (f v) (f u)) (Value.rational ((v-u)*l)) := by
  have hd (t : Rat) (ht : u≤t) (ht' : t≤v) : LE (Value.rational (-l)) (Value.neg (d t)) := by
    intro i j
    have hh := hl t ht ht' j i
    change -l≤ -((d t).real.preferred.compute j).lo
    exact Rat.neg_le_neg hh
  have h := lower (negate H) hM hdelta hd ha huv hb
  intro i j
  have hh := h 0 i
  change (v-u)*(-l)≤ -((f v).real.preferred.compute i).lo-(-((f u).real.preferred.compute i).hi) at hh
  change ((f v).real.preferred.compute i).lo-((f u).real.preferred.compute i).hi≤(v-u)*l
  grind only

end ComputableAnalysis.FTCRealOrder


