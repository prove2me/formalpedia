-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_SecantFoundation
-- name    : liuyao_ca_fd889115_k1_Analysis_SecantFoundation
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:14.066203+00:00
-- url     : https://prove2.me/theorems/09715074-839b-4efc-a80e-38446cbd1ae0
-- title:
--   Computable analysis · SecantFoundation · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/SecantFoundation.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralFTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-!
Finite secant constructions and telescoping laws. These do not assert that an
arbitrary function has a derivative or an integral. Concrete functions supply
their already proved finite-difference estimates.
-/
namespace ComputableAnalysis
namespace SecantFoundation

set_option maxHeartbeats 2000000

theorem abs_div (a h : Rat) (hh : h≠0) : qabs (a/h)=qabs a/qabs h := by
  by_cases hp : 0<h
  · rw [Rat.div_def,qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hp),
      qabs_eq_self_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp)),Rat.div_def]
  · have hn : h<0 := by grind
    have hc := Rat.mul_inv_cancel h hh
    have hneg : (-h)⁻¹ = -h⁻¹ := by
      have hm : (-h)*(-h⁻¹)=1 := by grind
      calc
        (-h)⁻¹ = (-h)⁻¹*1 := by rw [Rat.mul_one]
        _ = (-h)⁻¹*((-h)*(-h⁻¹)) := by rw [hm]
        _ = ((-h)⁻¹*(-h))*(-h⁻¹) := by rw [Rat.mul_assoc]
        _ = -h⁻¹ := by rw [Rat.inv_mul_cancel (-h) (by grind),Rat.one_mul]
    have hi : h⁻¹<0 := by
      have hp := Rat.inv_pos.mpr (show 0 < -h by grind)
      rw [hneg] at hp
      grind
    rw [Rat.div_def,qabs_mul,qabs_eq_neg_of_nonpos (Rat.le_of_lt hn),
      qabs_eq_neg_of_nonpos (Rat.le_of_lt hi),Rat.div_def,hneg]

def value (F : FunctionOnInterval) (x : Rat) : RealCompute :=
  if hx : F.lower ≤ x ∧ x ≤ F.upper then
    { compute := F.compute x hx }
  else RealCompute.ofRat 0

theorem value_compute (F : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (value F x).compute n = F.compute x hx n := by
  change F.lower ≤ x ∧ x ≤ F.upper at hx
  simp only [value, dif_pos hx]

theorem value_valid (F : FunctionOnInterval) (x : Rat) : (value F x).Valid := by
  unfold value
  split
  · next hx => exact F.valid_on x (F.defined_on x hx)
  · exact RealCompute.ofRat_valid 0

def secantStep (p : Nat) (radius : Rat) : Rat := radius/((p+1:Nat):Rat)

theorem secantStep_bounds (p : Nat) (radius : Rat)
    (hp : 0 < p) (hr : 0 < radius) (hr1 : radius ≤ 1) :
    0 < secantStep p radius ∧ secantStep p radius ≤ radius ∧
      secantStep p radius ≤ 1/(p:Rat) := by
  have ha : 0 < (p:Rat) := by exact_mod_cast hp
  have hb : 0 < ((p+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos p
  have ha1 : (p:Rat) ≤ ((p+1:Nat):Rat) := by exact_mod_cast Nat.le_succ p
  have hb1 : (1:Rat) ≤ ((p+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos p
  have hca := Rat.mul_inv_cancel (p:Rat) (Rat.ne_of_gt ha)
  have hcb := Rat.mul_inv_cancel ((p+1:Nat):Rat) (Rat.ne_of_gt hb)
  unfold secantStep
  constructor
  · rw [Rat.div_def]; exact Rat.mul_pos hr (Rat.inv_pos.mpr hb)
  constructor
  · apply Rat.le_of_mul_le_mul_right (c:=((p+1:Nat):Rat)) _ hb
    have hm := Rat.mul_le_mul_of_nonneg_left hb1 (Rat.le_of_lt hr)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hb)]
    grind
  · apply Rat.le_of_mul_le_mul_right (c:=(p:Rat)*((p+1:Nat):Rat)) _ (Rat.mul_pos ha hb)
    simp only [Rat.div_def,Rat.one_mul]
    have hm := Rat.mul_le_mul_of_nonneg_right hr1 (Rat.le_of_lt ha)
    calc
      radius*((p+1:Nat):Rat)⁻¹*((p:Rat)*((p+1:Nat):Rat)) = radius*(p:Rat) := by grind [Rat.mul_assoc,Rat.mul_comm]
      _ ≤ (p:Rat) := by simpa only [Rat.one_mul] using hm
      _ ≤ ((p+1:Nat):Rat) := ha1
      _ = (p:Rat)⁻¹*((p:Rat)*((p+1:Nat):Rat)) := by grind [Rat.mul_assoc,Rat.mul_comm]

/-- Left and right finite differences at rational inputs, padded by their
proved error. The closed derivative formula is absent from this algorithm. -/
def derivativeCandidate {F D : FunctionOnInterval} (H : HasDerivativeOnInterval F D)
    (x radius : Rat) : RealCompute where
  compute n :=
    let h := secantStep (H.stepPrecision n) radius
    let left := QInterval.differenceQuotient
      ((value F (x-h)).compute (H.evalPrecision x (-h) n))
      ((value F x).compute (H.evalPrecision x (-h) n)) (-h)
    let right := QInterval.differenceQuotient
      ((value F (x+h)).compute (H.evalPrecision x h n))
      ((value F x).compute (H.evalPrecision x h n)) h
    QInterval.expand (QInterval.hull left right) (2*(precisionAtStage n).val)

theorem derivativeCandidate_bounds {F D : FunctionOnInterval}
    (H : HasDerivativeOnInterval F D) (hstep : ∀ n, 0 < H.stepPrecision n)
    (x radius : Rat) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hx : inDomainInterval F.lower F.upper x)
    (hl : F.lower ≤ x-radius) (hu : x+radius ≤ F.upper) (n : Nat) :
    ((derivativeCandidate H x radius).compute n).width ≤ 10*(precisionAtStage n).val ∧
    ∀ m, ((derivativeCandidate H x radius).compute n).Overlaps ((value D x).compute m) := by
  let h := secantStep (H.stepPrecision n) radius
  have hb := secantStep_bounds (H.stepPrecision n) radius (hstep n) hr hr1
  have hleft : inDomainInterval F.lower F.upper (x-h) := by
    constructor <;> grind
  have hright : inDomainInterval F.lower F.upper (x+h) := by
    constructor <;> grind
  have hD : inDomainInterval D.lower D.upper x := by
    simpa [H.same_lower,H.same_upper] using hx
  have hcL := H.close x (-h) n hx
    (by simpa only [Rat.sub_eq_add_neg] using hleft) hD
    (by grind : -h≠0) (by rw [qabs_neg,qabs_eq_self_of_nonneg (Rat.le_of_lt hb.1)]; exact hb.2.2)
  have hcR := H.close x h n hx hright hD (Rat.ne_of_gt hb.1)
    (by rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hb.1)]; exact hb.2.2)
  let pL := H.evalPrecision x (-h) n
  let pR := H.evalPrecision x h n
  have hcL' : QInterval.NearAt
      (QInterval.differenceQuotient ((value F (x-h)).compute pL)
        ((value F x).compute pL) (-h)) ((value D x).compute pL) (precisionAtStage n) := by
    simpa only [value_compute F (x-h) hleft,value_compute F x hx,value_compute D x hD,
      intervalNearAtPrecision,show x + -h = x-h by grind] using hcL
  have hcR' : QInterval.NearAt
      (QInterval.differenceQuotient ((value F (x+h)).compute pR)
        ((value F x).compute pR) h) ((value D x).compute pR) (precisionAtStage n) := by
    simpa only [value_compute F (x+h) hright,value_compute F x hx,value_compute D x hD,
      intervalNearAtPrecision] using hcR
  have hv := value_valid D x
  have hep := (precisionAtStage n).property
  have hovLR := RealCompute.le_refl (value D x) hv pL pR
  have hovRL := RealCompute.le_refl (value D x) hv pR pL
  constructor
  · dsimp [derivativeCandidate]
    unfold QInterval.NearAt QInterval.width at hcL' hcR'
    unfold QInterval.expand QInterval.hull QInterval.width
    grind
  · intro m
    have hovLM := RealCompute.le_refl (value D x) hv pL m
    have hovML := RealCompute.le_refl (value D x) hv m pL
    dsimp [derivativeCandidate]
    unfold QInterval.NearAt QInterval.width at hcL'
    unfold QInterval.expand QInterval.hull QInterval.Overlaps
    grind

def derivative {F D : FunctionOnInterval} (H : HasDerivativeOnInterval F D)
    (x radius : Rat) (padding : Nat → Rat) : RealCompute :=
  RealCompute.prefixStabilize (derivativeCandidate H x radius) padding

/-- Both nesting and shrinking are proved for the literal secant algorithm;
the supplied finite estimate has already been constructed for the function. -/
theorem derivative_valid_and_equiv {F D : FunctionOnInterval}
    (H : HasDerivativeOnInterval F D) (hstep : ∀ n, 0 < H.stepPrecision n)
    (x radius : Rat) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hx : inDomainInterval F.lower F.upper x)
    (hl : F.lower ≤ x-radius) (hu : x+radius ≤ F.upper)
    (padding : Nat → Rat) (hw : ∀ n, ((value D x).compute n).width ≤ padding n)
    (hs : ShrinksToZero padding) :
    (derivative H x radius padding).Valid ∧
      (derivative H x radius padding).Equiv (value D x) := by
  have hb := derivativeCandidate_bounds H hstep x radius hr hr1 hx hl hu
  have he : (derivativeCandidate H x radius).Equiv (value D x) := by
    intro n
    exact (RealCompute.compareAt_overlap_iff _ _ n n).2 ((hb n).2 n)
  have hc : RealCompute.WidthsShrinkToZero (derivativeCandidate H x radius).compute := by
    intro eps
    let small : QPos := ⟨eps.val/10,by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨N,hN⟩ := precisionAtStage_shrinksToZero small
    refine ⟨N,fun n hn => ?_⟩
    have he := hN n hn
    have hm := Rat.mul_le_mul_of_nonneg_left he (by decide +kernel : (0:Rat)≤10)
    dsimp [small] at hm
    have hbnd := (hb n).1
    grind
  exact ⟨RealCompute.prefixStabilize_valid hc (value_valid D x) he hw hs,
    RealCompute.prefixStabilize_equiv_anchor (value_valid D x) he hw⟩

private theorem small_cell {F D : FunctionOnInterval}
    (H : HasDerivativeOnInterval F D) (u v l r : Rat) (n : Nat)
    (hu : inDomainInterval F.lower F.upper u)
    (hv : inDomainInterval F.lower F.upper v) (huv : u < v)
    (hs : v-u ≤ 1/((H.stepPrecision n : Nat) : Rat))
    (hl : ∀ x (hx : inDomainInterval D.lower D.upper x), u ≤ x → x ≤ v →
      ∀ k, l ≤ (D.compute x hx k).hi)
    (hr : ∀ x (hx : inDomainInterval D.lower D.upper x), u ≤ x → x ≤ v →
      ∀ k, (D.compute x hx k).lo ≤ r) :
    (RealCompute.ofRat ((v-u)*(l-3*(precisionAtStage n).val))).Le
      (value F v-value F u) ∧
    (value F v-value F u).Le
      (RealCompute.ofRat ((v-u)*(r+3*(precisionAtStage n).val))) := by
  let h := v-u
  have hp : 0 < h := by dsimp [h]; grind
  have hxD : inDomainInterval D.lower D.upper u := by
    simpa [H.same_lower,H.same_upper] using hu
  have huvEq : u+h = v := by dsimp [h]; grind
  have hxv : inDomainInterval F.lower F.upper (u+h) := by
    simpa only [huvEq] using hv
  have hc := H.close u h n hu hxv hxD (Rat.ne_of_gt hp)
    (by simpa [qabs_eq_self_of_nonneg (Rat.le_of_lt hp)] using hs)
  let p := H.evalPrecision u h n
  let Q := QInterval.differenceQuotient (F.compute v hv p) (F.compute u hu p) h
  let J := D.compute u hxD p
  let e := (precisionAtStage n).val
  have hc' : Q.lo ≤ J.hi+e ∧ J.lo ≤ Q.hi+e ∧ Q.width ≤ e ∧ J.width ≤ e := by
    simpa only [intervalNearAtPrecision,QInterval.NearAt,huvEq] using hc
  have hlow := hl u hxD (Rat.le_refl) (Rat.le_of_lt huv) p
  have hhigh := hr u hxD (Rat.le_refl) (Rat.le_of_lt huv) p
  have hql : l-3*e ≤ Q.lo := by grind [QInterval.width]
  have hqu : Q.hi ≤ r+3*e := by grind [QInterval.width]
  have hcancel := Rat.mul_inv_cancel h (Rat.ne_of_gt hp)
  have helo : h*Q.lo = (F.compute v hv p).lo-(F.compute u hu p).hi := by
    dsimp [Q,QInterval.differenceQuotient,QInterval.divRat]
    simp only [QInterval.scaleRat,Rat.div_def,Rat.one_mul,if_pos (Rat.le_of_lt (Rat.inv_pos.mpr hp)),QInterval.sub]
    grind [Rat.mul_assoc,Rat.mul_comm]
  have hehi : h*Q.hi = (F.compute v hv p).hi-(F.compute u hu p).lo := by
    dsimp [Q,QInterval.differenceQuotient,QInterval.divRat]
    simp only [QInterval.scaleRat,Rat.div_def,Rat.one_mul,if_pos (Rat.le_of_lt (Rat.inv_pos.mpr hp)),QInterval.sub]
    grind [Rat.mul_assoc,Rat.mul_comm]
  have hb := Rat.mul_le_mul_of_nonneg_left hql (Rat.le_of_lt hp)
  have ht := Rat.mul_le_mul_of_nonneg_left hqu (Rat.le_of_lt hp)
  rw [helo] at hb
  rw [hehi] at ht
  constructor
  · intro _ m
    have hov := RealCompute.le_refl (value F v-value F u) (RealCompute.sub_valid (value_valid F v) (value_valid F u)) p m
    change ((value F v).compute _).lo - ((value F u).compute _).hi ≤ ((value F v).compute _).hi - ((value F u).compute _).lo at hov
    rw [value_compute F v hv,value_compute F u hu,value_compute F v hv,value_compute F u hu] at hov
    change (F.compute v hv p).lo-(F.compute u hu p).hi ≤
      (F.compute v hv m).hi-(F.compute u hu m).lo at hov
    change h*(l-3*e) ≤ ((value F v).compute m).hi-((value F u).compute m).lo
    rw [value_compute F v hv,value_compute F u hu]
    exact Rat.le_trans hb hov
  · intro m _
    have hov := RealCompute.le_refl (value F v-value F u) (RealCompute.sub_valid (value_valid F v) (value_valid F u)) m p
    change ((value F v).compute _).lo - ((value F u).compute _).hi ≤ ((value F v).compute _).hi - ((value F u).compute _).lo at hov
    rw [value_compute F v hv,value_compute F u hu,value_compute F v hv,value_compute F u hu] at hov
    change (F.compute v hv m).lo-(F.compute u hu m).hi ≤
      (F.compute v hv p).hi-(F.compute u hu p).lo at hov
    change ((value F v).compute m).lo-((value F u).compute m).hi ≤ h*(r+3*e)
    rw [value_compute F v hv,value_compute F u hu]
    exact Rat.le_trans hov ht

private theorem subdivide {F D : FunctionOnInterval}
    (H : HasDerivativeOnInterval F D) (l r : Rat) (n k : Nat)
    (u v : Rat) (hu : inDomainInterval F.lower F.upper u)
    (hv : inDomainInterval F.lower F.upper v) (huv : u ≤ v)
    (hs : (v-u)*((1:Rat)/2)^k ≤ 1/((H.stepPrecision n : Nat) : Rat))
    (hl : ∀ x (hx : inDomainInterval D.lower D.upper x), u ≤ x → x ≤ v →
      ∀ j, l ≤ (D.compute x hx j).hi)
    (hr : ∀ x (hx : inDomainInterval D.lower D.upper x), u ≤ x → x ≤ v →
      ∀ j, (D.compute x hx j).lo ≤ r) :
    (RealCompute.ofRat ((v-u)*(l-3*(precisionAtStage n).val))).Le
      (value F v-value F u) ∧
    (value F v-value F u).Le
      (RealCompute.ofRat ((v-u)*(r+3*(precisionAtStage n).val))) := by
  induction k generalizing u v with
  | zero =>
    by_cases he : u=v
    · subst v
      constructor
      · intro _ m
        have ho := RealCompute.interval_order_of_valid _ (value_valid F u) m
        change (u-u)*(l-3*(precisionAtStage n).val) ≤ ((value F u).compute m).hi-((value F u).compute m).lo
        grind
      · intro m _
        have ho := RealCompute.interval_order_of_valid _ (value_valid F u) m
        change ((value F u).compute m).lo-((value F u).compute m).hi ≤ (u-u)*(r+3*(precisionAtStage n).val)
        grind
    · exact small_cell H u v l r n hu hv (by grind)
        (by simpa only [Rat.pow_zero,Rat.mul_one] using hs) hl hr
  | succ k ih =>
    let z := (u+v)/2
    have huz : u ≤ z := by dsimp [z]; grind
    have hzv : z ≤ v := by dsimp [z]; grind
    have hz : inDomainInterval F.lower F.upper z :=
      ⟨Rat.le_trans hu.1 huz,Rat.le_trans hzv hv.2⟩
    have hzs : (z-u)*((1:Rat)/2)^k ≤ 1/((H.stepPrecision n : Nat) : Rat) := by
      rw [Rat.pow_succ] at hs
      dsimp [z]; grind
    have hsz : (v-z)*((1:Rat)/2)^k ≤ 1/((H.stepPrecision n : Nat) : Rat) := by
      rw [Rat.pow_succ] at hs
      dsimp [z]; grind
    have hleft := ih u z hu hz huz hzs
      (fun x hx hux hxz => hl x hx hux (Rat.le_trans hxz hzv))
      (fun x hx hux hxz => hr x hx hux (Rat.le_trans hxz hzv))
    have hright := ih z v hz hv hzv hsz
      (fun x hx hzx hxv => hl x hx (Rat.le_trans huz hzx) hxv)
      (fun x hx hzx hxv => hr x hx (Rat.le_trans huz hzx) hxv)
    have ht := RealCompute.sub_add_sub_cancel_middle_equiv
      (value_valid F u) (value_valid F z) (value_valid F v)
    have hsum := RealCompute.add_valid
      (RealCompute.sub_valid (value_valid F z) (value_valid F u))
      (RealCompute.sub_valid (value_valid F v) (value_valid F z))
    have hend := RealCompute.sub_valid (value_valid F v) (value_valid F u)
    have hladd := RealCompute.le_add_le_add hleft.1 hright.1
    have hradd := RealCompute.le_add_le_add hleft.2 hright.2
    have hlend := RealCompute.le_trans hsum hladd (RealCompute.le_of_equiv hsum hend ht)
    have hrend := RealCompute.le_trans hsum
      (RealCompute.le_of_equiv hend hsum (RealCompute.equiv_symm ht)) hradd
    constructor
    · intro j m
      have he := hlend j m
      change (z-u)*(l-3*(precisionAtStage n).val)+(v-z)*(l-3*(precisionAtStage n).val) ≤ _ at he
      have eq : (z-u)*(l-3*(precisionAtStage n).val)+(v-z)*(l-3*(precisionAtStage n).val) =
          (v-u)*(l-3*(precisionAtStage n).val) := by grind
      rw [eq] at he
      exact he
    · intro m j
      have he := hrend m j
      change _ ≤ (z-u)*(r+3*(precisionAtStage n).val)+(v-z)*(r+3*(precisionAtStage n).val) at he
      have eq : (z-u)*(r+3*(precisionAtStage n).val)+(v-z)*(r+3*(precisionAtStage n).val) =
          (v-u)*(r+3*(precisionAtStage n).val) := by grind
      rw [eq] at he
      exact he

/-- Finite subdivision and shrinking secant errors prove the exact cell laws
used by FTC. No integral or endpoint identity is assumed. -/
theorem cellDerivativeBounds {F D : FunctionOnInterval}
    (H : HasDerivativeOnInterval F D)
    (hstep : ∀ n, 0 < H.stepPrecision n) (B : Rat)
    (hbound : ∀ x (hx : inDomainInterval D.lower D.upper x) n,
      -B ≤ (D.compute x hx n).lo ∧ (D.compute x hx n).hi ≤ B) :
    Integral.CellDerivativeBounds D (value F) := by
  constructor
  · intro x _; exact value_valid F x
  · intro u v l hu huv hv hl _ m
    have huF : inDomainInterval F.lower F.upper u := by
      rw [←H.same_lower,←H.same_upper]; exact ⟨hu,Rat.le_trans huv hv⟩
    have hvF : inDomainInterval F.lower F.upper v := by
      rw [←H.same_lower,←H.same_upper]; exact ⟨Rat.le_trans hu huv,hv⟩
    change (v-u)*l ≤ ((value F v-value F u).compute m).hi
    by_cases hn : (v-u)*l ≤ ((value F v-value F u).compute m).hi
    · exact hn
    exfalso
    let eps : QPos := ⟨((v-u)*l-((value F v-value F u).compute m).hi)/2,by grind⟩
    let n := RationalMajorant.natRateStage (3*(v-u)) eps+1
    have he := RationalMajorant.natRateStage_spec_of_le (by grind : 0 ≤ 3*(v-u)) eps (Nat.le_refl (n-1))
    let delta : QPos := ⟨1/((H.stepPrecision n:Nat):Rat),by
      rw [Rat.div_def,Rat.one_mul]
      exact Rat.inv_pos.mpr (by exact_mod_cast hstep n)⟩
    have hs := RationalMajorant.halfDecayShift_spec (by grind : 0 ≤ v-u) delta
    have h := (subdivide H l B n (RationalMajorant.halfDecayShift (v-u) delta)
      u v huF hvF huv hs hl
      (fun x hx _ _ j => Rat.le_trans
        (RealCompute.interval_order_of_valid {compute:=D.compute x hx} (D.valid_on x (D.defined_on x hx)) j) (hbound x hx j).2)).1 0 m
    change (v-u)*(l-3*(precisionAtStage n).val) ≤ _ at h
    change 3*(v-u)/(n:Rat) ≤ eps.val at he
    simp only [precisionAtStage,if_neg (show n≠0 by dsimp [n]; omega)] at h
    dsimp [eps] at he
    grind [Rat.div_def]
  · intro u v r hu huv hv hr m _
    have huF : inDomainInterval F.lower F.upper u := by
      rw [←H.same_lower,←H.same_upper]; exact ⟨hu,Rat.le_trans huv hv⟩
    have hvF : inDomainInterval F.lower F.upper v := by
      rw [←H.same_lower,←H.same_upper]; exact ⟨Rat.le_trans hu huv,hv⟩
    change ((value F v-value F u).compute m).lo ≤ (v-u)*r
    by_cases hn : ((value F v-value F u).compute m).lo ≤ (v-u)*r
    · exact hn
    exfalso
    let eps : QPos := ⟨(((value F v-value F u).compute m).lo-(v-u)*r)/2,by grind⟩
    let n := RationalMajorant.natRateStage (3*(v-u)) eps+1
    have he := RationalMajorant.natRateStage_spec_of_le (by grind : 0 ≤ 3*(v-u)) eps (Nat.le_refl (n-1))
    let delta : QPos := ⟨1/((H.stepPrecision n:Nat):Rat),by
      rw [Rat.div_def,Rat.one_mul]
      exact Rat.inv_pos.mpr (by exact_mod_cast hstep n)⟩
    have hs := RationalMajorant.halfDecayShift_spec (by grind : 0 ≤ v-u) delta
    have h := (subdivide H (-B) r n (RationalMajorant.halfDecayShift (v-u) delta)
      u v huF hvF huv hs
      (fun x hx _ _ j => by
        have hb := hbound x hx j
        have ho := D.valid_on x (D.defined_on x hx)
        have hord := RealCompute.interval_order_of_valid {compute:=D.compute x hx} ho j
        exact Rat.le_trans hb.1 hord) hr).2 m 0
    change _ ≤ (v-u)*(r+3*(precisionAtStage n).val) at h
    change 3*(v-u)/(n:Rat) ≤ eps.val at he
    simp only [precisionAtStage,if_neg (show n≠0 by dsimp [n]; omega)] at h
    dsimp [eps] at he
    grind [Rat.div_def]

end SecantFoundation
end ComputableAnalysis


