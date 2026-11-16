-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus
-- name    : liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:08:24.885556+00:00
-- url     : https://prove2.me/theorems/7b14afa9-9485-4e55-9309-33e2b086620e
-- title:
--   Computable analysis · FTCRealCalculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FTCRealCalculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealOrder
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzIntegralBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralValueBounds

set_option autoImplicit true

/-! A justified FTC step for a supplied real computation and its supplied
derivative. Finite first-order data and tight integrand bounds prove the
integral role; the record contains no integral or endpoint-agreement field. -/
namespace ComputableAnalysis.FTCRealCalculus
open ComputableCoefficient RealApproximationOrder FTCRealOrder Integral
set_option maxHeartbeats 500000

theorem rational_small (r : Rat) : Small (Value.rational r) (qabs r) := by
  constructor
  · intro _ _; exact neg_qabs_le_self r
  · intro _ _; exact self_le_qabs r

theorem scale_small {x : Value} {B : Rat} (h : Small x B) (c : Rat) : Small (scale c x) (qabs c*B) := by
  apply ((rational_small c).mul h).congr
  apply arithmetic_identity
  intro s
  simp only [Value.mul,Value.rational,scale]

structure Step (f d : Rat → Value) (a b : Rat) where
  error : Rat
  error_nonnegative : 0≤error
  radius : QPos
  firstOrder : FTCRealOrder.FirstOrder f d a b error radius.val
  variation : Rat
  variation_nonnegative : 0≤variation
  lipschitz : LipschitzIntegralBounds.Lipschitz d a b variation

namespace Step

def restrict {f d : Rat → Value} {a b : Rat} (S : Step f d a b)
    (u v : Rat) (hu : a≤u) (hv : v≤b) : Step f d u v where
  error := S.error
  error_nonnegative := S.error_nonnegative
  radius := S.radius
  firstOrder x y hx hxy hy hs := S.firstOrder x y (by grind only) hxy (by grind only) hs
  variation := S.variation
  variation_nonnegative := S.variation_nonnegative
  lipschitz x y hx hxy hy := S.lipschitz x y (by grind only) hxy (by grind only)

theorem cellBounds {f d : Rat → Value} {a b : Rat} (S : Step f d a b) :
    CellDerivativeBounds (LipschitzIntegralBounds.onInterval d a b) (fun q => (f q).real.preferred) := by
  refine ⟨fun q _ => (f q).real.valid,?_,?_⟩
  · intro u v l hu huv hv hl
    exact FTCRealOrder.lower S.firstOrder S.error_nonnegative S.radius.property
      (fun t ht ht' => fun _ n => hl t ⟨by grind only,by grind only⟩ ht ht' n) hu huv hv
  · intro u v r hu huv hv hr
    exact FTCRealOrder.upper S.firstOrder S.error_nonnegative S.radius.property
      (fun t ht ht' => fun n _ => hr t ⟨by grind only,by grind only⟩ ht ht' n) hu huv hv

/-- The actual endpoint computation has the mathematical definite-integral
role. This conclusion follows from finite derivative evidence and rectangles. -/
theorem hasIntegral {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) :
    HasIntegral (LipschitzIntegralBounds.onInterval d a b)
      ((f b).real.preferred-(f a).real.preferred) :=
  S.cellBounds.hasIntegral hab (LipschitzIntegralBounds.tight d a b S.variation hab S.lipschitz S.variation_nonnegative)

theorem ftc {f d : Rat → Value} {a b : Rat} (S : Step f d a b) {I : RealCompute}
    (hI : HasIntegral (LipschitzIntegralBounds.onInterval d a b) I) :
    I.Equiv ((f b).real.preferred-(f a).real.preferred) := hI.ftc S.cellBounds

theorem nonnegative {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b)
    (hd : ∀ q, a≤q → q≤b → LE (Value.rational 0) (d q)) :
    LE (Value.rational 0) (sub (f b) (f a)) :=
  (S.hasIntegral hab).nonnegative (fun q hq n => hd q hq.1 hq.2 0 n)

def constant (C : Value) (a b : Rat) : Step (fun _ => C) (fun _ => Value.rational 0) a b where
  error := 0
  error_nonnegative := by decide +kernel
  radius := ⟨1,by decide +kernel⟩
  firstOrder := by
    intro u v _ _ _ _
    simp only [Rat.zero_mul]
    have hz : Small (Value.rational 0) 0 := by simpa only [show qabs (0:Rat)=0 by decide +kernel] using rational_small 0
    apply hz.congr
    apply arithmetic_identity
    intro s
    simp only [Value.rational,sub,scale]
    grind only
  variation := 0
  variation_nonnegative := by decide +kernel
  lipschitz := by
    intro u v _ _ _
    simp only [Rat.zero_mul]
    have hz : Small (Value.rational 0) 0 := by simpa only [show qabs (0:Rat)=0 by decide +kernel] using rational_small 0
    apply hz.congr
    apply arithmetic_identity
    intro s
    simp only [Value.rational,sub]
    grind only

def scale {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (c : Rat) :
    Step (fun q => RealApproximationOrder.scale c (f q))
      (fun q => RealApproximationOrder.scale c (d q)) a b where
  error := qabs c*S.error
  error_nonnegative := Rat.mul_nonneg (qabs_nonneg c) S.error_nonnegative
  radius := S.radius
  firstOrder := by
    intro u v hu huv hv hs
    have h := scale_small (S.firstOrder u v hu huv hv hs) c
    have he : qabs c*(S.error*(v-u)*(v-u))=(qabs c*S.error)*(v-u)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [RealApproximationOrder.scale,sub]
    grind only
  variation := qabs c*S.variation
  variation_nonnegative := Rat.mul_nonneg (qabs_nonneg c) S.variation_nonnegative
  lipschitz := by
    intro u v hu huv hv
    have h := scale_small (S.lipschitz u v hu huv hv) c
    have he : qabs c*(S.variation*(v-u))=(qabs c*S.variation)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [RealApproximationOrder.scale,sub]
    grind only

def add {f d g e : Rat → Value} {a b : Rat} (S : Step f d a b) (T : Step g e a b) :
    Step (fun q => Value.add (f q) (g q)) (fun q => Value.add (d q) (e q)) a b where
  error := S.error+T.error
  error_nonnegative := Rat.add_nonneg S.error_nonnegative T.error_nonnegative
  radius := ⟨min S.radius.val T.radius.val,by have := S.radius.property; have := T.radius.property; grind⟩
  firstOrder := by
    intro u v hu huv hv hs
    have h := (S.firstOrder u v hu huv hv (by grind)).add (T.firstOrder u v hu huv hv (by grind))
    have he : S.error*(v-u)*(v-u)+T.error*(v-u)*(v-u)=(S.error+T.error)*(v-u)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [Value.add,sub,RealApproximationOrder.scale]
    grind only
  variation := S.variation+T.variation
  variation_nonnegative := Rat.add_nonneg S.variation_nonnegative T.variation_nonnegative
  lipschitz := by
    intro u v hu huv hv
    have h := (S.lipschitz u v hu huv hv).add (T.lipschitz u v hu huv hv)
    have he : S.variation*(v-u)+T.variation*(v-u)=(S.variation+T.variation)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [Value.add,sub]
    grind only

def subtract {f d g e : Rat → Value} {a b : Rat} (S : Step f d a b) (T : Step g e a b) :
    Step (fun q => sub (f q) (g q)) (fun q => sub (d q) (e q)) a b := by
  let H := S.add (T.scale (-1))
  refine ⟨H.error,H.error_nonnegative,H.radius,?_,H.variation,H.variation_nonnegative,?_⟩
  · intro u v hu huv hv hs
    apply (H.firstOrder u v hu huv hv hs).congr
    apply arithmetic_identity
    intro s
    simp only [Value.add,sub,RealApproximationOrder.scale]
    grind only
  · intro u v hu huv hv
    apply (H.lipschitz u v hu huv hv).congr
    apply arithmetic_identity
    intro s
    simp only [Value.add,sub,RealApproximationOrder.scale]
    grind only

def congr {f d g e : Rat → Value} {a b : Rat} (S : Step f d a b)
    (hf : ∀ q, (f q).real.preferred.Equiv (g q).real.preferred)
    (hd : ∀ q, (d q).real.preferred.Equiv (e q).real.preferred) : Step g e a b where
  error := S.error
  error_nonnegative := S.error_nonnegative
  radius := S.radius
  firstOrder := by
    intro u v hu huv hv hs
    apply (S.firstOrder u v hu huv hv hs).congr
    exact RealCompute.sub_equiv (sub (f v) (f u)).real.valid (sub (g v) (g u)).real.valid
      (RealApproximationOrder.scale (v-u) (d u)).real.valid (RealApproximationOrder.scale (v-u) (e u)).real.valid
      (RealCompute.sub_equiv (f v).real.valid (g v).real.valid (f u).real.valid (g u).real.valid (hf v) (hf u))
      (RealCompute.scaleRat_equiv (hd u))
  variation := S.variation
  variation_nonnegative := S.variation_nonnegative
  lipschitz := by
    intro u v hu huv hv
    apply (S.lipschitz u v hu huv hv).congr
    exact RealCompute.sub_equiv (d v).real.valid (e v).real.valid (d u).real.valid (e u).real.valid (hd v) (hd u)

def mul_constant {f d : Rat → Value} {a b : Rat} (S : Step f d a b)
    (C : Value) (B : Rat) (hB : 0≤B) (hC : Small C B) :
    Step (fun q => Value.mul C (f q)) (fun q => Value.mul C (d q)) a b where
  error := B*S.error
  error_nonnegative := Rat.mul_nonneg hB S.error_nonnegative
  radius := S.radius
  firstOrder := by
    intro u v hu huv hv hs
    have h := hC.mul (S.firstOrder u v hu huv hv hs)
    have he : B*(S.error*(v-u)*(v-u))=(B*S.error)*(v-u)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [Value.mul,sub,RealApproximationOrder.scale]
    grind only
  variation := B*S.variation
  variation_nonnegative := Rat.mul_nonneg hB S.variation_nonnegative
  lipschitz := by
    intro u v hu huv hv
    have h := hC.mul (S.lipschitz u v hu huv hv)
    have he : B*(S.variation*(v-u))=(B*S.variation)*(v-u) := by grind only
    rw [he] at h
    apply h.congr
    apply arithmetic_identity
    intro s
    simp only [Value.mul,sub]
    grind only

end Step
/-- The FTC order law bounds a function increment by a supplied uniform
bound for its derivative. This gives the integrand variation needed by the
next FTC step. -/
theorem lipschitz_of_firstOrder {f d : Rat → Value} {a b M delta C : Rat}
    (H : FTCRealOrder.FirstOrder f d a b M delta) (hM : 0≤M) (hd : 0<delta)
    (bounded : ∀ t, a≤t → t≤b → Small (d t) C) :
    LipschitzIntegralBounds.Lipschitz f a b C := by
  intro u v hu huv hv
  have hl := FTCRealOrder.lower H hM hd
    (fun t ht ht' => (bounded t (by grind only) (by grind only)).1) hu huv hv
  have hr := FTCRealOrder.upper H hM hd
    (fun t ht ht' => (bounded t (by grind only) (by grind only)).2) hu huv hv
  constructor
  · intro i j
    have hh := hl i j
    change (v-u)*(-C)≤_ at hh
    change -(C*(v-u))≤_
    grind only
  · intro i j
    have hh := hr i j
    change _≤(v-u)*C at hh
    change _≤C*(v-u)
    grind only

end ComputableAnalysis.FTCRealCalculus


