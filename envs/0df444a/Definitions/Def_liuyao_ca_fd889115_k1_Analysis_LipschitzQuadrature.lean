-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature
-- name    : liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:12:39.635999+00:00
-- url     : https://prove2.me/theorems/ab7cd55c-c689-427b-a300-bf9a567737c5
-- title:
--   Computable analysis · LipschitzQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/LipschitzQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealProduct
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzIntegralBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BoundsQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLaws
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralValueBounds

set_option autoImplicit true

/-! An executable proper integral for a supplied sampler and justified
Lipschitz evidence. This is one sufficient construction route; it imposes no
integrand class on other integral constructions. -/
namespace ComputableAnalysis.LipschitzQuadrature
open ComputableCoefficient RealApproximationOrder RawLimit Integral
set_option maxHeartbeats 600000

structure Data (f : Rat → Value) (a b : Rat) where
  ordered : a≤b
  constant : Rat
  nonnegative : 0≤constant
  lipschitz : LipschitzIntegralBounds.Lipschitz f a b constant

/-- The executable quadrature certificate on the integer-first dyadic grid. -/
def Data.dyadic {f : Rat → Value} {a b : Rat} (D : Data f a b) :
    BoundsQuadrature.DyadicData (LipschitzIntegralBounds.onInterval f a b) :=
  LipschitzIntegralBounds.dyadicData f a b D.constant D.ordered D.lipschitz D.nonnegative

def Data.tests {f : Rat → Value} {a b : Rat} (D : Data f a b) (n : Nat) :
    Bounds (LipschitzIntegralBounds.onInterval f a b) :=
  D.dyadic.tests n

theorem Data.tests_shrink {f : Rat → Value} {a b : Rat} (D : Data f a b) :
    ShrinksToZero (fun n => (D.tests n).upperSum-(D.tests n).lowerSum) :=
  D.dyadic.shrinks

def Data.integral {f : Rat → Value} {a b : Rat} (D : Data f a b) : RealCompute :=
  if a=b then RealCompute.ofRat 0 else
    D.dyadic.integral

private theorem zero_sums (f : Rat → Value) (a : Rat)
    (B : Bounds (LipschitzIntegralBounds.onInterval f a a)) : B.lowerSum=0 ∧ B.upperSum=0 := by
  have point (k : Nat) (hk : k≤B.partition.pieces) : B.partition.point k=a := by
    have H := B.partition.point_in_bounds hk
    change a≤B.partition.point k ∧ B.partition.point k≤a at H
    grind only
  have zero (w : Nat → Rat) :
      rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*w k) B.partition.pieces=0 := by
    have H : rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*w k) B.partition.pieces=
        rectangleSum (fun _ => 0) B.partition.pieces := by
      apply rectangleSum_congr
      intro k hk
      rw [point k (by omega),point (k+1) (by omega),Rat.sub_self,Rat.zero_mul]
    rw [H,rectangleSum_zero]
  exact ⟨zero B.lower,zero B.upper⟩

theorem Data.hasIntegral {f : Rat → Value} {a b : Rat} (D : Data f a b) :
    HasIntegral (LipschitzIntegralBounds.onInterval f a b) D.integral := by
  by_cases h : a=b
  · subst b
    simp only [Data.integral]
    refine ⟨RealCompute.ofRat_valid 0,?_,LipschitzIntegralBounds.tight f a a D.constant D.ordered D.lipschitz D.nonnegative⟩
    intro B n
    have H := zero_sums f a B
    change B.lowerSum≤0 ∧ 0≤B.upperSum
    rw [H.1,H.2]
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  · simp only [Data.integral,if_neg h]
    exact D.dyadic.hasIntegral

def Data.value {f : Rat → Value} {a b : Rat} (D : Data f a b) : Value :=
  parameter D.integral D.hasIntegral.valid

theorem Data.identify {f : Rat → Value} {a b : Rat} (D : Data f a b) {I : RealCompute}
    (hI : HasIntegral (LipschitzIntegralBounds.onInterval f a b) I) : D.integral.Equiv I :=
  D.hasIntegral.unique hI

def Data.restrict {f : Rat → Value} {a b : Rat} (D : Data f a b)
    (u v : Rat) (hu : a≤u) (huv : u≤v) (hv : v≤b) : Data f u v where
  ordered := huv
  constant := D.constant
  nonnegative := D.nonnegative
  lipschitz x y hx hxy hy := D.lipschitz x y (Rat.le_trans hu hx) hxy (Rat.le_trans hy hv)

def Data.add {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b) :
    Data (fun t => Value.add (f t) (g t)) a b where
  ordered := D.ordered
  constant := D.constant+E.constant
  nonnegative := Rat.add_nonneg D.nonnegative E.nonnegative
  lipschitz := by
    intro u v hu huv hv
    have H := (D.lipschitz u v hu huv hv).add (E.lipschitz u v hu huv hv)
    have he : D.constant*(v-u)+E.constant*(v-u)=(D.constant+E.constant)*(v-u) := by grind only
    rw [he] at H
    apply H.congr
    apply arithmetic_identity; intro s; simp only [Value.add,sub]; grind only

def Data.scale {f : Rat → Value} {a b : Rat} (D : Data f a b) (c : Rat) :
    Data (fun t => RealApproximationOrder.scale c (f t)) a b where
  ordered := D.ordered
  constant := qabs c*D.constant
  nonnegative := Rat.mul_nonneg (qabs_nonneg c) D.nonnegative
  lipschitz := by
    intro u v hu huv hv
    have H := FTCRealCalculus.scale_small (D.lipschitz u v hu huv hv) c
    have he : qabs c*(D.constant*(v-u))=(qabs c*D.constant)*(v-u) := by grind only
    rw [he] at H
    apply H.congr
    apply arithmetic_identity; intro s; simp only [RealApproximationOrder.scale,sub]; grind only

def Data.neg {f : Rat → Value} {a b : Rat} (D : Data f a b) : Data (fun t => Value.neg (f t)) a b where
  ordered := D.ordered
  constant := D.constant
  nonnegative := D.nonnegative
  lipschitz := by
    intro u v hu huv hv
    apply (D.lipschitz u v hu huv hv).neg.congr
    apply arithmetic_identity; intro s; simp only [Value.neg,sub]; grind only

def Data.subtract {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b) :
    Data (fun t => sub (f t) (g t)) a b where
  ordered := D.ordered
  constant := D.constant+E.constant
  nonnegative := Rat.add_nonneg D.nonnegative E.nonnegative
  lipschitz := by
    intro u v hu huv hv
    have H := (D.lipschitz u v hu huv hv).add (E.lipschitz u v hu huv hv).neg
    have he : D.constant*(v-u)+E.constant*(v-u)=(D.constant+E.constant)*(v-u) := by grind only
    rw [he] at H
    apply H.congr
    apply arithmetic_identity; intro s; simp only [Value.add,Value.neg,sub]; grind only

theorem Data.small {f : Rat → Value} {a b : Rat} (D : Data f a b) (B : Rat)
    (hB : ∀ t,a≤t → t≤b → Small (f t) B) : Small D.value ((b-a)*B) := by
  have hl := D.hasIntegral.lower_bound (-B) (fun t ht n => (hB t ht.1 ht.2).1 0 n)
  have hu := D.hasIntegral.upper_bound B (fun t ht n => (hB t ht.1 ht.2).2 n 0)
  constructor
  · intro i j
    have h := hl 0 j
    change (b-a)*(-B)≤(D.integral.compute j).hi at h
    change -((b-a)*B)≤(D.integral.compute j).hi
    grind only
  · exact hu

/-- The algorithmic choices disappear from the public integral law. -/
theorem Data.add_identity {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b) :
    (D.add E).integral.Equiv (D.integral+E.integral) :=
  D.hasIntegral.add_identity E.hasIntegral (D.add E).hasIntegral rfl rfl rfl rfl
    (by intro t _ _ _; exact RealCompute.equiv_refl _ (Value.add (f t) (g t)).real.valid)

def Data.mul {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b)
    (B C : Rat) (hB : 0≤B) (hC : 0≤C)
    (bf : ∀ t,a≤t → t≤b → Small (f t) B)
    (bg : ∀ t,a≤t → t≤b → Small (g t) C) : Data (fun t => Value.mul (f t) (g t)) a b where
  ordered := D.ordered
  constant := D.constant*C+B*E.constant
  nonnegative := Rat.add_nonneg (Rat.mul_nonneg D.nonnegative hC) (Rat.mul_nonneg hB E.nonnegative)
  lipschitz := FTCRealCalculus.product_lipschitz f g a b D.constant E.constant B C D.lipschitz E.lipschitz bf bg

theorem Data.congr {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b)
    (he : ∀ t,a≤t → t≤b → (f t).real.preferred.Equiv (g t).real.preferred) : D.integral.Equiv E.integral :=
  (D.hasIntegral.congrFunction (G := LipschitzIntegralBounds.onInterval g a b) ⟨rfl,rfl,fun t ht _ => he t ht.1 ht.2⟩).unique E.hasIntegral

theorem Data.scale_identity {f : Rat → Value} {a b : Rat} (D : Data f a b) (c : Rat) :
    (D.scale c).integral.Equiv (RealCompute.scaleRat c D.integral) :=
  D.hasIntegral.scaleRat_identity (D.scale c).hasIntegral c ⟨rfl,rfl,by
    intro t _ _
    exact RealCompute.equiv_refl _ (RealApproximationOrder.scale c (f t)).real.valid⟩

theorem Data.neg_identity {f : Rat → Value} {a b : Rat} (D : Data f a b) :
    D.neg.integral.Equiv (-D.integral) := by
  have H := (D.scale (-1)).congr D.neg (by
    intro t _ _
    apply arithmetic_identity; intro s; simp only [RealApproximationOrder.scale,Value.neg]; grind only)
  have S := D.scale_identity (-1)
  have C : (RealCompute.scaleRat (-1) D.integral).Equiv (-D.integral) := by
    apply arithmetic_identity (RealApproximationOrder.scale (-1) D.value) (Value.neg D.value)
    intro s; simp only [RealApproximationOrder.scale,Value.neg]; grind only
  exact RealCompute.equiv_trans D.neg.hasIntegral.valid (D.scale (-1)).hasIntegral.valid
    (RealCompute.neg_valid D.hasIntegral.valid) (RealCompute.equiv_symm H)
    (RealCompute.equiv_trans (D.scale (-1)).hasIntegral.valid (RealCompute.scaleRat_valid D.hasIntegral.valid)
      (RealCompute.neg_valid D.hasIntegral.valid) S C)

theorem Data.subtract_identity {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b) :
    (D.subtract E).integral.Equiv (D.integral-E.integral) := by
  have H := (D.add E.neg).congr (D.subtract E) (by
    intro t _ _
    apply arithmetic_identity; intro s; simp only [Value.add,Value.neg,sub]; grind only)
  have S := (D.add_identity E.neg)
  have A := RealCompute.add_equiv D.hasIntegral.valid D.hasIntegral.valid E.neg.hasIntegral.valid
    (RealCompute.neg_valid E.hasIntegral.valid) (RealCompute.equiv_refl _ D.hasIntegral.valid) E.neg_identity
  have C : (D.integral+(-E.integral)).Equiv (D.integral-E.integral) := by
    apply arithmetic_identity (Value.add D.value (Value.neg E.value)) (sub D.value E.value)
    intro s; simp only [Value.add,Value.neg,sub]; grind only
  exact RealCompute.equiv_trans (D.subtract E).hasIntegral.valid (D.add E.neg).hasIntegral.valid
    (RealCompute.sub_valid D.hasIntegral.valid E.hasIntegral.valid) (RealCompute.equiv_symm H)
    (RealCompute.equiv_trans (D.add E.neg).hasIntegral.valid (RealCompute.add_valid D.hasIntegral.valid E.neg.hasIntegral.valid)
      (RealCompute.sub_valid D.hasIntegral.valid E.hasIntegral.valid) S
      (RealCompute.equiv_trans (RealCompute.add_valid D.hasIntegral.valid E.neg.hasIntegral.valid)
        (RealCompute.add_valid D.hasIntegral.valid (RealCompute.neg_valid E.hasIntegral.valid))
        (RealCompute.sub_valid D.hasIntegral.valid E.hasIntegral.valid) A C))

theorem Data.difference_small {f g : Rat → Value} {a b : Rat} (D : Data f a b) (E : Data g a b)
    (B : Rat) (hb : ∀ t,a≤t → t≤b → Small (sub (f t) (g t)) B) :
    Small (sub D.value E.value) ((b-a)*B) :=
  ((D.subtract E).small B hb).congr (D.subtract_identity E)

/-- Interval additivity for independently computed compact quadratures. -/
theorem Data.append {f : Rat → Value} {a b c : Rat}
    (D : Data f a b) (E : Data f b c) (F : Data f a c) :
    F.integral.Equiv (D.integral+E.integral) := by
  let G := LipschitzIntegralBounds.onInterval f a c
  have hD : HasIntegral (G.restrict a b Rat.le_refl D.ordered E.ordered) D.integral :=
    D.hasIntegral.congrFunction (G := G.restrict a b Rat.le_refl D.ordered E.ordered)
      ⟨rfl,rfl,by intro t _ _ n; exact (RealCompute.equiv_refl (f t).real.preferred (f t).real.valid) n⟩
  have hE : HasIntegral (G.restrict b c D.ordered E.ordered Rat.le_refl) E.integral :=
    E.hasIntegral.congrFunction (G := G.restrict b c D.ordered E.ordered Rat.le_refl)
      ⟨rfl,rfl,by intro t _ _ n; exact (RealCompute.equiv_refl (f t).real.preferred (f t).real.valid) n⟩
  exact HasIntegral.append_identity (F := G) b D.ordered E.ordered hD hE F.hasIntegral

/-- Positive affine substitution for independently computed integrals.
The argument transports the source rectangle tests with their exact lengths. -/
theorem Data.affine_identity {f g : Rat → Value} {a b u v c s : Rat}
    (F : Data f a b) (G : Data g u v) (hs : 0 < s)
    (hu : u = c + s * a) (hv : v = c + s * b)
    (h : ∀ t, a ≤ t → t ≤ b → (f t).real.preferred.Equiv (g (c + s * t)).real.preferred) :
    G.integral.Equiv (RealCompute.scaleRat s F.integral) := by
  let transport (B : Bounds (LipschitzIntegralBounds.onInterval f a b)) :
      Bounds (LipschitzIntegralBounds.onInterval g u v) := by
    let P := B.partition
    let Q : RationalPartition u v :=
      { pieces := P.pieces
        positive := P.positive
        point := fun k => c + s * P.point k
        left_endpoint := by rw [P.left_endpoint]; exact hu.symm
        right_endpoint := by rw [P.right_endpoint]; exact hv.symm
        monotone := by
          intro i j hij hj
          have hmul := Rat.mul_le_mul_of_nonneg_left (P.monotone i j hij hj) (Rat.le_of_lt hs)
          grind only }
    have hinv := Rat.mul_inv_cancel s (Rat.ne_of_gt hs)
    have invpos := Rat.le_of_lt (Rat.inv_pos.mpr hs)
    have preimage (k : Nat) (hk : k < P.pieces) (x : Rat)
        (hx : (Q.cell k hk).contains x) : (P.cell k hk).contains ((x - c) / s) := by
      change c + s * P.point k ≤ x ∧ x ≤ c + s * P.point (k+1) at hx
      have hl := Rat.mul_le_mul_of_nonneg_right hx.1 invpos
      have hr := Rat.mul_le_mul_of_nonneg_right hx.2 invpos
      have he (t : Rat) : (c + s * t) * s⁻¹ = c * s⁻¹ + t := by grind only
      rw [he] at hl hr
      change P.point k ≤ (x-c)/s ∧ (x-c)/s ≤ P.point (k+1)
      constructor <;> grind only [Rat.div_def]
    have eqAt (k : Nat) (hk : k < P.pieces) (x : Rat)
        (hx : (P.cell k hk).contains ((x - c) / s)) :
        (f ((x - c) / s)).real.preferred.Equiv (g x).real.preferred := by
      have hh := (P.cell k hk).contains_inDomain hx
      have he : c + s * ((x - c) / s) = x := by grind only [Rat.div_def]
      simpa only [he] using h ((x - c) / s) hh.1 hh.2
    exact
      { partition := Q
        lower := B.lower
        upper := B.upper
        lower_le := by
          intro k hk x hx n
          have ht := preimage k hk x hx
          have he := RealCompute.le_of_equiv (f ((x-c)/s)).real.valid (g x).real.valid (eqAt k hk x ht)
          have hb : (RealCompute.ofRat (B.lower k)).Le (f ((x-c)/s)).real.preferred :=
            fun _ j => B.lower_le k hk _ ht j
          exact RealCompute.le_trans (f ((x-c)/s)).real.valid hb he 0 n
        upper_ge := by
          intro k hk x hx n
          have ht := preimage k hk x hx
          have he := RealCompute.le_of_equiv (g x).real.valid (f ((x-c)/s)).real.valid
            (RealCompute.equiv_symm (eqAt k hk x ht))
          have hb : (f ((x-c)/s)).real.preferred.Le (RealCompute.ofRat (B.upper k)) :=
            fun j _ => B.upper_ge k hk _ ht j
          exact RealCompute.le_trans (f ((x-c)/s)).real.valid he hb n 0 }
  have sums (B : Bounds (LipschitzIntegralBounds.onInterval f a b)) :
      (transport B).lowerSum = s * B.lowerSum ∧ (transport B).upperSum = s * B.upperSum := by
    have sum (w : Nat → Rat) :
        rectangleSum (fun k => ((c + s * B.partition.point (k+1)) -
          (c + s * B.partition.point k)) * w k) B.partition.pieces =
        s * rectangleSum (fun k => (B.partition.point (k+1) - B.partition.point k) * w k)
          B.partition.pieces := by
      rw [Rat.mul_comm, ← rectangleSum_scale]
      apply rectangleSum_congr
      intro k _
      grind only
    exact ⟨sum B.lower, sum B.upper⟩
  let J := RealCompute.scaleRat s F.integral
  have encloses (B : Bounds (LipschitzIntegralBounds.onInterval f a b)) (n : Nat) :
      (transport B).lowerSum ≤ (J.compute n).hi ∧ (J.compute n).lo ≤ (transport B).upperSum := by
    obtain ⟨hl, hr⟩ := F.hasIntegral.bounds B n
    rw [(sums B).1, (sums B).2]
    change _ ≤ (RealCompute.scaleRatCompute s F.integral n).hi ∧
      (RealCompute.scaleRatCompute s F.integral n).lo ≤ _
    simp only [RealCompute.scaleRatCompute, if_pos (Rat.le_of_lt hs)]
    exact ⟨Rat.mul_le_mul_of_nonneg_left hl (Rat.le_of_lt hs),
      Rat.mul_le_mul_of_nonneg_left hr (Rat.le_of_lt hs)⟩
  apply equiv_of_bounds G.hasIntegral.tight G.hasIntegral.bounds
  intro A n
  have cross (B : Bounds (LipschitzIntegralBounds.onInterval f a b)) :
      A.lowerSum ≤ (J.compute n).hi + ((transport B).upperSum - (transport B).lowerSum) ∧
      (J.compute n).lo ≤ A.upperSum + ((transport B).upperSum - (transport B).lowerSum) := by
    have hl := Bounds.lowerSum_le_upperSum A (transport B)
    have hr := Bounds.lowerSum_le_upperSum (transport B) A
    obtain ⟨hJ₁, hJ₂⟩ := encloses B n
    constructor <;> grind only
  have arbitrarily (eps : QPos) : ∃ B : Bounds (LipschitzIntegralBounds.onInterval f a b),
      (transport B).upperSum - (transport B).lowerSum ≤ eps.val := by
    have hp : 0 < eps.val / s := Rat.mul_pos eps.property (Rat.inv_pos.mpr hs)
    obtain ⟨B, hB⟩ := F.hasIntegral.tight ⟨_, hp⟩
    have hh := Rat.mul_le_mul_of_nonneg_right hB (Rat.le_of_lt hs)
    change (B.upperSum - B.lowerSum) * s ≤ (eps.val / s) * s at hh
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hs)] at hh
    exact ⟨B, by rw [(sums B).1, (sums B).2]; grind only⟩
  constructor
  · by_cases hn : A.lowerSum ≤ (J.compute n).hi
    · exact hn
    exfalso
    obtain ⟨B, hb⟩ := arbitrarily ⟨(A.lowerSum - (J.compute n).hi) / 2, by grind only⟩
    have := (cross B).1
    change _ ≤ (A.lowerSum - (J.compute n).hi) / 2 at hb
    grind only
  · by_cases hn : (J.compute n).lo ≤ A.upperSum
    · exact hn
    exfalso
    obtain ⟨B, hb⟩ := arbitrarily ⟨((J.compute n).lo - A.upperSum) / 2, by grind only⟩
    have := (cross B).2
    change _ ≤ ((J.compute n).lo - A.upperSum) / 2 at hb
    grind only

/-- Integrate the derivative along the straight segment from zero to `x`.
This computes the divided difference even when the segment has length zero. -/
private def Data.segmentData {d : Rat → Value} {a b : Rat} (D : Data d a b)
    (x : Rat) (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b) : Data (fun t => d (x * t)) 0 1 where
  ordered := by decide
  constant := D.constant * qabs x
  nonnegative := Rat.mul_nonneg D.nonnegative (qabs_nonneg x)
  lipschitz := by
    intro u v hu huv hv
    have inside (t : Rat) (ht : 0 ≤ t) (ht' : t ≤ 1) : a ≤ x * t ∧ x * t ≤ b := by
      by_cases h : 0 ≤ x
      · have h₁ := Rat.mul_nonneg h ht
        have h₂ := Rat.mul_le_mul_of_nonneg_left ht' h
        constructor <;> grind only
      · have h₁ := Rat.mul_nonneg (show 0 ≤ -x by grind only) ht
        have h₂ := Rat.mul_le_mul_of_nonneg_left ht' (show 0 ≤ -x by grind only)
        constructor <;> grind only
    have iu := inside u hu (by grind only)
    have iv := inside v (by grind only) hv
    by_cases h : 0 ≤ x
    · have h' := Rat.mul_le_mul_of_nonneg_left huv h
      have H := D.lipschitz _ _ iu.1 h' iv.2
      simpa only [qabs_eq_self_of_nonneg h, show x * v - x * u = x * (v - u) by grind only,
        Rat.mul_assoc] using H
    · have hx' : x ≤ 0 := by grind only
      have h' := Rat.mul_le_mul_of_nonneg_left huv (show 0 ≤ -x by grind only)
      have H := (D.lipschitz _ _ iv.1 (show x * v ≤ x * u by grind only) iu.2).neg
      rw [show D.constant * (x * u - x * v) = D.constant * qabs x * (v-u) by
        rw [qabs_eq_neg_of_nonpos hx']; grind only] at H
      exact H.congr (arithmetic_identity _ _ (by
        intro s
        simp only [Value.neg, sub]
        grind only))

/-- The normalized average of the derivative from zero to `x`.
For negative `x` the parameter traverses the segment in increasing order. -/
def Data.ftcQuotient {d : Rat → Value} {a b : Rat} (D : Data d a b)
    (x : Rat) (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b) :
    Data (fun t => d (if 0 ≤ x then x * t else x * (1 - t))) 0 1 where
  ordered := by decide
  constant := D.constant * qabs x
  nonnegative := Rat.mul_nonneg D.nonnegative (qabs_nonneg x)
  lipschitz := by
    intro u v hu huv hv
    let E := D.segmentData x hx h0
    by_cases hp : 0 ≤ x
    · have H := E.lipschitz u v hu huv hv
      change Small (sub (d (x * v)) (d (x * u))) (D.constant * qabs x * (v-u)) at H
      simpa only [if_pos hp] using H
    · have H := (E.lipschitz (1-v) (1-u) (by grind only) (by grind only) (by grind only)).neg
      rw [show (1-u)-(1-v)=v-u by grind only] at H
      simp only [if_neg hp]
      exact H.congr (arithmetic_identity _ _ (by
        intro s
        simp only [Value.neg, sub]
        grind only))

theorem Data.ftcQuotient_zero {d : Rat → Value} {a b : Rat} (D : Data d a b)
    (h0 : a ≤ 0 ∧ 0 ≤ b) :
    (D.ftcQuotient 0 h0 h0).integral.Equiv (d 0).real.preferred := by
  let Q := D.ftcQuotient 0 h0 h0
  have h := Integral.constant_hasIntegral (d 0).real.preferred (d 0).real.valid 0 1 Q.ordered
  have hh := Q.identify (h.congrFunction
    (G := LipschitzIntegralBounds.onInterval (fun t => d (if 0 ≤ (0 : Rat) then 0*t else 0*(1-t))) 0 1)
    ⟨rfl, rfl, fun t _ _ => by
      change (d 0).real.preferred.Equiv (d (if 0 ≤ (0 : Rat) then 0*t else 0*(1-t))).real.preferred
      rw [if_pos (Rat.le_refl : (0 : Rat) ≤ 0), Rat.zero_mul]
      exact RealCompute.equiv_refl _ (d 0).real.valid⟩)
  have he : (RealApproximationOrder.scale ((1 : Rat) - 0) (d 0)).real.preferred.Equiv (d 0).real.preferred := by
    apply arithmetic_identity
    intro s
    simp only [RealApproximationOrder.scale]
    grind only
  exact RealCompute.equiv_trans Q.hasIntegral.valid h.valid (d 0).real.valid hh he

/-- The FTC identifies the integral quotient with the increment after
multiplication by `x`, for positive, negative and zero arguments. -/
theorem Data.ftcQuotient_identity {f d : Rat → Value} {a b : Rat}
    (D : Data d a b) (S : FTCRealCalculus.Step f d a b) (x : Rat)
    (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b) :
    (RealApproximationOrder.scale x (D.ftcQuotient x hx h0).value).real.preferred.Equiv (sub (f x) (f 0)).real.preferred := by
  let Q := D.ftcQuotient x hx h0
  by_cases hp : 0 < x
  · let F := D.restrict 0 x h0.1 (Rat.le_of_lt hp) hx.2
    have h := Q.affine_identity F (c := 0) hp (by grind only) (by grind only) (fun t _ _ => by
      rw [Rat.zero_add, if_pos (Rat.le_of_lt hp)]
      exact RealCompute.equiv_refl _ (d (x*t)).real.valid)
    exact RealCompute.equiv_trans (RealApproximationOrder.scale x Q.value).real.valid F.hasIntegral.valid
      (sub (f x) (f 0)).real.valid (RealCompute.equiv_symm h)
      ((S.restrict 0 x h0.1 hx.2).ftc F.hasIntegral)
  · by_cases hn : x < 0
    · let F := D.restrict x 0 hx.1 (Rat.le_of_lt hn) h0.2
      have h := Q.affine_identity F (c := x) (s := -x) (by grind only)
        (by grind only) (by grind only) (fun t _ _ => by
          simp only [if_neg (show ¬ 0 ≤ x by grind only),
            show x * (1-t) = x + -x*t by grind only]
          exact RealCompute.equiv_refl _ (d (x + -x*t)).real.valid)
      have h' := (S.restrict x 0 hx.1 h0.2).ftc F.hasIntegral
      have he : (RealApproximationOrder.scale (-x) Q.value).real.preferred.Equiv (sub (f 0) (f x)).real.preferred :=
        RealCompute.equiv_trans (RealApproximationOrder.scale (-x) Q.value).real.valid F.hasIntegral.valid
          (sub (f 0) (f x)).real.valid (RealCompute.equiv_symm h) h'
      have hneg := RealCompute.neg_equiv he
      have hl : (RealApproximationOrder.scale x Q.value).real.preferred.Equiv (Value.neg (RealApproximationOrder.scale (-x) Q.value)).real.preferred := by
        apply arithmetic_identity
        intro s
        simp only [RealApproximationOrder.scale, Value.neg]
        grind only
      have hr : (Value.neg (sub (f 0) (f x))).real.preferred.Equiv (sub (f x) (f 0)).real.preferred := by
        apply arithmetic_identity
        intro s
        simp only [sub, Value.neg]
        grind only
      exact RealCompute.equiv_trans (RealApproximationOrder.scale x Q.value).real.valid (Value.neg (RealApproximationOrder.scale (-x) Q.value)).real.valid
        (sub (f x) (f 0)).real.valid hl
        (RealCompute.equiv_trans (Value.neg (RealApproximationOrder.scale (-x) Q.value)).real.valid
          (Value.neg (sub (f 0) (f x))).real.valid (sub (f x) (f 0)).real.valid hneg hr)
    · have he : x = 0 := by grind only
      subst x
      apply arithmetic_identity
      intro s
      simp only [RealApproximationOrder.scale, sub, Rat.zero_mul, Rat.sub_self]

/-- The quotient approaches the supplied derivative at zero with an
explicit error, on either side of zero. -/
theorem Data.ftcQuotient_error {d : Rat → Value} {a b : Rat} (D : Data d a b)
    (x : Rat) (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b) :
    Small (sub (D.ftcQuotient x hx h0).value (d 0)) (D.constant * qabs x) := by
  let Q := D.ftcQuotient x hx h0
  have H (t : Rat) (ht : 0 ≤ t) (ht' : t ≤ 1) :
      Small (sub (d (if 0 ≤ x then x*t else x*(1-t))) (d 0)) (D.constant * qabs x) := by
    by_cases hp : 0 ≤ x
    · rw [if_pos hp, qabs_eq_self_of_nonneg hp]
      have hl := Rat.mul_nonneg hp ht
      have hr := Rat.mul_le_mul_of_nonneg_left ht' hp
      have hd := D.lipschitz 0 (x*t) h0.1 hl (by grind only)
      apply hd.mono
      exact Rat.mul_le_mul_of_nonneg_left (by grind only) D.nonnegative
    · have hn : x ≤ 0 := by grind only
      have hl := Rat.mul_nonneg (show 0 ≤ -x by grind only) (show 0 ≤ 1-t by grind only)
      have hr := Rat.mul_le_mul_of_nonneg_left (show 1-t ≤ 1 by grind only) (show 0 ≤ -x by grind only)
      rw [if_neg hp, qabs_eq_neg_of_nonpos hn]
      have hd := (D.lipschitz (x*(1-t)) 0 (by grind only) (by grind only) h0.2).neg
      apply (hd.mono (Rat.mul_le_mul_of_nonneg_left (show 0-x*(1-t) ≤ -x by grind only)
        D.nonnegative)).congr
      apply arithmetic_identity
      intro s
      simp only [sub, Value.neg]
      grind only
  have he := D.ftcQuotient_zero h0
  have hh := Q.difference_small (D.ftcQuotient 0 h0 h0) (D.constant * qabs x) (by
    intro t ht hu
    change Small (sub (d (if 0 ≤ x then x*t else x*(1-t)))
      (d (if 0 ≤ (0 : Rat) then 0*t else 0*(1-t)))) _
    rw [if_pos (Rat.le_refl : (0 : Rat) ≤ 0), Rat.zero_mul]
    exact H t ht hu)
  have h := hh.congr (y := sub Q.value (d 0))
    (RealCompute.sub_equiv Q.hasIntegral.valid Q.hasIntegral.valid
    (D.ftcQuotient 0 h0 h0).hasIntegral.valid (d 0).real.valid
    (RealCompute.equiv_refl _ Q.hasIntegral.valid) he)
  rwa [show (1 : Rat) - 0 = 1 by grind only, Rat.one_mul] at h

/-- Melrose's division step for a normalized profile. The input profile
can be the Gaussian once its finite FTC evidence is supplied. -/
theorem Data.ftcQuotient_decomposition {f g d : Rat → Value} {a b : Rat}
    (D : Data d a b)
    (S : FTCRealCalculus.Step (fun t => sub (f t) (Value.mul (f 0) (g t))) d a b)
    (x : Rat) (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b)
    (hg : (g 0).real.preferred.Equiv (RealCompute.ofRat 1)) :
    (Value.add (Value.mul (f 0) (g x))
      (RealApproximationOrder.scale x (D.ftcQuotient x hx h0).value)).real.preferred.Equiv
      (f x).real.preferred := by
  let w := fun t => sub (f t) (Value.mul (f 0) (g t))
  let Q := RealApproximationOrder.scale x (D.ftcQuotient x hx h0).value
  let G := Value.mul (f 0) (g x)
  have hzero : (w 0).real.preferred.Equiv (RealCompute.ofRat 0) := by
    have hp := RealCompute.mul_equiv (y' := RealCompute.ofRat 1) (f 0).real.valid (f 0).real.valid (g 0).real.valid
      (RealCompute.ofRat_valid 1) (RealCompute.equiv_refl _ (f 0).real.valid) hg
    have he : (Value.mul (f 0) (Value.rational 1)).real.preferred.Equiv (f 0).real.preferred :=
      arithmetic_identity _ _ (by intro s; simp only [Value.mul, Value.rational, Rat.mul_one])
    have hp' := RealCompute.equiv_trans (Value.mul (f 0) (g 0)).real.valid
      (Value.mul (f 0) (Value.rational 1)).real.valid (f 0).real.valid hp he
    exact RealCompute.equiv_trans (w 0).real.valid (sub (f 0) (f 0)).real.valid (RealCompute.ofRat_valid 0)
      (RealCompute.sub_equiv (f 0).real.valid (f 0).real.valid (Value.mul (f 0) (g 0)).real.valid
        (f 0).real.valid (RealCompute.equiv_refl _ (f 0).real.valid) hp')
      (RealCompute.sub_self_equiv_zero (f 0).real.valid)
  have h := D.ftcQuotient_identity S x hx h0
  have hs := RealCompute.sub_equiv (y' := RealCompute.ofRat 0) (w x).real.valid (w x).real.valid (w 0).real.valid
    (RealCompute.ofRat_valid 0) (RealCompute.equiv_refl _ (w x).real.valid) hzero
  have hr : (Value.add G (sub (w x) (Value.rational 0))).real.preferred.Equiv (f x).real.preferred := by
    apply arithmetic_identity
    intro s
    simp only [w, G, Value.add, Value.rational, sub]
    grind only
  refine RealCompute.equiv_trans (Value.add G Q).real.valid
    (Value.add G (sub (w x) (Value.rational 0))).real.valid (f x).real.valid ?_ hr
  apply RealCompute.add_equiv G.real.valid G.real.valid Q.real.valid
    (sub (w x) (Value.rational 0)).real.valid (RealCompute.equiv_refl _ G.real.valid)
  exact RealCompute.equiv_trans Q.real.valid (sub (w x) (w 0)).real.valid
    (sub (w x) (Value.rational 0)).real.valid h hs


/-- Division gains one power of decay away from zero. The quotient itself
continues to be computed by the normalized derivative integral. -/
theorem Data.ftcQuotient_decay {w d : Rat → Value} {a b : Rat}
    (D : Data d a b) (S : FTCRealCalculus.Step w d a b)
    (x : Rat) (hx : a ≤ x ∧ x ≤ b) (h0 : a ≤ 0 ∧ 0 ≤ b)
    (hz : (w 0).real.preferred.Equiv (RealCompute.ofRat 0)) (hne : x ≠ 0)
    (B : Rat) (hw : Small (w x) B) :
    Small (D.ftcQuotient x hx h0).value (B / qabs x) := by
  let Q := (D.ftcQuotient x hx h0).value
  have he := D.ftcQuotient_identity S x hx h0
  have hs : (sub (w x) (w 0)).real.preferred.Equiv (w x).real.preferred := by
    have h := RealCompute.sub_equiv (y' := RealCompute.ofRat 0) (w x).real.valid (w x).real.valid
      (w 0).real.valid (RealCompute.ofRat_valid 0) (RealCompute.equiv_refl _ (w x).real.valid) hz
    exact RealCompute.equiv_trans (sub (w x) (w 0)).real.valid
      (sub (w x) (Value.rational 0)).real.valid (w x).real.valid h
      (arithmetic_identity _ _ (by intro s; simp only [sub, Value.rational]; grind only))
  have h := hw.congr (y := RealApproximationOrder.scale x Q)
    (RealCompute.equiv_symm (RealCompute.equiv_trans (RealApproximationOrder.scale x Q).real.valid
      (sub (w x) (w 0)).real.valid (w x).real.valid he hs))
  have hi : qabs x⁻¹ = (qabs x)⁻¹ := by
    have hm := Rat.inv_mul_cancel x hne
    have hq := congrArg qabs hm
    rw [qabs_mul, show qabs (1 : Rat) = 1 by decide +kernel] at hq
    have hne' : qabs x ≠ 0 := by
      intro hh
      rw [hh, Rat.mul_zero] at hq
      exact (by decide : (0 : Rat) ≠ 1) hq
    calc
      _ = qabs x⁻¹ * (qabs x * (qabs x)⁻¹) := by rw [Rat.mul_inv_cancel _ hne', Rat.mul_one]
      _ = _ := by rw [← Rat.mul_assoc, hq, Rat.one_mul]
  have H := FTCRealCalculus.scale_small h x⁻¹
  rw [hi, show (qabs x)⁻¹ * B = B / qabs x by grind only [Rat.div_def]] at H
  exact H.congr (arithmetic_identity _ Q (by
    intro s
    simp only [RealApproximationOrder.scale]
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel x hne, Rat.one_mul]))


/-- A power of the unit-interval coordinate, used in the derivatives of the
FTC quotient. The Lipschitz constant is the exponent. -/
def unitPowerData (j : Nat) : Data (fun t => Value.rational (t^j)) 0 1 where
  ordered := by decide
  constant := j
  nonnegative := Rat.natCast_nonneg
  lipschitz := by
    have power (u v : Rat) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
        ∀ n : Nat, 0 ≤ v^n-u^n ∧ v^n-u^n ≤ (n : Rat)*(v-u) := by
      have hu₁ : u ≤ 1 := Rat.le_trans huv hv
      have hv₀ : 0 ≤ v := Rat.le_trans hu huv
      have unit (n : Nat) : u^n ≤ 1 := by
        induction n with
        | zero => rw [Rat.pow_zero]; exact Rat.le_refl
        | succ n ih =>
          rw [Rat.pow_succ]
          exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hu) (by simpa only [Rat.one_mul] using hu₁)
      intro n
      induction n with
      | zero => simp only [Rat.pow_zero]; grind only
      | succ n ih =>
        have h₁ := Rat.mul_le_mul_of_nonneg_right ih.2 hv₀
        have h₂ := Rat.mul_le_mul_of_nonneg_left hv
          (Rat.mul_nonneg (show (0 : Rat) ≤ (n : Rat) from Rat.natCast_nonneg) (show 0 ≤ v-u by grind only))
        have h₃ := Rat.mul_le_mul_of_nonneg_right (unit n) (show 0 ≤ v-u by grind only)
        have h₄ := Rat.mul_nonneg ih.1 hv₀
        have h₅ := Rat.mul_nonneg (Rat.pow_nonneg hu : 0 ≤ u^n) (show 0 ≤ v-u by grind only)
        rw [Rat.pow_succ, Rat.pow_succ, Rat.natCast_add]
        have he : v^n*v-u^n*u = (v^n-u^n)*v + u^n*(v-u) := by grind only
        rw [he]
        constructor <;> grind only
    intro u v hu huv hv
    have h := power u v hu huv hv j
    apply ((FTCRealCalculus.rational_small (v^j-u^j)).mono
      (by rw [qabs_eq_self_of_nonneg h.1]; exact h.2)).congr
    exact arithmetic_identity _ _ (fun _ => rfl)

theorem unitPower_small (j : Nat) (t : Rat) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    Small (Value.rational (t^j)) 1 := by
  apply (FTCRealCalculus.rational_small (t^j)).mono
  rw [qabs_eq_self_of_nonneg (Rat.pow_nonneg ht)]
  induction j with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ j ih =>
    rw [Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ht) (by simpa only [Rat.one_mul] using ht')

end ComputableAnalysis.LipschitzQuadrature


