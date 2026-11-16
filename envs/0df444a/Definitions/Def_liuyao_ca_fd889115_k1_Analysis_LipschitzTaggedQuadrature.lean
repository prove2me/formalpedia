-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzTaggedQuadrature
-- name    : liuyao_ca_fd889115_k1_Analysis_LipschitzTaggedQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:14:09.439824+00:00
-- url     : https://prove2.me/theorems/9459cc8c-472c-44e4-8d06-83d842062149
-- title:
--   Computable analysis · LipschitzTaggedQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/LipschitzTaggedQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EffectiveImproperIntegral

set_option autoImplicit true

/-! Actual represented tagged sums approximate the independent proper integral. -/
namespace ComputableAnalysis.LipschitzQuadrature
open ComputableCoefficient RealApproximationOrder FTCRealOrder FTCRealCalculus
set_option maxHeartbeats 800000
set_option autoImplicit false

def constantData (K : Value) (a b : Rat) (hab : a≤b) : Data (fun _ => K) a b where
  ordered := hab
  constant := 0
  nonnegative := by decide +kernel
  lipschitz := by
    intro u v _ _ _
    have H := rational_small 0
    rw [show qabs (0:Rat)=0 by decide +kernel] at H
    simp only [Rat.zero_mul]
    apply H.congr
    apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only

theorem constant_value (K : Value) (a b : Rat) (hab : a≤b) :
    Same (constantData K a b hab).value (RealApproximationOrder.scale (b-a) K) :=
  by
    have H := Integral.constant_hasIntegral K.real.preferred K.real.valid a b hab
    have H' : Integral.HasIntegral (LipschitzIntegralBounds.onInterval (fun _ => K) a b)
        (RealCompute.scaleRat (b-a) K.real.preferred) := H.congrFunction ⟨rfl,rfl,by
      intro t _ _
      exact RealCompute.equiv_refl _ K.real.valid⟩
    exact (constantData K a b hab).identify H' 

theorem Data.tag_error {f : Rat → Value} {a b : Rat} (D : Data f a b)
    (t : Rat) (ht : a≤t) (htb : t≤b) :
    Small (sub D.value (RealApproximationOrder.scale (b-a) (f t))) (D.constant*(b-a)*(b-a)) := by
  let C := constantData (f t) a b D.ordered
  have pointwise : ∀ q,a≤q → q≤b → Small (sub (f q) (f t)) (D.constant*(b-a)) := by
    intro q hq hqb
    by_cases h : t≤q
    · exact (D.lipschitz t q ht h hqb).mono (by
        have H := Rat.mul_le_mul_of_nonneg_left (show q-t≤b-a by grind only) D.nonnegative
        exact H)
    · have hqt : q≤t := by grind only
      have H := (D.lipschitz q t hq hqt htb).neg
      have A : Same (Value.neg (sub (f t) (f q))) (sub (f q) (f t)) := by
        apply arithmetic_identity; intro s; simp only [sub,Value.neg]; grind only
      exact (H.congr A).mono (by
        have H := Rat.mul_le_mul_of_nonneg_left (show t-q≤b-a by grind only) D.nonnegative
        exact H)
  have H := D.difference_small C (D.constant*(b-a)) pointwise
  have A : Same (sub D.value C.value) (sub D.value (RealApproximationOrder.scale (b-a) (f t))) :=
    (Same.refl D.value).sub (constant_value (f t) a b D.ordered)
  exact (H.congr A).mono (by grind only)

def taggedSum {a b : Rat} (f : Rat → Value) (P : RationalPartition a b) (tag : Nat → Rat) : Nat → Value
  | 0 => Value.rational 0
  | k+1 => Value.add (taggedSum f P tag k) (RealApproximationOrder.scale (P.point (k+1)-P.point k) (f (tag k)))

theorem zero_value {f : Rat → Value} {a : Rat} (D : Data f a a) : Same D.value (Value.rational 0) := by
  change D.integral.Equiv (RealCompute.ofRat 0)
  simp only [Data.integral]
  exact RealCompute.equiv_refl _ (RealCompute.ofRat_valid 0)

theorem zero_value_of_eq {f : Rat → Value} {a b : Rat} (D : Data f a b) (h : b=a) : Same D.value (Value.rational 0) := by
  subst b
  exact zero_value D

theorem Data.tagged_prefix_error {f : Rat → Value} {a b : Rat} (D : Data f a b)
    (P : RationalPartition a b) (tag : Nat → Rat) (h : Rat) (_hh : 0≤h)
    (width : ∀ k,k<P.pieces → P.point (k+1)-P.point k≤h)
    (tags : ∀ k,k<P.pieces → P.point k≤tag k ∧ tag k≤P.point (k+1))
    (k : Nat) (hk : k≤P.pieces) :
    Small (sub (D.restrict a (P.point k) Rat.le_refl (P.point_in_bounds hk).1 (P.point_in_bounds hk).2).value
      (taggedSum f P tag k)) (D.constant*(P.point k-a)*h) := by
  induction k with
  | zero =>
    simp only [P.left_endpoint,taggedSum]
    have Z := zero_value_of_eq (D.restrict a (P.point 0) Rat.le_refl (P.point_in_bounds hk).1 (P.point_in_bounds hk).2) P.left_endpoint
    have B := rational_small 0
    rw [show qabs (0:Rat)=0 by decide +kernel] at B
    have A : Same (sub (D.restrict a (P.point 0) Rat.le_refl (P.point_in_bounds hk).1 (P.point_in_bounds hk).2).value (Value.rational 0)) (Value.rational 0) := by
      apply ((Z.sub (Same.refl (Value.rational 0))).trans)
      apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only
    have E : D.constant*(a-a)*h=0 := by grind only
    rw [E]
    exact B.congr A.symm
  | succ k ih =>
    have hk' : k<P.pieces := by omega
    have hkle : k≤P.pieces := by omega
    have hstep := P.monotone k (k+1) (by omega) hk
    let L := D.restrict a (P.point k) Rat.le_refl (P.point_in_bounds hkle).1 (P.point_in_bounds hkle).2
    let U := D.restrict (P.point k) (P.point (k+1)) (P.point_in_bounds hkle).1 hstep (P.point_in_bounds hk).2
    let V := D.restrict a (P.point (k+1)) Rat.le_refl (P.point_in_bounds hk).1 (P.point_in_bounds hk).2
    have HU := U.tag_error (tag k) (tags k hk').1 (tags k hk').2
    have dw : 0≤P.point (k+1)-P.point k := by grind only
    have mult := Rat.mul_le_mul_of_nonneg_left (width k hk') (Rat.mul_nonneg D.nonnegative dw)
    have HU' : Small (sub U.value (RealApproximationOrder.scale (P.point (k+1)-P.point k) (f (tag k))))
        (D.constant*(P.point (k+1)-P.point k)*h) := HU.mono mult
    have H := (ih hkle).add HU'
    have S : Same V.value (Value.add L.value U.value) := L.append U V
    have A : Same (sub V.value (taggedSum f P tag (k+1)))
        (Value.add (sub L.value (taggedSum f P tag k))
          (sub U.value (RealApproximationOrder.scale (P.point (k+1)-P.point k) (f (tag k))))) := by
      apply (S.sub (Same.refl _)).trans
      apply arithmetic_identity; intro s; simp only [taggedSum,sub,Value.add]; grind only
    exact (H.congr A.symm).mono (by grind only)

theorem Data.tagged_error {f : Rat → Value} {a b : Rat} (D : Data f a b)
    (P : RationalPartition a b) (tag : Nat → Rat) (h : Rat) (hh : 0≤h)
    (width : ∀ k,k<P.pieces → P.point (k+1)-P.point k≤h)
    (tags : ∀ k,k<P.pieces → P.point k≤tag k ∧ tag k≤P.point (k+1)) :
    Small (sub D.value (taggedSum f P tag P.pieces)) (D.constant*(b-a)*h) := by
  have H := D.tagged_prefix_error P tag h hh width tags P.pieces (Nat.le_refl _)
  let E := D.restrict a (P.point P.pieces) Rat.le_refl (P.point_in_bounds (Nat.le_refl _)).1 (P.point_in_bounds (Nat.le_refl _)).2
  have HI : Integral.HasIntegral (LipschitzIntegralBounds.onInterval f a b) E.integral :=
    E.hasIntegral.congrFunction ⟨rfl,P.right_endpoint,by intro t _ _; exact RealCompute.equiv_refl _ (f t).real.valid⟩
  have B : Same E.value D.value := HI.unique D.hasIntegral
  have T := H.congr (B.sub (Same.refl (taggedSum f P tag P.pieces)))
  simpa only [P.right_endpoint] using T

def midpointTag (a b : Rat) (M k : Nat) : Rat := a+((k:Rat)+1/2)*mesh a b M

def midpointPrefix (f : Rat → Value) (a b : Rat) (M : Nat) : Nat → Value
  | 0 => Value.rational 0
  | k+1 => Value.add (midpointPrefix f a b M k) (RealApproximationOrder.scale (mesh a b M) (f (midpointTag a b M k)))

theorem Data.midpoint_error {f : Rat → Value} {a b : Rat} (D : Data f a b) (M : Nat) (hM : 0<M) :
    Small (sub D.value (midpointPrefix f a b M M)) (D.constant*(b-a)*mesh a b M) := by
  let P := RationalPartition.uniform a b M hM D.ordered
  let h := mesh a b M
  have nonnegative : 0≤h := (RationalPartition.uniform_maxStepAtMost_mesh a b M hM D.ordered).1
  have step (k : Nat) : P.point (k+1)-P.point k=h := by
    simp only [P,RationalPartition.uniform,leftPoint,Rat.natCast_add]
    change (a+((k:Rat)+1)*h)-(a+(k:Rat)*h)=h
    grind only
  have tags (k : Nat) (_hk : k<P.pieces) : P.point k≤midpointTag a b M k ∧ midpointTag a b M k≤P.point (k+1) := by
    simp only [P,RationalPartition.uniform,leftPoint,midpointTag,Rat.natCast_add]
    change a+(k:Rat)*h≤a+((k:Rat)+1/2)*h ∧ a+((k:Rat)+1/2)*h≤a+((k:Rat)+1)*h
    constructor <;> grind only
  have H := D.tagged_error P (midpointTag a b M) h nonnegative (fun k _ => by rw [step]; exact Rat.le_refl) tags
  have S (k : Nat) : taggedSum f P (midpointTag a b M) k=midpointPrefix f a b M k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [taggedSum,midpointPrefix,step,ih]; rfl
  rw [S] at H
  exact H


/-- A represented constant factors out of the proper integral. -/
theorem Data.mul_constant_identity {f : Rat → Value} {a b : Rat} (D : Data f a b)
    (c : Value) (B C : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : Small c C)
    (hf : ∀ t, a ≤ t → t ≤ b → Small (f t) B) :
    Same ((constantData c a b D.ordered).mul D C B hC hB (fun _ _ _ => hc) hf).value
      (Value.mul c D.value) := by
  let E := (constantData c a b D.ordered).mul D C B hC hB (fun _ _ _ => hc) hf
  have sums (M k : Nat) :
      Same (midpointPrefix (fun t => Value.mul c (f t)) a b M k)
        (Value.mul c (midpointPrefix f a b M k)) := by
    induction k with
    | zero => exact arithmetic_identity _ _ (by intro s; simp [midpointPrefix, Value.mul, Value.rational])
    | succ k ih =>
      refine (ih.add (Same.refl _)).trans ?_
      apply arithmetic_identity
      intro s
      simp only [midpointPrefix, Value.add, Value.mul, RealApproximationOrder.scale]
      grind only
  let A := (E.constant + C * D.constant) * (b-a) * (b-a)
  have hs : ShrinksToZero (fun n => A / ((n+1 : Nat) : Rat)) :=
    shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)
  have hz : Small (sub E.value (Value.mul c D.value)) 0 := by
    apply EffectiveImproperIntegral.small_of_errors _ 0 _ hs
    intro n
    let M := n+1
    have hM : 0 < M := by omega
    have h := (E.midpoint_error M hM).add (hc.mul (D.midpoint_error M hM).neg)
    have he : E.constant*(b-a)*mesh a b M + C*(D.constant*(b-a)*mesh a b M) =
        A / ((n+1 : Nat) : Rat) := by
      simp only [mesh, if_neg (Nat.ne_of_gt hM), A, M, Rat.div_def]
      grind only
    rw [he] at h
    rw [Rat.zero_add]
    refine (h.congr ((Same.refl E.value).sub (sums M M) |>.add (Same.refl _))).congr ?_
    apply arithmetic_identity
    intro s
    simp only [Value.add, Value.mul, Value.neg, sub]
    grind only
  exact small_sub_zero_same hz


private theorem midpoint_reflect (M k : Nat) (hM : 0 < M) (hk : k < M) :
    1 - midpointTag 0 1 M k = midpointTag 0 1 M (M-1-k) := by
  have hn : M-1-k+k+1=M := by omega
  have hcast := congrArg (fun n : Nat => (n : Rat)) hn
  simp only [Rat.natCast_add] at hcast
  have hi := Rat.mul_inv_cancel (M : Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  simp only [midpointTag, mesh, if_neg (Nat.ne_of_gt hM), Rat.zero_add, Rat.div_def]
  grind only

private theorem midpoint_reflected_sums (f : Rat → Value) (M : Nat) (hM : 0 < M) :
    Same (midpointPrefix (fun t => f (1-t)) 0 1 M M) (midpointPrefix f 0 1 M M) := by
  apply arithmetic_identity
  intro s
  let term := fun k => mesh 0 1 M * (f (midpointTag 0 1 M k)).sample s
  have direct (n : Nat) :
      (midpointPrefix f 0 1 M n).sample s = Integral.rectangleSum term n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [midpointPrefix, Integral.rectangleSum, Value.add, RealApproximationOrder.scale, ih]
      rfl
  have rev (n : Nat) (hn : n ≤ M) :
      (midpointPrefix (fun t => f (1-t)) 0 1 M n).sample s =
        Integral.rectangleSum term M - Integral.rectangleSum term (M-n) := by
    induction n with
    | zero => simp only [midpointPrefix, Value.rational, Nat.sub_zero, Rat.sub_self]
    | succ n ih =>
      have he : M-n = (M-(n+1))+1 := by omega
      have hi := ih (by omega)
      have hk := midpoint_reflect M n hM (by omega)
      simp only [midpointPrefix, Value.add, RealApproximationOrder.scale, hk, hi]
      rw [he, Integral.rectangleSum]
      rw [show M-1-n=M-(n+1) by omega]
      change Integral.rectangleSum term M -
        (Integral.rectangleSum term (M-(n+1)) + term (M-(n+1))) + term (M-(n+1)) = _
      grind only
  rw [rev M (Nat.le_refl _), direct, Nat.sub_self, Integral.rectangleSum]
  grind only

/-- Reflection of the unit parameter preserves the value of quadrature. -/
theorem Data.reflect_unit {f : Rat → Value} (D : Data f 0 1)
    (E : Data (fun t => f (1-t)) 0 1) : Same E.value D.value := by
  have hz : Small (sub E.value D.value) 0 := by
    apply EffectiveImproperIntegral.small_of_errors _ 0
      (fun n => (E.constant + D.constant) / ((n+1 : Nat) : Rat))
      (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
    intro n
    let M := n+1
    have hM : 0 < M := by omega
    have H := (E.midpoint_error M hM).add (D.midpoint_error M hM).neg
    have he : E.constant*(1-0)*mesh 0 1 M + D.constant*(1-0)*mesh 0 1 M =
        0 + (E.constant+D.constant)/((n+1 : Nat) : Rat) := by
      simp only [mesh, if_neg (Nat.ne_of_gt hM), M, Rat.div_def]
      grind only
    rw [he] at H
    refine (H.congr (((Same.refl E.value).sub (midpoint_reflected_sums f M hM)).add (Same.refl _))).congr ?_
    apply arithmetic_identity
    intro s
    simp only [Value.add, Value.neg, sub]
    grind only
  exact small_sub_zero_same hz


def UniformFirstOrder (f d : Rat → Value) (a b : Rat) : Prop :=
  ∀ eps : QPos, ∃ δ : QPos, ∀ u v, a ≤ u → u ≤ v → v ≤ b → v-u ≤ δ.val →
    Small (sub (sub (f v) (f u)) (RealApproximationOrder.scale (v-u) (d u))) (eps.val*(v-u))

theorem UniformFirstOrder.restrict {f d : Rat → Value} {a b u v : Rat}
    (h : UniformFirstOrder f d a b) (hu : a ≤ u) (hv : v ≤ b) :
    UniformFirstOrder f d u v := by
  intro eps
  obtain ⟨δ, hδ⟩ := h eps
  exact ⟨δ, fun x y hx hxy hy => hδ x y (Rat.le_trans hu hx) hxy (Rat.le_trans hy hv)⟩

/-- The FTC for a uniform relative error modulus. The proof compares
the endpoint increment with actual tagged sums of the supplied derivative. -/
theorem Data.ftc_of_uniform_remainder {f d : Rat → Value} {a b : Rat} (D : Data d a b)
    (H : UniformFirstOrder f d a b) :
    Same D.value (sub (f b) (f a)) := by
  have hb : 0 ≤ b-a := by have := D.ordered; grind only
  have hs : ShrinksToZero (fun n => ((D.constant+1)*(b-a)) / ((n+1 : Nat) : Rat)) :=
    shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors _ 0 _ hs
  intro n
  let eps : QPos := ⟨1 / ((n+1 : Nat) : Rat), one_div_nat_pos (Nat.succ_pos n)⟩
  obtain ⟨δ, hδ⟩ := H eps
  let ε : QPos := ⟨min δ.val eps.val, by
    rw [Rat.min_def]
    split
    · exact δ.property
    · exact eps.property⟩
  have hε₁ : ε.val ≤ δ.val := by change min δ.val eps.val ≤ _; grind
  have hε₂ : ε.val ≤ eps.val := by change min δ.val eps.val ≤ _; grind
  have hm : ShrinksToZero (fun k => (b-a) / ((k+1 : Nat) : Rat)) :=
    shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)
  obtain ⟨N,hN⟩ := hm ε
  let M := N+1
  have hM : 0 < M := by omega
  let P := RationalPartition.uniform a b M hM D.ordered
  let m := mesh a b M
  have hm' : m ≤ ε.val := by
    change mesh a b M ≤ _
    rw [mesh, if_neg (Nat.ne_of_gt hM)]
    exact hN N (Nat.le_refl _)
  have hn : 0 ≤ m := mesh_nonneg_of_le hM D.ordered
  have hstep (k : Nat) : P.point (k+1)-P.point k=m := by
    simp only [P,RationalPartition.uniform,leftPoint,Rat.natCast_add]
    change (a+((k:Rat)+1)*m)-(a+(k:Rat)*m)=m
    grind only
  have near (k : Nat) (hk : k ≤ M) :
      Small (sub (sub (f (P.point k)) (f a)) (taggedSum d P P.point k))
        (eps.val*(P.point k-a)) := by
    induction k with
    | zero =>
      rw [P.left_endpoint, Rat.sub_self, Rat.mul_zero]
      have h := rational_small 0
      rw [show qabs (0 : Rat) = 0 by decide +kernel] at h
      exact h.congr (arithmetic_identity _ _ (by
        intro s; simp only [taggedSum, Value.rational, sub, Rat.sub_self]))
    | succ k ih =>
      have hkp : k ≤ M := by omega
      have hkv : k+1 ≤ P.pieces := hk
      have hku : k ≤ P.pieces := hkp
      have hmon := P.monotone k (k+1) (by omega) hkv
      have H := hδ (P.point k) (P.point (k+1)) (P.point_in_bounds hku).1 hmon
        (P.point_in_bounds hkv).2 (by rw [hstep]; exact Rat.le_trans hm' hε₁)
      have K := (ih hkp).add H
      rw [show eps.val*(P.point k-a)+eps.val*(P.point (k+1)-P.point k) =
        eps.val*(P.point (k+1)-a) by grind only] at K
      exact K.congr (arithmetic_identity _ _ (by
        intro s
        simp only [taggedSum, Value.add, sub]
        grind only))
  have hend := near M (Nat.le_refl _)
  have hPM : P.point M = b := P.right_endpoint
  rw [hPM] at hend
  have hint := D.tagged_error P P.point m hn
    (fun k _ => by rw [hstep]; exact Rat.le_refl)
    (fun k hk => ⟨Rat.le_refl, P.monotone _ _ (by omega) (by omega)⟩)
  have hint' : Small (sub D.value (taggedSum d P P.point M)) (D.constant*(b-a)*m) := hint
  refine ((hint'.add hend.neg).congr (arithmetic_identity _ _ (by
    intro s; simp only [Value.add, Value.neg, sub]; grind only))).mono ?_
  have hmul := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hm' hε₂)
    (Rat.mul_nonneg D.nonnegative hb)
  change D.constant*(b-a)*m + eps.val*(b-a) ≤ 0 + (D.constant+1)*(b-a)/((n+1 : Nat) : Rat)
  simp only [eps, Rat.div_def, Rat.one_mul] at hmul ⊢
  grind only

/-- Uniform secant convergence and a Lipschitz derivative give a quadratic
remainder, by identifying increments with the fixed dyadic integral. -/
def Data.stepOfUniformFirstOrder {f d : Rat → Value} {a b : Rat} (D : Data d a b)
    (h : UniformFirstOrder f d a b) : Step f d a b where
  error := D.constant
  error_nonnegative := D.nonnegative
  radius := ⟨1, by decide⟩
  variation := D.constant
  variation_nonnegative := D.nonnegative
  lipschitz := D.lipschitz
  firstOrder u v hu huv hv _ := by
    let E := D.restrict u v hu (Rat.le_of_lt huv) hv
    have inc : Same E.value (sub (f v) (f u)) :=
      E.ftc_of_uniform_remainder (h.restrict hu hv)
    exact (E.tag_error u Rat.le_refl (Rat.le_of_lt huv)).congr
      (inc.sub (Same.refl _))

/-- Accumulation from the lower endpoint using the fixed dyadic integral. -/
def Data.accumulated {f : Rat → Value} {a b : Rat} (D : Data f a b) (t : Rat) : Value :=
  if h : a ≤ t ∧ t ≤ b then (D.restrict a t Rat.le_refl h.1 h.2).value else Value.rational 0

/-- The second direction of FTC for a sampler with supplied Lipschitz
control. This is quadratic error for the actual finite-window computation. -/
def Data.accumulationStep {f : Rat → Value} {a b : Rat} (D : Data f a b) :
    Step D.accumulated f a b where
  error := D.constant
  error_nonnegative := D.nonnegative
  radius := ⟨1,by decide +kernel⟩
  firstOrder := by
    intro u v hu huv hv _
    have huv' := Rat.le_of_lt huv
    have hu' : a ≤ u ∧ u ≤ b := ⟨hu,Rat.le_trans huv' hv⟩
    have hv' : a ≤ v ∧ v ≤ b := ⟨Rat.le_trans hu huv',hv⟩
    let A := D.restrict a u Rat.le_refl hu'.1 hu'.2
    let B := D.restrict u v hu huv' hv
    let C := D.restrict a v Rat.le_refl hv'.1 hv'.2
    let K := constantData (f u) u v huv'
    have H := B.difference_small K (D.constant*(v-u)) (fun t hut htv => by
      have J := D.lipschitz u t hu hut (Rat.le_trans htv hv)
      have h := Rat.mul_le_mul_of_nonneg_left (show t-u ≤ v-u by grind only) D.nonnegative
      exact J.mono h)
    have H' : Same (Value.add A.value B.value) C.value :=
      RealCompute.equiv_symm (A.append B C)
    have huval : D.accumulated u = A.value := dif_pos hu'
    have hvval : D.accumulated v = C.value := dif_pos hv'
    rw [huval,hvval]
    have E : Same K.value (RealApproximationOrder.scale (v-u) (f u)) := constant_value (f u) u v huv'
    have J : Same B.value (sub C.value A.value) := by
      apply Same.trans (Y := sub (Value.add A.value B.value) A.value) _ (H'.sub (Same.refl A.value))
      apply arithmetic_identity
      intro s
      simp only [Value.add,sub]
      grind only
    have H'' := H.congr (J.sub E)
    have h : (v-u)*(D.constant*(v-u)) = D.constant*(v-u)*(v-u) := by grind only
    rw [h] at H''
    exact H''
  variation := D.constant
  variation_nonnegative := D.nonnegative
  lipschitz := D.lipschitz

end ComputableAnalysis.LipschitzQuadrature


