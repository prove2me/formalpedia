-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerRealDerivative
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerRealDerivative
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:00:11.260666+00:00
-- url     : https://prove2.me/theorems/addc7c4d-ce87-49de-bf7d-ac23bfdbed71
-- title:
--   Computable analysis · EulerRealDerivative · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerRealDerivative.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerReal
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealSecantDerivative

set_option autoImplicit true

/-! Identification of the Euler computation by its secants. Finite powers,
their certified error bounds, and order are the proof ingredients. -/
namespace ComputableAnalysis.EulerReal
open EulerFinite
set_option maxHeartbeats 2500000

theorem sample_point_bounds {M q : Rat} (hM : 0≤M) (hl : -M≤q) (hr : q≤M)
    (n i : Nat) :
    ((sample q).compute i).lo≤lower q (count M n)+budget M*M^2/(count M n:Rat) ∧
      lower q (count M n)≤((sample q).compute i).hi := by
  have hb := input_within (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q) i
  change -(inputBound (RealCompute.ofRat q))≤q ∧ q≤inputBound (RealCompute.ofRat q) at hb
  have hs := count_positive (inputBound (RealCompute.ofRat q)) i
  have hs' := count_large (inputBound (RealCompute.ofRat q)) i
  have hn := count_positive M n
  have hn' := count_large M n
  have hcross := cross_bound hs hn (a := q) (b := q)
    (by grind only) (by grind only) Rat.le_refl
  have hcross' := cross_bound hn hs (a := q) (b := q)
    (by grind only) (by grind only) Rat.le_refl
  have hw := enclosure_width hM (I := ⟨q,q⟩) Rat.le_refl hl hr n
  change upper q (count M n)-lower q (count M n)≤budget M*((q-q)+M^2/(count M n:Rat)) at hw
  constructor
  · change lower q (count (inputBound (RealCompute.ofRat q)) i)≤_
    grind [Rat.div_def]
  · exact hcross'

theorem sample_mono {a b : Rat} (hab : a≤b) : (sample a).Le (sample b) := by
  intro i j
  have ha := input_within (x := RealCompute.ofRat a) (RealCompute.ofRat_valid a) i
  have hb := input_within (x := RealCompute.ofRat b) (RealCompute.ofRat_valid b) j
  change -(inputBound (RealCompute.ofRat a))≤a ∧ a≤inputBound (RealCompute.ofRat a) at ha
  change -(inputBound (RealCompute.ofRat b))≤b ∧ b≤inputBound (RealCompute.ofRat b) at hb
  change lower a (count (inputBound (RealCompute.ofRat a)) i)≤upper b (count (inputBound (RealCompute.ofRat b)) j)
  exact cross_bound (count_positive _ i) (count_positive _ j)
    (by have := count_large (inputBound (RealCompute.ofRat a)) i; grind only)
    (by have := count_large (inputBound (RealCompute.ofRat b)) j; grind only) hab

theorem secant_compute {a b : Rat} (hab : a<b) (n : Nat) :
    (BracketDerivative.secant sample a b).compute n =
      {lo := (((sample b).compute n).lo-((sample a).compute n).hi)/(b-a),
       hi := (((sample b).compute n).hi-((sample a).compute n).lo)/(b-a)} := by
  have hi : 0≤1/(b-a) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (by grind only))
  simp only [BracketDerivative.secant,RealCompute.scaleRat,RealCompute.scaleRatCompute,
    RealCompute.sub,RealCompute.subCompute,if_pos hi]
  congr 1
  · change (1/(b-a))*(((sample b).compute n).lo-((sample a).compute n).hi)=_
    grind [Rat.div_def]
  · change (1/(b-a))*(((sample b).compute n).hi-((sample a).compute n).lo)=_
    grind [Rat.div_def]

/-- All secants of the constructed function lie between its endpoint values. -/
theorem secant_order {a b : Rat} (hab : a<b) :
    (sample a).Le (BracketDerivative.secant sample a b) ∧
      (BracketDerivative.secant sample a b).Le (sample b) := by
  let M := qabs a+qabs b+1
  have hM : 0≤M := by have := qabs_nonneg a; have := qabs_nonneg b; dsimp [M]; grind only
  have ha : -M≤a ∧ a≤M := by
    have := neg_qabs_le_self a; have := self_le_qabs a; have := qabs_nonneg b
    dsimp [M]; constructor <;> grind only
  have hb : -M≤b ∧ b≤M := by
    have := neg_qabs_le_self b; have := self_le_qabs b; have := qabs_nonneg a
    dsimp [M]; constructor <;> grind only
  let C := budget M*M+budget M*M^2*(1+1/(b-a))
  have hi : 0<(b-a)⁻¹ := Rat.inv_pos.mpr (by grind only)
  have hC : 0≤C := by
    have hB := Rat.le_of_lt (budget_positive M)
    have hs : 0≤M^2 := by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using rat_square_nonneg_basic M
    have H1 := Rat.mul_nonneg hB hM
    have H2 := Rat.mul_nonneg (Rat.mul_nonneg hB hs) (show 0≤1+1/(b-a) by grind [Rat.div_def])
    dsimp [C]; grind only
  have approx (n i j : Nat) :
      ((sample a).compute i).lo≤((BracketDerivative.secant sample a b).compute j).hi+C/(count M n:Rat) ∧
      ((BracketDerivative.secant sample a b).compute j).lo≤((sample b).compute i).hi+C/(count M n:Rat) := by
    let N := count M n
    let delta := budget M*M^2/(N:Rat)
    let eta := budget M*M/(N:Rat)
    have hdelta : 0≤delta := by
      have H1 := Rat.le_of_lt (budget_positive M)
      have H2 : 0≤M^2 := by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using rat_square_nonneg_basic M
      have H3 := Rat.le_of_lt (Rat.inv_pos.mpr (count_positive M n))
      exact Rat.mul_nonneg (Rat.mul_nonneg H1 H2) H3
    have Hai := sample_point_bounds hM ha.1 ha.2 n i
    have Haj := sample_point_bounds hM ha.1 ha.2 n j
    have Hbi := sample_point_bounds hM hb.1 hb.2 n i
    have Hbj := sample_point_bounds hM hb.1 hb.2 n j
    have Hfinite := finite_chord_error hM ha.1 hab hb.2 (count_large M n)
    have Hbudget := upper_le_budget hM (Rat.le_refl : M≤M) n
    have Hb1 := Rat.mul_le_mul_of_nonneg_right Hbudget hM
    have Hb2 := Rat.mul_le_mul_of_nonneg_right Hb1
      (Rat.le_of_lt (Rat.inv_pos.mpr (count_positive M n)))
    have Heta : upper M N*M/(N:Rat)≤eta := by exact Hb2
    have Hlow : lower a N≤(lower b N-lower a N)/(b-a)+eta := by grind only
    have Hhigh : (lower b N-lower a N)/(b-a)≤lower b N+eta := by grind only
    have Hnum1 : lower b N-lower a N≤
        ((sample b).compute j).hi-((sample a).compute j).lo+delta := by
      change ((sample a).compute j).lo≤lower a N+delta ∧ _ at Haj
      change _ ∧ lower b N≤((sample b).compute j).hi at Hbj
      grind only
    have Hnum2 : ((sample b).compute j).lo-((sample a).compute j).hi≤
        lower b N-lower a N+delta := by
      change _ ∧ lower a N≤((sample a).compute j).hi at Haj
      change ((sample b).compute j).lo≤lower b N+delta ∧ _ at Hbj
      grind only
    have Hd1 := Rat.mul_le_mul_of_nonneg_right Hnum1 (Rat.le_of_lt hi)
    have Hd2 := Rat.mul_le_mul_of_nonneg_right Hnum2 (Rat.le_of_lt hi)
    have He : eta+delta+delta/(b-a)=C/(N:Rat) := by dsimp [eta,delta,C]; grind [Rat.div_def]
    rw [secant_compute hab j]
    change ((sample a).compute i).lo≤_ ∧ _≤((sample b).compute i).hi+C/(N:Rat)
    rw [←He]
    change ((sample a).compute i).lo≤lower a N+delta ∧ _ at Hai
    change _ ∧ lower b N≤((sample b).compute i).hi at Hbi
    dsimp only [N,delta,eta] at Hlow Hhigh Hd1 Hd2 Hai Hbi hdelta ⊢
    constructor <;> grind [Rat.div_def]
  constructor
  · intro i j
    by_cases h : ((sample a).compute i).lo≤((BracketDerivative.secant sample a b).compute j).hi
    · exact h
    have hp : 0<(((sample a).compute i).lo-((BracketDerivative.secant sample a b).compute j).hi)/2 := by grind only
    obtain ⟨n,hn⟩ := count_decay M C hC ⟨_,hp⟩
    have H := (approx n i j).1
    have hn := hn n (Nat.le_refl n)
    grind only
  · intro i j
    by_cases h : ((BracketDerivative.secant sample a b).compute i).lo≤((sample b).compute j).hi
    · exact h
    have hp : 0<(((BracketDerivative.secant sample a b).compute i).lo-((sample b).compute j).hi)/2 := by grind only
    obtain ⟨n,hn⟩ := count_decay M C hC ⟨_,hp⟩
    have H := (approx n j i).2
    have hn := hn n (Nat.le_refl n)
    grind only

theorem enclosure_covers {M : Rat} {x : RealCompute} (hx : x.Valid) (hw : within M x)
    (n : Nat) {r : Rat} (hr : (x.compute n).lo≤r ∧ r≤(x.compute n).hi) :
    RawLimit.InInterval (sample r) (enclosure M (x.compute n) n) := by
  have hsrc (j : Nat) := input_within (x := RealCompute.ofRat r) (RealCompute.ofRat_valid r) j
  constructor
  · intro i j
    have H := hsrc j
    change -(inputBound (RealCompute.ofRat r))≤r ∧ r≤inputBound (RealCompute.ofRat r) at H
    exact cross_bound (count_positive M n) (count_positive _ j)
      (by have := count_large M n; have := (hw n).1; grind only)
      (by have := count_large (inputBound (RealCompute.ofRat r)) j; grind only) hr.1
  · intro j i
    have H := hsrc j
    change -(inputBound (RealCompute.ofRat r))≤r ∧ r≤inputBound (RealCompute.ofRat r) at H
    exact cross_bound (count_positive _ j) (count_positive M n)
      (by have := count_large (inputBound (RealCompute.ofRat r)) j; grind only)
      (by have := count_large M n; have := (hw n).2; grind only) hr.2

/-- Euler's method solves the normalized growth equation at every valid real
input. The derivative is the same executable represented evaluation. -/
theorem derivative {x : RealCompute} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) sample x (eval x) := by
  refine ⟨hx,eval_valid hx,(fun q _ => sample_valid q),
    ⟨BracketDerivative.enlarged x,BracketDerivative.enlarged_admissible hx⟩,?_⟩
  intro A hA
  let M := inputBound A
  let Q := fun i j => enclosure M (A.compute i) j
  refine ⟨eval_valid hx,Q,(fun n => n),(fun n => n),RawLimit.cofinal_id,RawLimit.cofinal_id,
    eval_valid hA.2.1,eval_congr hA.2.1 hx hA.2.2.1,?_⟩
  rintro n y ⟨a,b,ha,hab,hb,rfl⟩
  have H := secant_order hab
  have ha' : (A.compute n).lo≤a ∧ a≤(A.compute n).hi := by constructor <;> grind only
  have hb' : (A.compute n).lo≤b ∧ b≤(A.compute n).hi := by constructor <;> grind only
  have Hlo := enclosure_covers hA.2.1 (input_within hA.2.1) n ha'
  have Hhi := enclosure_covers hA.2.1 (input_within hA.2.1) n hb'
  exact ⟨RealCompute.le_trans (sample_valid a) Hlo.1 H.1,
    RealCompute.le_trans (sample_valid b) H.2 Hhi.2⟩

end ComputableAnalysis.EulerReal


