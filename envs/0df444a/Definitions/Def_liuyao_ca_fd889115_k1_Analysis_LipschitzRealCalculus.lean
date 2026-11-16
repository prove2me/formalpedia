-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealCalculus
-- name    : liuyao_ca_fd889115_k1_Analysis_LipschitzRealCalculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:01:46.931369+00:00
-- url     : https://prove2.me/theorems/3d629edf-e896-4068-8872-8cd69ca17636
-- title:
--   Computable analysis · LipschitzRealCalculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/LipschitzRealCalculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealExtension
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealIntervalImage
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealSecantDerivative

set_option autoImplicit true

/-! Covered real continuity and derivatives from uniform real first-order
estimates. These laws assert no universal derivative or integral existence. -/
namespace ComputableAnalysis.LipschitzRealExtension
open RawLimit BracketDerivative BracketContinuity
set_option maxHeartbeats 2000000

theorem continuous {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) (w : Nat → Rat) (hw : ShrinksToZero w)
    (widths : ∀ q n, ((f q).compute n).width≤w n) {x : RealCompute} (hx : x.Valid) :
    HasContinuousAt (fun _ => True) f x (extend f L x) := by
  have hval := valid hf hL lip w hw widths hx
  refine ⟨hx,hval,fun q _ => hf q,⟨BracketDerivative.enlarged x,enlarged_admissible hx⟩,fun A hA => ?_⟩
  have hAv := valid hf hL lip w hw widths hA.2.1
  have hc : HasEnclosureValue (BracketContinuity.observations f A) (extend f L A) := by
    refine ⟨hAv,(fun _ j => (extend f L A).compute j),(fun n => n),(fun n => n),
      cofinal_id,cofinal_id,hAv,RealCompute.equiv_refl _ hAv,?_⟩
    rintro n y ⟨r,hl,hr,rfl⟩
    exact covers hf hL lip hA.2.1 n ⟨hl,hr⟩
  exact hc.congr_value hval (congr hf hL lip hA.2.1 hx hA.2.2.1)

theorem constant_product_continuous {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) (w : Nat → Rat) (hw : ShrinksToZero w)
    (widths : ∀ q n, ((f q).compute n).width≤w n) (C : RealCompute) (hC : C.Valid)
    {x : RealCompute} (hx : x.Valid) :
    HasContinuousAt (fun _ => True) (fun q => RealCompute.mul C (f q)) x
      (RealCompute.mul C (extend f L x)) := by
  have hval := valid hf hL lip w hw widths hx
  have hprod := RealCompute.mul_valid hC hval
  refine ⟨hx,hprod,fun q _ => RealCompute.mul_valid hC (hf q),
    ⟨BracketDerivative.enlarged x,enlarged_admissible hx⟩,fun A hA => ?_⟩
  have hAv := valid hf hL lip w hw widths hA.2.1
  have hPv := RealCompute.mul_valid hC hAv
  have hc : HasEnclosureValue (BracketContinuity.observations (fun q => RealCompute.mul C (f q)) A)
      (RealCompute.mul C (extend f L A)) := by
    refine ⟨hPv,(fun _ j => (RealCompute.mul C (extend f L A)).compute j),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,hPv,RealCompute.equiv_refl _ hPv,?_⟩
    rintro n y ⟨r,hl,hr,rfl⟩
    exact RealIntervalImage.mul hC (hf r) (RealIntervalImage.current hC n)
      (covers hf hL lip hA.2.1 n ⟨hl,hr⟩)
  exact hc.congr_value hprod (RealCompute.mul_equiv hC hC hAv hval
    (RealCompute.equiv_refl _ hC) (congr hf hL lip hA.2.1 hx hA.2.2.1))

theorem continuous_neg {domain : Rat → Prop} {f : Rat → RealCompute} {x y : RealCompute}
    (h : HasContinuousAt domain f x y) : HasContinuousAt domain (fun q => -(f q)) x (-y) := by
  refine ⟨h.1,RealCompute.neg_valid h.2.1,fun q hq => RealCompute.neg_valid (h.2.2.1 q hq),h.2.2.2.1,fun A hA => ?_⟩
  obtain ⟨hv,Q,n,m,hn,hm,hdiag,he,cover⟩ := h.2.2.2.2 A hA
  refine ⟨RealCompute.neg_valid hv,(fun i j => {lo := -(Q i j).hi,hi := -(Q i j).lo}),n,m,hn,hm,
    RealCompute.neg_valid hdiag,RealCompute.neg_equiv he,?_⟩
  rintro k z ⟨r,hl,hr,rfl⟩
  exact RealIntervalImage.neg (cover k (f r) ⟨r,hl,hr,rfl⟩)

/-- A uniform finite first-order bound on rational secants. The derivative
sampler is independently supplied and its real-input value needs continuity. -/
def FirstOrder (f d : Rat → RealCompute) (M delta : Rat) : Prop :=
  ∀ u v, u<v → v-u≤delta →
    InInterval (f v-f u-RealCompute.scaleRat (v-u) (d u))
      {lo := -M*(v-u)*(v-u),hi := M*(v-u)*(v-u)}

theorem secant_error {f d : Rat → RealCompute} {M delta u v : Rat}
    (H : FirstOrder f d M delta) (huv : u<v) (hstep : v-u≤delta) :
    InInterval (BracketDerivative.secant f u v-d u) {lo := -M*(v-u),hi := M*(v-u)} := by
  have hp : 0<v-u := by grind only
  have hn : 0≤1/(v-u) := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hc := Rat.inv_mul_cancel (v-u) (Rat.ne_of_gt hp)
  have cancel (A Z : Rat) : ((v-u)⁻¹*A-Z)*(v-u)=A-(v-u)*Z := by
    have hm : ((v-u)⁻¹*A)*(v-u)=A := by
      rw [Rat.mul_comm ((v-u)⁻¹) A,Rat.mul_assoc,hc,Rat.mul_one]
    have he : ((v-u)⁻¹*A-Z)*(v-u)=((v-u)⁻¹*A)*(v-u)-Z*(v-u) := by grind only
    rw [he,hm]
    rw [Rat.mul_comm Z (v-u)]
  have Huv := H u v huv hstep
  constructor
  · intro i n
    have h := Huv.1 0 n
    change -M*(v-u)*(v-u)≤((f v).compute n).hi-((f u).compute n).lo-
      (RealCompute.scaleRatCompute (v-u) (d u) n).lo at h
    simp only [RealCompute.scaleRatCompute,if_pos (Rat.le_of_lt hp)] at h
    change -M*(v-u)≤(RealCompute.scaleRatCompute (1/(v-u)) (f v-f u) n).hi-((d u).compute n).lo
    simp only [RealCompute.scaleRatCompute,if_pos hn]
    apply Rat.le_of_mul_le_mul_right (c := v-u) _ hp
    change (-M*(v-u))*(v-u)≤((1/(v-u))*(((f v).compute n).hi-((f u).compute n).lo)-((d u).compute n).lo)*(v-u)
    simp only [Rat.div_def,Rat.one_mul]
    rw [cancel]
    exact h
  · intro n i
    have h := Huv.2 n 0
    change ((f v).compute n).lo-((f u).compute n).hi-
      (RealCompute.scaleRatCompute (v-u) (d u) n).hi≤M*(v-u)*(v-u) at h
    simp only [RealCompute.scaleRatCompute,if_pos (Rat.le_of_lt hp)] at h
    change (RealCompute.scaleRatCompute (1/(v-u)) (f v-f u) n).lo-((d u).compute n).hi≤M*(v-u)
    simp only [RealCompute.scaleRatCompute,if_pos hn]
    apply Rat.le_of_mul_le_mul_right (c := v-u) _ hp
    change ((1/(v-u))*(((f v).compute n).lo-((f u).compute n).hi)-((d u).compute n).hi)*(v-u)≤(M*(v-u))*(v-u)
    simp only [Rat.div_def,Rat.one_mul]
    rw [cancel]
    exact h

/-- A proved rational first-order estimate identifies the derivative at
every represented input. Full nearby rational secants, including secants
crossing a piece boundary, are covered. -/
theorem derivative_of_firstOrder {f d : Rat → RealCompute} {M delta : Rat}
    (hf : ∀ q, (f q).Valid) (hM : 0≤M) (hdelta : 0<delta)
    (H : FirstOrder f d M delta) {x D : RealCompute}
    (hD : HasContinuousAt (fun _ => True) d x D) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) f x D := by
  apply RealSecantDerivative.hasDerivative_iff_neighborhoods.mpr
  refine ⟨hD.1,hD.2.1,fun q _ => hf q,hD.2.2.2.1,fun A hA => ⟨hD.2.1,?_⟩⟩
  intro k eps
  let half : QPos := ⟨eps.val/2,by have := eps.property; grind only⟩
  let small : QPos := ⟨eps.val/(2*(M+1)),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind only))⟩
  have hd := (hasContinuousAt_iff_neighborhoods.mp hD).2.2.2.2 A hA
  obtain ⟨N,hN⟩ := hd.2 k half
  obtain ⟨K,hK⟩ := hA.2.1.2.2 ⟨delta,hdelta⟩
  obtain ⟨J,hJ⟩ := hA.2.1.2.2 small
  let T := max N (max K J)
  refine ⟨T,?_⟩
  rintro y ⟨a,b,ha,hab,hb,rfl⟩
  have hlen : b-a≤(A.compute T).width := by unfold QInterval.width; grind only
  have hstep := hK T (by dsimp [T]; omega)
  change (A.compute T).width≤delta at hstep
  have hsmall := hJ T (by dsimp [T]; omega)
  have herr := secant_error H hab (Rat.le_trans hlen hstep)
  have nest := hA.2.1.2.1 N T (by dsimp [T]; omega)
  have haN : (A.compute N).lo≤a ∧ a≤(A.compute N).hi := by constructor <;> grind only
  have hi := hN (d a) ⟨a,haN.1,haN.2,rfl⟩
  have hout := RealIntervalImage.error_translate (BracketDerivative.secant_valid (hf a) (hf b))
    (hD.2.2.1 a True.intro) (M*(b-a)) (by simpa only [Rat.neg_mul] using herr) hi
  have hm := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hlen hsmall) hM
  have he : small.val*(2*(M+1))=eps.val := by
    dsimp [small]; exact Rat.div_mul_cancel (by grind only : 2*(M+1)≠0)
  have hp := small.property
  have hbudget : M*(b-a)≤eps.val/2 := by grind only
  apply RealIntervalImage.weaken hout
  unfold QInterval.ContainsInterval QInterval.expand
  dsimp only [half]
  constructor <;> grind only

end ComputableAnalysis.LipschitzRealExtension


