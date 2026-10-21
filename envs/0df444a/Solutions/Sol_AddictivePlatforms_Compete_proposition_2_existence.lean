-- Prove2me | solution 1 for AddictivePlatforms.Compete.proposition_2_existence
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T17:40:17.784077+00:00
-- url     : https://prove2.me/submissions/98c41f32-9be7-447b-b2f5-315be17e4801

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model
open Set
open scoped ENNReal
open AddictivePlatforms.Compete

private lemma feasible_mix (Abar : ℝ≥0∞) {A B α β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hcA : ENNReal.ofReal A ≤ Abar)
    (hcB : ENNReal.ofReal B ≤ Abar) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (hab : α + β = 1) :
    0 ≤ α * A + β * B ∧ ENNReal.ofReal (α * A + β * B) ≤ Abar := by
  refine ⟨by positivity, ?_⟩
  have ht : α * A + β * B ≤ max A B := by
    calc
      _ ≤ α * max A B + β * max A B := by gcongr <;> simp
      _ = max A B := by rw [← add_mul, hab, one_mul]
  exact (ENNReal.ofReal_le_ofReal ht).trans (by
    rcases le_total A B with h | h
    · simpa [max_eq_right h] using hcB
    · simpa [max_eq_left h] using hcA)

private lemma perspective_mix (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) {d : ℝ}
    (hu : ConcaveOn ℝ (Ici 0) (fun a => u a d))
    (hC : ConvexOn ℝ (Ici 0) C)
    {y z A B α β : ℝ} (hy : 0 < y) (hz : 0 < z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hab : α + β = 1) :
    α * perspObj u C y d A + β * perspObj u C z d B ≤
      perspObj u C (α * y + β * z) d (α * A + β * B) := by
  have ht : 0 < α * y + β * z := by
    rcases ha.eq_or_lt with h | h
    · have hb1 : β = 1 := by linarith
      simp [← h, hb1, hz]
    · positivity
  have hw : α * y / (α * y + β * z) + β * z / (α * y + β * z) = 1 := by
    field_simp
  have hu' := hu.2 (show A / y ∈ Ici 0 by exact div_nonneg hA hy.le)
    (show B / z ∈ Ici 0 by exact div_nonneg hB hz.le)
    (show 0 ≤ α * y / (α * y + β * z) by positivity)
    (show 0 ≤ β * z / (α * y + β * z) by positivity) hw
  simp only [smul_eq_mul] at hu'
  have he : α * y / (α * y + β * z) * (A / y) +
      β * z / (α * y + β * z) * (B / z) =
        (α * A + β * B) / (α * y + β * z) := by field_simp
  rw [he] at hu'
  have hu'' := mul_le_mul_of_nonneg_left hu' ht.le
  have he' : (α * y + β * z) *
      (α * y / (α * y + β * z) * u (A / y) d +
        β * z / (α * y + β * z) * u (B / z) d) =
      α * y * u (A / y) d + β * z * u (B / z) d := by field_simp
  rw [he'] at hu''
  have hc := hC.2 hA hB ha hb hab
  simp only [smul_eq_mul] at hc
  unfold perspObj
  nlinarith

theorem value_concave (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d)) :
    ∀ d : ℝ, 0 ≤ d →
      ConcaveOn ℝ (Ioi 0) (fun y => perspObj u C y d (Astar y d)) := by
  intro d hd
  refine ⟨convex_Ioi 0, ?_⟩
  intro y hy z hz α β ha hb hab
  simp only [smul_eq_mul]
  have ht : 0 < α * y + β * z := by
    simpa only [smul_eq_mul, mem_Ioi] using (convex_Ioi (0 : ℝ) hy hz ha hb hab)
  have hAy := hA y hy d hd
  have hAz := hA z hz d hd
  have hm := feasible_mix Abar hAy.1 hAz.1 hAy.2.1 hAz.2.1 ha hb hab
  exact (perspective_mix u C (hS.assumption1.concaveOn_a d hd)
    hS.assumption2.convexOn hy hz hAy.1 hAz.1 ha hb hab).trans
      ((hA _ ht d hd).2.2 _ hm.1 hm.2)

private lemma objective_strictConcave (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d) :
    StrictConcaveOn ℝ (Ici 0) (perspObj u C y d) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro A hA B hB hAB α β ha hb hab
  have hn : A / y ≠ B / y := by
    intro h
    exact hAB ((div_left_inj' hy.ne').mp h)
  have hu := (hS.strictConcaveOn_a d hd).2
    (div_nonneg hA hy.le) (div_nonneg hB hy.le) hn ha hb hab
  have hc := hS.assumption2.convexOn.2 hA hB ha.le hb.le hab
  simp only [smul_eq_mul] at hu hc ⊢
  have he : α * (A / y) + β * (B / y) = (α * A + β * B) / y := by ring
  rw [he] at hu
  have hum := mul_lt_mul_of_pos_left hu hy
  unfold perspObj
  nlinarith

theorem maximizer_unique (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y d A B : ℝ} (hy : 0 < y) (hd : 0 ≤ d)
    (hA : IsPerspMax u C Abar y d A) (hB : IsPerspMax u C Abar y d B) : A = B := by
  let F : Set ℝ := {x | 0 ≤ x ∧ ENNReal.ofReal x ≤ Abar}
  have hf : Convex ℝ F := by
    intro x hx z hz α β ha hb hab
    exact feasible_mix Abar hx.1 hz.1 hx.2 hz.2 ha hb hab
  have hs : StrictConcaveOn ℝ F (perspObj u C y d) :=
    (objective_strictConcave u C hS hy hd).subset (fun _ hx => hx.1) hf
  exact hs.eq_of_isMaxOn (fun x hx => hA.2.2 x hx.1 hx.2)
    (fun x hx => hB.2.2 x hx.1 hx.2) ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩

theorem perspective_bundle (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d)) :
    (∀ d : ℝ, 0 ≤ d →
      ConcaveOn ℝ (Ioi 0) (fun y => perspObj u C y d (Astar y d))) ∧
    (∀ y d A : ℝ, 0 < y → 0 ≤ d → IsPerspMax u C Abar y d A → A = Astar y d) := by
  refine ⟨value_concave u C Abar hS Astar hA, ?_⟩
  intro y d A hy hd hAm
  exact maximizer_unique u C Abar hS hy hd hAm (hA y hy d hd)

set_option autoImplicit false
open Set
open scoped ENNReal
open AddictivePlatforms.Compete
namespace AttentionComparative
lemma slice_diff (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {d : ℝ} (hd : 0 ≤ d) : DifferentiableOn ℝ (fun a => u a d) (Ici 0) := by
  exact hS.assumption1.differentiableOn.comp
    (differentiableOn_id.prodMk (differentiableOn_const d)) (fun a ha => ⟨ha,hd⟩)
lemma perspective_deriv (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Ici 0))
    {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    HasDerivAt (fun a => y*f (a/y)) (derivWithin f (Ici 0) (x/y)) x := by
  have h := (hf (x/y) (div_nonneg hx.le hy.le)).hasDerivWithinAt.hasDerivAt
    (Ici_mem_nhds (div_pos hx hy))
  convert (h.comp x ((hasDerivAt_id x).div_const y)).const_mul y using 1 <;>
    first | rfl | field_simp
lemma cost_deriv (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Ici 0))
    {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    HasDerivAt (fun a => f (y*a)/y) (derivWithin f (Ici 0) (y*x)) x := by
  have h := (hf (y*x) (mul_nonneg hy.le hx.le)).hasDerivWithinAt.hasDerivAt
    (Ici_mem_nhds (mul_pos hy hx))
  convert (h.comp x ((hasDerivAt_id x).const_mul y)).div_const y using 1 <;>
    first | rfl | field_simp
lemma benefit_difference (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Ici 0))
    (hc : ConcaveOn ℝ (Ici 0) f) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyz : y ≤ z) :
    MonotoneOn (fun a => z*f (a/z)-y*f (a/y)) (Ici 0) := by
  have hcont (t : ℝ) (ht : 0 < t) :
      ContinuousOn (fun a => t*f (a/t)) (Ici 0) :=
    continuousOn_const.mul (hf.continuousOn.comp (continuousOn_id.div_const t)
      (fun a ha => div_nonneg ha ht.le))
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) ((hcont z hz).sub (hcont y hy))
    (f' := fun a => derivWithin f (Ici 0) (a/z)-derivWithin f (Ici 0) (a/y))
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact ((perspective_deriv f hf hz hx').sub (perspective_deriv f hf hy hx')).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x := (show 0 < x by simpa only [interior_Ici,mem_Ioi] using hx).le
    apply sub_nonneg.2
    exact hc.antitoneOn_derivWithin hf (div_nonneg hx' hz.le) (div_nonneg hx' hy.le)
      ((div_le_div_iff₀ hz hy).2 (by nlinarith))
lemma cost_difference (C : ℝ → ℝ) (hf : DifferentiableOn ℝ C (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) C) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyz : y ≤ z) :
    MonotoneOn (fun a => C (z*a)/z-C (y*a)/y) (Ici 0) := by
  have hcont (t : ℝ) (ht : 0 < t) :
      ContinuousOn (fun a => C (t*a)/t) (Ici 0) :=
    (hf.continuousOn.comp (continuousOn_const.mul continuousOn_id)
      (fun a ha => mul_nonneg ht.le ha)).div_const t
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) ((hcont z hz).sub (hcont y hy))
    (f' := fun a => derivWithin C (Ici 0) (z*a)-derivWithin C (Ici 0) (y*a))
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact ((cost_deriv C hf hz hx').sub (cost_deriv C hf hy hx')).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x := (show 0 < x by simpa only [interior_Ici,mem_Ioi] using hx).le
    exact sub_nonneg.2 (hc.monotoneOn_derivWithin hf
      (mul_nonneg hy.le hx') (mul_nonneg hz.le hx') (mul_le_mul_of_nonneg_right hyz hx'))
lemma total_monotone (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y z d A B : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≤ z) (hd : 0 ≤ d) (hA : IsPerspMax u C Abar y d A)
    (hB : IsPerspMax u C Abar z d B) : A ≤ B := by
  by_contra hn
  have hBA : B < A := lt_of_not_ge hn
  have hi := benefit_difference (fun a => u a d) (slice_diff u C hS hd)
    (hS.assumption1.concaveOn_a d hd) hy hz hyz hB.1 hA.1 hBA.le
  have hmA := hA.2.2 B hB.1 hB.2.1
  have hmB := hB.2.2 A hA.1 hA.2.1
  have he : perspObj u C y d B = perspObj u C y d A := by
    unfold perspObj at hmA hmB ⊢
    linarith
  have hB' : IsPerspMax u C Abar y d B :=
    ⟨hB.1,hB.2.1,fun x hx hc => (hA.2.2 x hx hc).trans_eq he.symm⟩
  exact hBA.ne (maximizer_unique u C Abar hS hy hd hB' hA)
lemma per_platform_antitone (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y z d A B : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≤ z) (hd : 0 ≤ d) (hA : IsPerspMax u C Abar y d A)
    (hB : IsPerspMax u C Abar z d B) : B/z ≤ A/y := by
  by_contra hn
  let a := A/y
  let b := B/z
  have hab : a < b := lt_of_not_ge hn
  have ha : 0 ≤ a := div_nonneg hA.1 hy.le
  have hb : 0 ≤ b := div_nonneg hB.1 hz.le
  have hea : y*a = A := by dsimp [a]; field_simp
  have heb : z*b = B := by dsimp [b]; field_simp
  have hyb : y*b ≤ B := by rw [← heb]; exact mul_le_mul_of_nonneg_right hyz hb
  have hza : z*a ≤ B := by rw [← heb]; exact mul_le_mul_of_nonneg_left hab.le hz.le
  have hcyb : ENNReal.ofReal (y*b) ≤ Abar :=
    (ENNReal.ofReal_le_ofReal hyb).trans hB.2.1
  have hcza : ENNReal.ofReal (z*a) ≤ Abar :=
    (ENNReal.ofReal_le_ofReal hza).trans hB.2.1
  have h1 := div_le_div_of_nonneg_right (hA.2.2 (y*b) (mul_nonneg hy.le hb) hcyb) hy.le
  have h2 := div_le_div_of_nonneg_right (hB.2.2 (z*a) (mul_nonneg hz.le ha) hcza) hz.le
  have hobj (t x : ℝ) (ht : 0 < t) :
      perspObj u C t d (t*x)/t = u x d-C (t*x)/t := by
    unfold perspObj
    rw [mul_div_cancel_left₀ x ht.ne']
    field_simp
  rw [← hea,hobj y b hy,hobj y a hy] at h1
  rw [← heb,hobj z a hz,hobj z b hz] at h2
  have hi := cost_difference C hS.assumption2.differentiableOn hS.assumption2.convexOn
    hy hz hyz ha hb hab.le
  have he : perspObj u C y d (y*b) = perspObj u C y d A := by
    apply (div_left_inj' hy.ne').mp
    rw [← hea,hobj y b hy,hobj y a hy]
    linarith
  have hB' : IsPerspMax u C Abar y d (y*b) :=
    ⟨mul_nonneg hy.le hb,hcyb,fun x hx hc => (hA.2.2 x hx hc).trans_eq he.symm⟩
  have hu := maximizer_unique u C Abar hS hy hd hB' hA
  have heab : a = b := by nlinarith
  exact hab.ne heab
end AttentionComparative
theorem comparative_bundle (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d)) :
    ∀ d : ℝ, 0 ≤ d →
      MonotoneOn (fun y => Astar y d) (Ioi 0) ∧
      AntitoneOn (fun y => Astar y d/y) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi 0) (fun y => perspObj u C y d (Astar y d)) := by
  intro d hd
  refine ⟨?_,?_,value_concave u C Abar hS Astar hA d hd⟩
  · intro y hy z hz hyz
    exact AttentionComparative.total_monotone u C Abar hS hy hz hyz hd (hA y hy d hd) (hA z hz d hd)
  · intro y hy z hz hyz
    exact AttentionComparative.per_platform_antitone u C Abar hS hy hz hyz hd
      (hA y hy d hd) (hA z hz d hd)
#print axioms comparative_bundle

set_option autoImplicit false
open Set
open scoped ENNReal
open AddictivePlatforms.Compete AttentionComparative

namespace AttentionExchange

lemma utility_difference (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e) :
    MonotoneOn (fun a => u a e - u a d) (Ici 0) := by
  have hdif (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun a => u a t) (u1 u x t) x :=
    ((slice_diff u C hS ht) x hx.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds hx)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    ((slice_diff u C hS he).continuousOn.sub (slice_diff u C hS hd).continuousOn)
    (f' := fun a => u1 u a e - u1 u a d)
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact ((hdif e he x hx').sub (hdif d hd x hx')).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x := (show 0 < x by simpa only [interior_Ici,mem_Ioi] using hx).le
    exact sub_nonneg.2 ((hS.assumption1.strictMonoOn_u1 x hx').monotoneOn hd he hde)

lemma normalized_obj (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (y d a : ℝ) (hy : 0 < y) :
    perspObj u C y d (y*a)/y = u a d-C (y*a)/y := by
  unfold perspObj
  rw [mul_div_cancel_left₀ a hy.ne']
  field_simp

lemma normalized_max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    {y d A a : ℝ} (hy : 0 < y) (hA : IsPerspMax u C Abar y d A)
    (ha : 0 ≤ a) (hc : ENNReal.ofReal (y*a) ≤ Abar) :
    u a d-C (y*a)/y ≤ perspObj u C y d A/y := by
  rw [← normalized_obj u C y d a hy]
  exact div_le_div_of_nonneg_right (hA.2.2 (y*a) (mul_nonneg hy.le ha) hc) hy.le

lemma normalized_value (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (y d A : ℝ) (hy : 0 < y) :
    perspObj u C y d A/y = u (A/y) d-C (y*(A/y))/y := by
  have h : y*(A/y) = A := by field_simp
  rw [← normalized_obj u C y d (A/y) hy,h]

lemma value_submodular (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d))
    {y z d e : ℝ} (hy : 0 < y) (hz : 0 < z) (hyz : y ≤ z)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e) :
    perspObj u C y d (Astar y d)/y + perspObj u C z e (Astar z e)/z ≤
      perspObj u C y e (Astar y e)/y + perspObj u C z d (Astar z d)/z := by
  let a := Astar y d/y
  let b := Astar z e/z
  have ha : 0 ≤ a := div_nonneg (hA y hy d hd).1 hy.le
  have hb : 0 ≤ b := div_nonneg (hA z hz e he).1 hz.le
  have hea : y*a = Astar y d := by dsimp [a]; field_simp
  have heb : z*b = Astar z e := by dsimp [b]; field_simp
  have hca : ENNReal.ofReal (y*a) ≤ Abar := by rw [hea]; exact (hA y hy d hd).2.1
  have hcb : ENNReal.ofReal (z*b) ≤ Abar := by rw [heb]; exact (hA z hz e he).2.1
  rw [normalized_value u C y d (Astar y d) hy, normalized_value u C z e (Astar z e) hz]
  change u a d-C (y*a)/y + (u b e-C (z*b)/z) ≤ _
  by_cases hab : a ≤ b
  · have hcyb : ENNReal.ofReal (y*b) ≤ Abar :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hyz hb)).trans hcb
    have hcza : ENNReal.ofReal (z*a) ≤ Abar :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hab hz.le)).trans hcb
    have h1 := normalized_max u C Abar hy (hA y hy e he) hb hcyb
    have h2 := normalized_max u C Abar hz (hA z hz d hd) ha hcza
    have hi := cost_difference C hS.assumption2.differentiableOn hS.assumption2.convexOn
      hy hz hyz ha hb hab
    linarith
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    have h1 := normalized_max u C Abar hy (hA y hy e he) ha hca
    have h2 := normalized_max u C Abar hz (hA z hz d hd) hb hcb
    have hi := utility_difference u C hS hd he hde hb ha hba
    linarith

lemma value_antitone (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d))
    {y d e : ℝ} (hy : 0 < y) (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e) :
    perspObj u C y e (Astar y e)/y ≤ perspObj u C y d (Astar y d)/y := by
  have h1 := (hS.assumption1.strictAntiOn_d (Astar y e/y)
    (div_nonneg (hA y hy e he).1 hy.le)).antitoneOn hd he hde
  have h2 := (hA y hy d hd).2.2 (Astar y e) (hA y hy e he).1 (hA y hy e he).2.1
  apply (div_le_div_iff_of_pos_right hy).2
  unfold perspObj at h2 ⊢
  nlinarith

lemma decreasing_differences (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d))
    {y z : ℝ} (hy : 0 < y) (hyz : y < z) :
    AntitoneOn (fun d => perspObj u C z d (Astar z d) -
      perspObj u C y d (Astar y d)) (Ici 0) := by
  have hz : 0 < z := hy.trans hyz
  intro d hd e he hde
  have hs := value_submodular u C Abar hS Astar hA hy hz hyz.le hd he hde
  have hn := value_antitone u C Abar hS Astar hA hz hd he hde
  let D := perspObj u C z e (Astar z e)/z-perspObj u C z d (Astar z d)/z
  let E := perspObj u C y e (Astar y e)/y-perspObj u C y d (Astar y d)/y
  have hDE : D ≤ E := by dsimp [D,E]; linarith
  have hD : D ≤ 0 := by dsimp [D]; linarith
  have hh : z*D ≤ y*E :=
    (mul_le_mul_of_nonpos_right hyz.le hD).trans (mul_le_mul_of_nonneg_left hDE hy.le)
  have hzD : z*D = perspObj u C z e (Astar z e)-perspObj u C z d (Astar z d) := by
    dsimp [D]; field_simp
  have hyE : y*E = perspObj u C y e (Astar y e)-perspObj u C y d (Astar y d) := by
    dsimp [E]; field_simp
  rw [hzD,hyE] at hh
  linarith

end AttentionExchange

theorem accepted_B2 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d)) :
    (∀ d : ℝ, 0 ≤ d →
      MonotoneOn (fun y => Astar y d) (Ioi 0) ∧
      AntitoneOn (fun y => Astar y d/y) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi 0) (fun y => perspObj u C y d (Astar y d))) ∧
    ∀ y z : ℝ, 0 < y → y < z →
      AntitoneOn (fun d => perspObj u C z d (Astar z d)-perspObj u C y d (Astar y d)) (Ici 0) := by
  refine ⟨comparative_bundle u C Abar hS Astar hA, ?_⟩
  intro y z hy hyz
  exact AttentionExchange.decreasing_differences u C Abar hS Astar hA hy hyz
#print axioms accepted_B2

namespace AttentionThreshold
open AttentionExchange AttentionComparative
lemma cross_four (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y z d e AYD AYE AZD AZE : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hyz : y ≤ z)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e)
    (hyd : IsPerspMax u C Abar y d AYD) (hye : IsPerspMax u C Abar y e AYE)
    (hzd : IsPerspMax u C Abar z d AZD) (hze : IsPerspMax u C Abar z e AZE) :
    perspObj u C y d AYD/y + perspObj u C z e AZE/z ≤
      perspObj u C y e AYE/y + perspObj u C z d AZD/z := by
  let a := AYD/y
  let b := AZE/z
  have ha : 0 ≤ a := div_nonneg hyd.1 hy.le
  have hb : 0 ≤ b := div_nonneg hze.1 hz.le
  have hea : y*a = AYD := by dsimp [a]; field_simp
  have heb : z*b = AZE := by dsimp [b]; field_simp
  have hca : ENNReal.ofReal (y*a) ≤ Abar := by rw [hea]; exact hyd.2.1
  have hcb : ENNReal.ofReal (z*b) ≤ Abar := by rw [heb]; exact hze.2.1
  rw [normalized_value u C y d AYD hy, normalized_value u C z e AZE hz]
  change u a d-C (y*a)/y + (u b e-C (z*b)/z) ≤ _
  by_cases hab : a ≤ b
  · have hcyb : ENNReal.ofReal (y*b) ≤ Abar :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hyz hb)).trans hcb
    have hcza : ENNReal.ofReal (z*a) ≤ Abar :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hab hz.le)).trans hcb
    have h1 := normalized_max u C Abar hy hye hb hcyb
    have h2 := normalized_max u C Abar hz hzd ha hcza
    have hi := cost_difference C hS.assumption2.differentiableOn hS.assumption2.convexOn
      hy hz hyz ha hb hab
    linarith
  · have h1 := normalized_max u C Abar hy hye ha hca
    have h2 := normalized_max u C Abar hz hzd hb hcb
    have hi := utility_difference u C hS hd he hde hb ha (lt_of_not_ge hab).le
    linarith

lemma value_strict_decrease (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y d e AD AE : ℝ}
    (hy : 0 < y) (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d < e)
    (hD : IsPerspMax u C Abar y d AD) (hE : IsPerspMax u C Abar y e AE) :
    perspObj u C y e AE/y < perspObj u C y d AD/y := by
  have h1 := (hS.assumption1.strictAntiOn_d (AE/y)
    (div_nonneg hE.1 hy.le)) hd he hde
  have h2 := hD.2.2 AE hE.1 hE.2.1
  apply (div_lt_div_iff_of_pos_right hy).2
  unfold perspObj at h2 ⊢
  nlinarith

lemma difference_strict_decrease (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y z d e AYD AYE AZD AZE : ℝ}
    (hy : 0 < y) (hyz : y < z) (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d < e)
    (hyd : IsPerspMax u C Abar y d AYD) (hye : IsPerspMax u C Abar y e AYE)
    (hzd : IsPerspMax u C Abar z d AZD) (hze : IsPerspMax u C Abar z e AZE) :
    perspObj u C z e AZE - perspObj u C y e AYE <
      perspObj u C z d AZD - perspObj u C y d AYD := by
  have hz := hy.trans hyz
  have hs := cross_four u C Abar hS hy hz hyz.le hd he hde.le hyd hye hzd hze
  have hn := value_strict_decrease u C Abar hS hz hd he hde hzd hze
  let D := perspObj u C z e AZE/z-perspObj u C z d AZD/z
  let E := perspObj u C y e AYE/y-perspObj u C y d AYD/y
  have hDE : D ≤ E := by dsimp [D,E]; linarith
  have hD : D < 0 := by dsimp [D]; linarith
  have hh : z*D < y*E :=
    (mul_lt_mul_of_neg_right hyz hD).trans_le (mul_le_mul_of_nonneg_left hDE hy.le)
  have hzD : z*D = perspObj u C z e AZE-perspObj u C z d AZD := by
    dsimp [D]; field_simp
  have hyE : y*E = perspObj u C y e AYE-perspObj u C y d AYD := by
    dsimp [E]; field_simp
  rw [hzD,hyE] at hh
  linarith

lemma eq3_unique (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (K : ℕ) (hK : 2 ≤ K)
    {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hD : Eq3 u C Abar K d)
    (hE : Eq3 u C Abar K e) : d = e := by
  have hy : 0 < (K:ℝ)-1 := by
    have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hyz : (K:ℝ)-1 < (K:ℝ) := by linarith
  obtain ⟨AD,BD,hAD,hBD,hdeq⟩ := hD
  obtain ⟨AE,BE,hAE,hBE,heeq⟩ := hE
  rcases lt_trichotomy d e with hlt | heq | hgt
  · have h := difference_strict_decrease u C Abar hS hy hyz hd he hlt hBD hBE hAD hAE
    rw [hdeq,heeq] at h
    linarith
  · exact heq
  · have h := difference_strict_decrease u C Abar hS hy hyz he hd hgt hBE hBD hAE hAD
    rw [hdeq,heeq] at h
    linarith

lemma finite_cap_max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) (hbar : Abar ≠ ⊤) {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d) :
    ∃ A : ℝ, IsPerspMax u C Abar y d A := by
  have hc : ContinuousOn (perspObj u C y d) (Ici 0) := by
    exact (continuousOn_const.mul
      ((slice_diff u C hS hd).continuousOn.comp (continuousOn_id.div_const y)
        (fun A hA => div_nonneg hA hy.le))).sub hS.assumption2.differentiableOn.continuousOn
  obtain ⟨A,hA,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) Abar.toReal).Nonempty from ⟨0,le_rfl,ENNReal.toReal_nonneg⟩)
    (hc.mono (fun _ h => h.1))
  refine ⟨A,hA.1,(ENNReal.ofReal_le_iff_le_toReal hbar).mpr hA.2,?_⟩
  intro B hB hb
  exact hmax ⟨hB,(ENNReal.ofReal_le_iff_le_toReal hbar).mp hb⟩

lemma negative_gap (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
    (hS : Standing u C) {y z d AY AZ : ℝ}
    (hy : 0 < y) (hyz : y < z) (hz1 : 1 ≤ z)
    (hneg : ∀ a : ℝ, 0 ≤ a → u a d - C a < 0)
    (hY : IsPerspMax u C Abar y d AY) (hZ : IsPerspMax u C Abar z d AZ) :
    perspObj u C z d AZ < perspObj u C y d AY := by
  have hz : 0 < z := hy.trans hyz
  have hinv : 0 ≤ 1/z := by positivity
  have hinv1 : 1/z ≤ 1 := (div_le_one hz).mpr hz1
  have hc := hS.assumption2.convexOn.2 hZ.1 (show (0:ℝ) ∈ Ici 0 by simp)
    hinv (sub_nonneg.mpr hinv1) (show 1/z + (1-1/z) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hS.C_zero] at hc
  have hc' : C (AZ/z) ≤ C AZ / z := by convert hc using 1 <;> congr 1 <;> ring
  have hn := hneg (AZ/z) (div_nonneg hZ.1 hz.le)
  have hv : perspObj u C z d AZ < 0 := by
    have ht : u (AZ/z) d - C AZ/z < 0 := by linarith
    have hmul := mul_neg_of_pos_of_neg hz ht
    unfold perspObj
    have he : z*(u (AZ/z) d-C AZ/z) = z*u (AZ/z) d-C AZ := by field_simp
    rwa [he] at hmul
  let r := y/z
  have hr : 0 < r := div_pos hy hz
  have hr1 : r < 1 := (div_lt_one hz).mpr hyz
  have hfeas : ENNReal.ofReal (r*AZ) ≤ Abar :=
    (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hZ.1 hr1.le)).trans hZ.2.1
  have hmax := hY.2.2 (r*AZ) (mul_nonneg hr.le hZ.1) hfeas
  have hcr := hS.assumption2.convexOn.2 hZ.1 (show (0:ℝ) ∈ Ici 0 by simp)
    hr.le (sub_nonneg.mpr hr1.le) (show r+(1-r)=1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hS.C_zero] at hcr
  have he : r*AZ/y = AZ/z := by dsimp [r]; field_simp
  have hscale : r*perspObj u C z d AZ ≤ perspObj u C y d AY := by
    unfold perspObj at hmax ⊢
    rw [he] at hmax
    have hrz : r*z = y := by dsimp [r]; field_simp
    rw [mul_sub, ← mul_assoc, hrz]
    linarith
  exact (by nlinarith [mul_pos (sub_pos.mpr hr1) (neg_pos.mpr hv)] :
    perspObj u C z d AZ < r*perspObj u C z d AZ).trans_le hscale
end AttentionThreshold
#print axioms AttentionThreshold.eq3_unique
#print axioms AttentionThreshold.finite_cap_max
#print axioms AttentionThreshold.negative_gap

theorem accepted_threshold_support (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) :
    (∀ Abar : ℝ≥0∞, ∀ K : ℕ, 2 ≤ K →
      ∀ d e : ℝ, 0 ≤ d → 0 ≤ e → Eq3 u C Abar K d → Eq3 u C Abar K e → d = e) ∧
    (∀ Abar : ℝ≥0∞, Abar ≠ ⊤ → ∀ y d : ℝ, 0 < y → 0 ≤ d →
      ∃ A : ℝ, IsPerspMax u C Abar y d A) := by
  constructor
  · intro Abar K hK d e hd he hD hE
    exact AttentionThreshold.eq3_unique u C Abar hS K hK hd he hD hE
  · intro Abar hbar y d hy hd
    exact AttentionThreshold.finite_cap_max u C Abar hS hbar hy hd
#print axioms accepted_threshold_support

namespace AttentionExistence
open AttentionThreshold AttentionComparative AttentionExchange
open scoped Topology
lemma small_improvement (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (B : ℝ) (hB : 0 < B) :
    ∃ a : ℝ, 0 < a ∧ a < B ∧ u 0 0 < u a 0 - C a := by
  have hp : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < u1 u a 0 - Cderiv C a := by
    rcases hS.assumption2.limit_pos with ⟨L,hL,hlim⟩ | hlim
    · exact hlim.eventually (eventually_gt_nhds hL)
    · exact hlim.eventually_gt_atTop (0:ℝ)
  obtain ⟨a,ha,hder⟩ := (hp.and (Ioo_mem_nhdsGT hB)).exists
  have hac : 0 < a := hder.1
  have hconv : ConvexOn ℝ (Ici 0) (fun x => C x - u x 0) :=
    hS.assumption2.convexOn.sub (hS.assumption1.concaveOn_a 0 le_rfl)
  have hD : HasDerivWithinAt (fun x => C x - u x 0)
      (Cderiv C a - u1 u a 0) (Ici 0) a :=
    (hS.assumption2.differentiableOn a hac.le).hasDerivWithinAt.sub
      ((slice_diff u C hS le_rfl) a hac.le).hasDerivWithinAt
  have h := hconv.slope_le_of_hasDerivWithinAt (show (0:ℝ) ∈ Ici 0 by simp)
    hac.le hac hD
  rw [slope_def_field] at h
  simp only [sub_zero, hS.C_zero, zero_sub] at h
  have hh := (div_le_iff₀ hac).mp h
  refine ⟨a,hac,hder.2,?_⟩
  nlinarith [mul_pos hac ha]

lemma positive_attention (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (Abar : ℝ≥0∞) (hbar : 0 < Abar) {y A : ℝ} (hy : 1 ≤ y)
    (hA : IsPerspMax u C Abar y 0 A) : 0 < A := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  obtain ⟨B,hB,hcap⟩ : ∃ B : ℝ, 0 < B ∧ ENNReal.ofReal B ≤ Abar := by
    by_cases ht : Abar = ⊤
    · exact ⟨1,zero_lt_one,by simp [ht]⟩
    · exact ⟨Abar.toReal,ENNReal.toReal_pos hbar.ne' ht,ENNReal.ofReal_toReal_le⟩
  obtain ⟨a,ha,haB,hu⟩ := small_improvement u C hS B hB
  have hmax := hA.2.2 a ha.le ((ENNReal.ofReal_le_ofReal haB.le).trans hcap)
  have hconv := (hS.assumption1.concaveOn_a 0 le_rfl).2 ha.le
    (show (0:ℝ) ∈ Ici 0 by simp) (show 0 ≤ 1/y by positivity)
    (sub_nonneg.mpr ((div_le_one hy0).mpr hy)) (show 1/y+(1-1/y)=1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at hconv
  have hc : u a 0 + (y-1)*u 0 0 ≤ y*u (a/y) 0 := by
    have h := mul_le_mul_of_nonneg_left hconv hy0.le
    have he : (1/y)*a = a/y := by ring
    rw [he] at h
    field_simp at h
    nlinarith
  by_contra hn
  have hAz : A=0 := le_antisymm (le_of_not_gt hn) hA.1
  simp only [perspObj, hAz, zero_div, hS.C_zero, sub_zero] at hmax
  nlinarith

lemma positive_gap (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (Abar : ℝ≥0∞) (hbar : 0 < Abar) {y z AY AZ : ℝ}
    (hy : 1 ≤ y) (hyz : y < z)
    (hY : IsPerspMax u C Abar y 0 AY) (hZ : IsPerspMax u C Abar z 0 AZ) :
    perspObj u C y 0 AY < perspObj u C z 0 AZ := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hz : 0 < z := hy0.trans hyz
  have hAY := positive_attention u C hS Abar hbar hy hY
  let r := y/z
  have hr : 0 < r := div_pos hy0 hz
  have hr1 : r < 1 := (div_lt_one hz).mpr hyz
  have hstrict := (hS.strictConcaveOn_a 0 le_rfl).2
    (show AY/y ∈ Ici 0 from (div_pos hAY hy0).le) (show (0:ℝ) ∈ Ici 0 by simp)
    (ne_of_gt (div_pos hAY hy0)) hr (sub_pos.mpr hr1)
    (show r+(1-r)=1 by ring)
  have he : r*(AY/y)+(1-r)*0 = AY/z := by dsimp [r]; field_simp; ring
  simp only [smul_eq_mul] at hstrict
  rw [he] at hstrict
  have hm := mul_lt_mul_of_pos_left hstrict hz
  have hnon := mul_nonneg (sub_nonneg.mpr hr1.le) hS.assumption1.u_zero_zero_nonneg
  have hzr : z*r = y := by dsimp [r]; field_simp
  rw [mul_add, ← mul_assoc, hzr] at hm
  have hmax := hZ.2.2 AY hY.1 hY.2.1
  unfold perspObj at hmax ⊢
  nlinarith [mul_nonneg hz.le hnon]

lemma uniform_dominates (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} {d : ℝ} (hd : 0 ≤ d) (J : Finset (Fin K)) (hJ : J.Nonempty)
    (a : Fin K → ℝ) (ha : ∀ k ∈ J, 0 ≤ a k) :
    payoff u C (fun _ => d) (J,a) ≤
      perspObj u C (J.card : ℝ) d (∑ k ∈ J, a k) := by
  have hc : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
  have hj := (hS.assumption1.concaveOn_a d hd).le_map_centerMass
    (t := J) (w := fun _ => (1:ℝ)) (p := a) (by intro k hk; norm_num)
    (by simpa using hc) ha
  simp only [Finset.centerMass, Finset.sum_const, nsmul_eq_mul, mul_one,
    smul_eq_mul, one_mul, Function.comp_def] at hj
  have hh := mul_le_mul_of_nonneg_left hj hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hh
  simpa only [payoff, if_neg hJ.ne_empty, perspObj, div_eq_mul_inv, mul_comm,
    sub_le_sub_iff_right] using hh

lemma uncapped_max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hE : UncOptExists u C K) {d : ℝ} (hd : 0 ≤ d)
    (J : Finset (Fin K)) (hJ : J.Nonempty) :
    ∃ A : ℝ, IsPerspMax u C ⊤ (J.card : ℝ) d A := by
  obtain ⟨a,ha,hmax⟩ := hE (fun _ => d) (by intro k; exact hd) J hJ
  have hc : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
  refine ⟨∑ k ∈ J, a k, Finset.sum_nonneg ha, le_top, ?_⟩
  intro A hA hcap
  have h := hmax (fun _ => A / (J.card : ℝ)) (by intro k hk; positivity)
  have he : (J.card : ℝ) * (A / (J.card : ℝ)) = A := by
    field_simp
  have hp : payoff u C (fun _ => d) (J, fun _ => A / (J.card : ℝ)) =
      perspObj u C (J.card : ℝ) d A := by
    simp [payoff, hJ.ne_empty, perspObj, Finset.sum_const, nsmul_eq_mul, he]
  rw [hp] at h
  exact h.trans (uniform_dominates u C hS hd J hJ a ha)

lemma capped_max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hE : UncOptExists u C K) {d : ℝ} (hd : 0 ≤ d)
    (J : Finset (Fin K)) (hJ : J.Nonempty) (Abar : ℝ≥0∞) :
    ∃ A : ℝ, IsPerspMax u C Abar (J.card : ℝ) d A := by
  by_cases ht : Abar = ⊤
  · subst Abar
    exact uncapped_max u C hS hE hd J hJ
  · exact finite_cap_max u C Abar hS ht (by exact_mod_cast hJ.card_pos) hd

lemma tail_bound (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {y d D AD A : ℝ} (hy : 0 < y) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hAD : IsPerspMax u C ⊤ y D AD) (hA : AD ≤ A) :
    perspObj u C y d A ≤ perspObj u C y d AD := by
  have hdiff := utility_difference u C hS hd (hd.trans hdD) hdD
    (div_nonneg hAD.1 hy.le) (div_nonneg (hAD.1.trans hA) hy.le)
    ((div_le_div_iff_of_pos_right hy).mpr hA)
  have hm := hAD.2.2 A (hAD.1.trans hA) le_top
  unfold perspObj at hm ⊢
  nlinarith [mul_le_mul_of_nonneg_left hdiff hy.le]

lemma bounded_max_lifts (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {y d D AD B A : ℝ} (hy : 0 < y) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hAD : IsPerspMax u C ⊤ y D AD) (hB : AD ≤ B)
    (hA : IsPerspMax u C (ENNReal.ofReal B) y d A) :
    IsPerspMax u C ⊤ y d A := by
  refine ⟨hA.1,le_top,?_⟩
  intro x hx hcap
  by_cases hxB : x ≤ B
  · exact hA.2.2 x hx (ENNReal.ofReal_le_ofReal hxB)
  · exact (tail_bound u C hS hy hd hdD hAD (hB.trans (le_of_not_ge hxB))).trans
      (hA.2.2 AD hAD.1 (ENNReal.ofReal_le_ofReal hB))

noncomputable def boundedValue (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (y B d : ℝ) : ℝ :=
  sSup ((fun A => perspObj u C y (max d 0) A) '' Icc 0 B)

lemma boundedValue_continuous (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {y B : ℝ} (hy : 0 < y) :
    Continuous (boundedValue u C y B) := by
  let f : ℝ → ℝ → ℝ := fun d A =>
    y * u (max A 0 / y) (max d 0) - C (max A 0)
  have hf : Continuous (Function.uncurry f) := by
    have hc : Continuous (fun p : ℝ × ℝ => (max p.2 0 / y, max p.1 0)) :=
      ((continuous_snd.max continuous_const).div_const y).prodMk
        (continuous_fst.max continuous_const)
    have hu := hS.assumption1.differentiableOn.continuousOn.comp_continuous hc
      (by intro p; exact ⟨div_nonneg (le_max_right p.2 0) hy.le,
        show 0 ≤ max p.1 0 from le_max_right p.1 0⟩)
    have hC : Continuous (fun p : ℝ × ℝ => C (max p.2 0)) :=
      hS.assumption2.differentiableOn.continuousOn.comp_continuous
      (continuous_snd.max (continuous_const (y := (0:ℝ))))
      (by intro p; exact show 0 ≤ max p.2 0 from le_max_right p.2 0)
    exact hu.const_mul y |>.sub hC
  have hs := (isCompact_Icc : IsCompact (Icc (0:ℝ) B)).continuous_sSup (f := f) hf
  convert hs using 1
  funext d
  unfold boundedValue
  congr 1
  apply Set.image_congr
  intro A hA
  simp [f,perspObj,max_eq_left hA.1]

lemma boundedValue_eq (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    {y B d A : ℝ} (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hA : IsPerspMax u C (ENNReal.ofReal B) y d A) :
    boundedValue u C y B d = perspObj u C y d A := by
  have hAB : A ≤ B := (ENNReal.ofReal_le_ofReal_iff hB).mp hA.2.1
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_,⟨A,⟨hA.1,hAB⟩,rfl⟩⟩
  · rintro v ⟨x,hx,rfl⟩
    simpa only [max_eq_left hd] using hA.2.2 x hx.1 (ENNReal.ofReal_le_ofReal hx.2)
  · intro w hw
    exact ⟨perspObj u C y d A,⟨A,⟨hA.1,hAB⟩,by simp [hd]⟩,hw⟩

lemma finite_crossing (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {y z B D : ℝ} (hy : 1 ≤ y) (hyz : y < z) (hB : 0 < B)
    (hD : 0 ≤ D) (hneg : ∀ a : ℝ, 0 ≤ a → u a D - C a < 0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ D ∧ ∃ AY AZ : ℝ,
      IsPerspMax u C (ENNReal.ofReal B) y d AY ∧
      IsPerspMax u C (ENNReal.ofReal B) z d AZ ∧
      perspObj u C y d AY = perspObj u C z d AZ := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hz : 0 < z := hy0.trans hyz
  have hex (w t : ℝ) (hw : 0 < w) (ht : 0 ≤ t) :=
    finite_cap_max u C (ENNReal.ofReal B) hS ENNReal.ofReal_ne_top hw ht
  let F := fun t => boundedValue u C z B t - boundedValue u C y B t
  have hcont : Continuous F :=
    (boundedValue_continuous u C hS hz).sub (boundedValue_continuous u C hS hy0)
  obtain ⟨Y0,hY0⟩ := hex y 0 hy0 le_rfl
  obtain ⟨Z0,hZ0⟩ := hex z 0 hz le_rfl
  have hpos : 0 < F 0 := by
    dsimp [F]
    rw [boundedValue_eq u C hB.le le_rfl hY0, boundedValue_eq u C hB.le le_rfl hZ0]
    exact sub_pos.mpr (positive_gap u C hS _ (ENNReal.ofReal_pos.mpr hB) hy hyz hY0 hZ0)
  obtain ⟨YD,hYD⟩ := hex y D hy0 hD
  obtain ⟨ZD,hZD⟩ := hex z D hz hD
  have hlow : F D < 0 := by
    dsimp [F]
    rw [boundedValue_eq u C hB.le hD hYD, boundedValue_eq u C hB.le hD hZD]
    exact sub_neg.mpr (negative_gap u C _ hS hy0 hyz (hy.trans hyz.le) hneg hYD hZD)
  obtain ⟨d,hd,hFd⟩ := intermediate_value_Icc' hD hcont.continuousOn ⟨hlow.le,hpos.le⟩
  have hdpos : 0 < d := by
    refine lt_of_le_of_ne hd.1 ?_
    intro he
    subst d
    linarith
  obtain ⟨AY,hAY⟩ := hex y d hy0 hd.1
  obtain ⟨AZ,hAZ⟩ := hex z d hz hd.1
  refine ⟨d,hdpos,hd.2,AY,AZ,hAY,hAZ,?_⟩
  dsimp [F] at hFd
  rw [boundedValue_eq u C hB.le hd.1 hAY, boundedValue_eq u C hB.le hd.1 hAZ] at hFd
  linarith
end AttentionExistence
#print axioms AttentionExistence.positive_gap
#print axioms AttentionExistence.capped_max

open AttentionExistence
theorem accepted_threshold (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (K : ℕ)
    (hK : 2 ≤ K) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃! dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar := by
  have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hy : 1 ≤ (K:ℝ)-1 := by linarith
  have hyz : (K:ℝ)-1 < K := by linarith
  have hy0 : 0 < (K:ℝ)-1 := by linarith
  have hz : 0 < (K:ℝ) := by linarith
  obtain ⟨D,hD,hneg⟩ := hS.assumption1.exists_neg
  have hroot : ∃ d : ℝ, 0 < d ∧ Eq3 u C Abar K d := by
    by_cases ht : Abar = ⊤
    · subst Abar
      have hex (m : ℕ) (hm : 0 < m) (hmK : m ≤ K) :
          ∃ A : ℝ, IsPerspMax u C ⊤ (m:ℝ) D A := by
        obtain ⟨J,hJsub,hcard⟩ := Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin K))) (n := m) (by simpa using hmK)
        have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
        simpa only [hcard] using uncapped_max u C hS hE hD J hJ
      obtain ⟨AZ,hAZ⟩ := hex K (by omega) le_rfl
      obtain ⟨AY,hAY⟩ : ∃ A : ℝ, IsPerspMax u C ⊤ ((K:ℝ)-1) D A := by
        simpa only [Nat.cast_sub (show 1 ≤ K by omega),Nat.cast_one] using
          hex (K-1) (by omega) (by omega)
      let B := max 1 (max AY AZ)
      have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hYB : AY ≤ B := (le_max_left _ _).trans (le_max_right _ _)
      have hZB : AZ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
      obtain ⟨d,hd,hdD,Y,Z,hY,hZ,heq⟩ := finite_crossing u C hS hy hyz hB hD hneg
      exact ⟨d,hd,Z,Y,bounded_max_lifts u C hS hz hd.le hdD hAZ hZB hZ,
        bounded_max_lifts u C hS hy0 hd.le hdD hAY hYB hY,heq.symm⟩
    · have hB : 0 < Abar.toReal := ENNReal.toReal_pos hAbar.ne' ht
      obtain ⟨d,hd,hdD,Y,Z,hY,hZ,heq⟩ := finite_crossing u C hS hy hyz hB hD hneg
      rw [ENNReal.ofReal_toReal ht] at hY hZ
      exact ⟨d,hd,Z,Y,hZ,hY,heq.symm⟩
  obtain ⟨d,hd,hEq⟩ := hroot
  refine ⟨d,⟨hd,hEq⟩,?_⟩
  intro e he
  exact AttentionThreshold.eq3_unique u C Abar hS K hK he.1.le hd.le he.2 hEq
#print axioms accepted_threshold

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AttentionResponse
open AttentionComparative AttentionExistence

lemma payoff_continuous (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (J : Finset (Fin K))
    (D : Set (Fin K → ℝ)) (hD : ∀ a ∈ D, ∀ k ∈ J, 0 ≤ a k) :
    ContinuousOn (fun a => payoff u C d (J,a)) D := by
  classical
  by_cases he : J = ∅
  · simp only [he, payoff, if_pos rfl]
    exact continuousOn_const
  · simp only [payoff, if_neg he]
    apply ContinuousOn.sub
    · apply continuousOn_finsetSum
      intro k hk
      exact (slice_diff u C hS (hd k)).continuousOn.comp
        (continuous_apply k).continuousOn (fun a ha => hD a ha k hk)
    · exact hS.assumption2.differentiableOn.continuousOn.comp
        (by fun_prop) (fun a ha => Finset.sum_nonneg (hD a ha))

lemma fixed_set_max_finite (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (J : Finset (Fin K))
    (Abar : ℝ≥0∞) (hbar : Abar ≠ ⊤) :
    ∃ a : Fin K → ℝ, Feasible Abar (J,a) ∧
      ∀ b : Fin K → ℝ, Feasible Abar (J,b) → payoff u C d (J,b) ≤ payoff u C d (J,a) := by
  classical
  let B := Abar.toReal
  let D : Set (Fin K → ℝ) := Icc 0 (fun _ => B) ∩ {a | ∑ k ∈ J, a k ≤ B}
  have hc : IsCompact D := isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hne : D.Nonempty := by
    refine ⟨0, ⟨le_rfl, fun k => ENNReal.toReal_nonneg⟩, ?_⟩
    change (∑ k ∈ J, (0 : Fin K → ℝ) k) ≤ B
    simpa using (show 0 ≤ B from ENNReal.toReal_nonneg)
  have hcont := payoff_continuous u C hS d hd J D (fun a ha k _ => ha.1.1 k)
  obtain ⟨a,ha,hmax⟩ := hc.exists_isMaxOn hne hcont
  refine ⟨a, ⟨fun k hk => ha.1.1 k, (ENNReal.ofReal_le_iff_le_toReal hbar).mpr ha.2⟩, ?_⟩
  intro b hb
  let b' : Fin K → ℝ := fun k => if k ∈ J then b k else 0
  have he (k : Fin K) (hk : k ∈ J) : b' k = b k := if_pos hk
  have hsum : (∑ k ∈ J, b' k) = ∑ k ∈ J, b k := Finset.sum_congr rfl he
  have hsumle : (∑ k ∈ J, b k) ≤ B := (ENNReal.ofReal_le_iff_le_toReal hbar).mp hb.2
  have hmem : b' ∈ D := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k
      dsimp [b']
      split_ifs with hk
      · exact hb.1 k hk
      · rfl
    · intro k
      dsimp [b']
      split_ifs with hk
      · exact (Finset.single_le_sum hb.1 hk).trans hsumle
      · exact ENNReal.toReal_nonneg
    · change (∑ k ∈ J, b' k) ≤ B
      simpa only [hsum] using hsumle
  have heq : payoff u C d (J,b') = payoff u C d (J,b) := by
    have hu : (∑ k ∈ J, u (b' k) (d k)) = ∑ k ∈ J, u (b k) (d k) :=
      Finset.sum_congr rfl (fun k hk => by rw [he k hk])
    simp only [payoff, Prod.fst, Prod.snd, hsum, hu]
  have hm : payoff u C d (J,b') ≤ payoff u C d (J,a) := hmax hmem
  rwa [heq] at hm

lemma fixed_set_max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hE : UncOptExists u C K)
    (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (J : Finset (Fin K)) (Abar : ℝ≥0∞) :
    ∃ a : Fin K → ℝ, Feasible Abar (J,a) ∧
      ∀ b : Fin K → ℝ, Feasible Abar (J,b) → payoff u C d (J,b) ≤ payoff u C d (J,a) := by
  classical
  by_cases he : J = ∅
  · subst J
    exact ⟨0, by simp [Feasible], by simp [payoff]⟩
  by_cases ht : Abar = ⊤
  · subst Abar
    obtain ⟨a,ha,hm⟩ := hE d hd J (Finset.nonempty_iff_ne_empty.mpr he)
    exact ⟨a, ⟨ha, le_top⟩, fun b hb => hm b hb.1⟩
  · exact fixed_set_max_finite u C hS d hd J Abar ht

lemma consumer_exists (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hE : UncOptExists u C K)
    (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (Abar : ℝ≥0∞) :
    ∃ x : Choice K, ConsumerOpt u C Abar d x := by
  classical
  choose a ha hmax using fun J : Finset (Fin K) => fixed_set_max u C hS hE d hd J Abar
  obtain ⟨J, _, hJ⟩ := Finset.exists_max_image Finset.univ
    (fun J : Finset (Fin K) => payoff u C d (J,a J)) Finset.univ_nonempty
  refine ⟨(J,a J), ha J, ?_⟩
  intro x hx
  exact (hmax x.1 x.2 hx).trans (hJ x.1 (Finset.mem_univ _))

lemma strategy_exists (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hE : UncOptExists u C K) (Abar : ℝ≥0∞) :
    ∃ σ : ConsumerStrategy K, ∀ d, (∀ k, 0 ≤ d k) → ConsumerOpt u C Abar d (σ d) := by
  classical
  let σ : ConsumerStrategy K := fun d =>
    if hd : ∀ k, 0 ≤ d k then (consumer_exists u C hS hE d hd Abar).choose else (∅,0)
  refine ⟨σ, ?_⟩
  intro d hd
  simpa only [σ, dif_pos hd] using (consumer_exists u C hS hE d hd Abar).choose_spec
lemma threshold_value_nonneg (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hK : 2 ≤ K) {Abar : ℝ≥0∞} {d A B : ℝ}
    (hA : IsPerspMax u C Abar (K : ℝ) d A)
    (hB : IsPerspMax u C Abar ((K : ℝ)-1) d B)
    (he : perspObj u C (K : ℝ) d A = perspObj u C ((K : ℝ)-1) d B) :
    0 ≤ perspObj u C (K : ℝ) d A := by
  have hk : 1 < (K : ℝ) := by exact_mod_cast (by omega : 1 < K)
  let r : ℝ := ((K : ℝ)-1)/(K : ℝ)
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hrk : r*(K : ℝ) = (K : ℝ)-1 := by dsimp [r]; field_simp
  have hc := hS.assumption2.convexOn.2 hA.1 (show (0 : ℝ) ∈ Ici 0 by simp) hr0
    (sub_nonneg.mpr hr1.le) (show r+(1-r)=1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hS.C_zero] at hc
  have hh := hB.2.2 (r*A) (mul_nonneg hr0 hA.1)
    ((ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hA.1 hr1.le)).trans hA.2.1)
  rw [← he] at hh
  have harg : (r*A)/((K : ℝ)-1) = A/(K : ℝ) := by
    dsimp [r]
    field_simp [show (K : ℝ)-1 ≠ 0 by linarith]
  have hv : r * perspObj u C (K : ℝ) d A ≤ perspObj u C ((K : ℝ)-1) d (r*A) := by
    unfold perspObj
    rw [harg, mul_sub, ← mul_assoc, hrk]
    exact sub_le_sub le_rfl hc
  have hb := hv.trans hh
  by_contra hn
  have ht := mul_neg_of_pos_of_neg (sub_pos.mpr hr1) (lt_of_not_ge hn)
  nlinarith

lemma below_threshold_value (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hK : 2 ≤ K) {Abar : ℝ≥0∞} {d A B y T : ℝ}
    (hd : 0 ≤ d) (hy : 0 < y) (hyK : y ≤ (K : ℝ)-1)
    (hA : IsPerspMax u C Abar (K : ℝ) d A)
    (hB : IsPerspMax u C Abar ((K : ℝ)-1) d B)
    (he : perspObj u C (K : ℝ) d A = perspObj u C ((K : ℝ)-1) d B)
    (hT : 0 ≤ T) (hcap : ENNReal.ofReal T ≤ Abar) :
    perspObj u C y d T ≤ perspObj u C (K : ℝ) d A := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hden : 0 < (K : ℝ)-y := by linarith
  let p : ℝ := 1/((K : ℝ)-y)
  let q : ℝ := ((K : ℝ)-1-y)/((K : ℝ)-y)
  have hp : 0 < p := one_div_pos.mpr hden
  have hq : 0 ≤ q := div_nonneg (by linarith) hden.le
  have hpq : p+q=1 := by dsimp [p,q]; field_simp; ring
  have hmix : p*y+q*(K : ℝ) = (K : ℝ)-1 := by dsimp [p,q]; field_simp; ring
  have hm := perspective_mix u C (hS.assumption1.concaveOn_a d hd)
    hS.assumption2.convexOn hy hk hT hA.1 hp.le hq hpq
  rw [hmix] at hm
  have hf := feasible_mix Abar hT hA.1 hcap hA.2.1 hp.le hq hpq
  have hb := hm.trans (hB.2.2 _ hf.1 hf.2)
  rw [← he] at hb
  have heq : p*perspObj u C (K : ℝ) d A + q*perspObj u C (K : ℝ) d A =
      perspObj u C (K : ℝ) d A := by rw [← add_mul,hpq,one_mul]
  have hb' := hb.trans_eq heq.symm
  exact le_of_mul_le_mul_left ((add_le_add_iff_right _).mp hb') hp

lemma uniform_threshold_opt (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hK : 2 ≤ K) {Abar : ℝ≥0∞} {d A B : ℝ} (hd : 0 ≤ d)
    (hA : IsPerspMax u C Abar (K : ℝ) d A)
    (hB : IsPerspMax u C Abar ((K : ℝ)-1) d B)
    (he : perspObj u C (K : ℝ) d A = perspObj u C ((K : ℝ)-1) d B) :
    ConsumerOpt u C Abar (fun _ : Fin K => d)
      (Finset.univ, fun _ => A/(K : ℝ)) := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hk0 : K ≠ 0 := by omega
  have hsum : (∑ _k : Fin K, A/(K : ℝ)) = A := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hk)]
  have hpay : payoff u C (fun _ : Fin K => d) (Finset.univ, fun _ => A/(K : ℝ)) =
      perspObj u C (K : ℝ) d A := by
    have hne : (Finset.univ : Finset (Fin K)) ≠ ∅ := by
      intro heq
      have hc := congrArg Finset.card heq
      exact hk0 (by simpa using hc)
    simp [payoff, hne, hsum, perspObj, Finset.sum_const, nsmul_eq_mul]
  refine ⟨⟨fun k hk' => div_nonneg hA.1 hk.le, by simpa only [hsum] using hA.2.1⟩, ?_⟩
  intro x hx
  rw [hpay]
  by_cases hJ : x.1 = ∅
  · simp only [payoff, hJ, if_pos rfl]
    exact threshold_value_nonneg u C hS hK hA hB he
  have hJn : x.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
  have hub := uniform_dominates u C hS hd x.1 hJn x.2 hx.1
  have hcard : x.1.card ≤ K := by simpa using Finset.card_le_univ x.1
  by_cases hEq : x.1.card = K
  · have hec : (x.1.card : ℝ) = (K : ℝ) := by exact_mod_cast hEq
    rw [hec] at hub
    exact hub.trans (hA.2.2 _ (Finset.sum_nonneg hx.1) hx.2)
  · have hjk : (x.1.card : ℝ) ≤ (K : ℝ)-1 := by
      have : x.1.card + 1 ≤ K := by omega
      have hh : (x.1.card : ℝ)+1 ≤ (K : ℝ) := by exact_mod_cast this
      linarith
    exact hub.trans (below_threshold_value u C hS hK hd
      (by exact_mod_cast hJn.card_pos) hjk hA hB he (Finset.sum_nonneg hx.1) hx.2)
end AttentionResponse
#print axioms AttentionResponse.strategy_exists
#print axioms AttentionResponse.uniform_threshold_opt

/-- The consumer side of the threshold construction, with a response at every profile.
    This theorem does not assert platform deviation inequalities or equilibrium uniqueness. -/
theorem local_consumer_support (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (K : ℕ) (hK : 2 ≤ K) (hE : UncOptExists u C K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃ (dstar A : ℝ) (σ : ConsumerStrategy K),
      0 < dstar ∧ Eq3 u C Abar K dstar ∧
      IsPerspMax u C Abar (K : ℝ) dstar A ∧
      σ (fun _ => dstar) = (Finset.univ, fun _ => A/(K : ℝ)) ∧
      (∀ d, (∀ k, 0 ≤ d k) → ConsumerOpt u C Abar d (σ d)) ∧
      0 ≤ consumerSurplus u C (fun _ => dstar) σ := by
  classical
  obtain ⟨dstar, hdstar, _⟩ := accepted_threshold u C hS K hK hE Abar hAbar
  obtain ⟨A,B,hA,hB,he⟩ := hdstar.2
  obtain ⟨σ0,hσ0⟩ := AttentionResponse.strategy_exists u C hS hE Abar
  let σ : ConsumerStrategy K := fun d =>
    if d = (fun _ => dstar) then (Finset.univ, fun _ => A/(K : ℝ)) else σ0 d
  have hop := AttentionResponse.uniform_threshold_opt u C hS hK hdstar.1.le hA hB he
  have hσ (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) : ConsumerOpt u C Abar d (σ d) := by
    by_cases heq : d = (fun _ => dstar)
    · subst d
      simpa only [σ, if_pos rfl] using hop
    · simpa only [σ, if_neg heq] using hσ0 d hd
  refine ⟨dstar,A,σ,hdstar.1,⟨A,B,hA,hB,he⟩,hA,by simp [σ],hσ,?_⟩
  have hh := (hσ (fun _ => dstar) (fun _ => hdstar.1.le)).2
    (∅, fun _ => 0) (by simp [Feasible])
  simpa [payoff, consumerSurplus] using hh
#print axioms local_consumer_support

namespace AttentionDeviation
open AttentionResponse
lemma excluded_uniform (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    {K : ℕ} (hK : 2 ≤ K) (k : Fin K) (d x B : ℝ) (Abar : ℝ≥0∞)
    (hB : IsPerspMax u C Abar ((K : ℝ)-1) d B) :
    Feasible Abar (Finset.univ.erase k, fun _ : Fin K => B/((K : ℝ)-1)) ∧
      payoff u C (Function.update (fun _ : Fin K => d) k x)
        (Finset.univ.erase k, fun _ : Fin K => B/((K : ℝ)-1)) =
          perspObj u C ((K : ℝ)-1) d B := by
  classical
  have hk : 0 < (K : ℝ)-1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hcard : ((Finset.univ.erase k).card : ℝ) = (K : ℝ)-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have hne : (Finset.univ.erase k : Finset (Fin K)) ≠ ∅ := by
    intro he
    rw [he, Finset.card_empty, Nat.cast_zero] at hcard
    linarith
  have hsum : (∑ j ∈ Finset.univ.erase k, B/((K : ℝ)-1)) = B := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_div_cancel₀ _ hk.ne']
  refine ⟨⟨fun j hj => div_nonneg hB.1 hk.le, by simpa only [hsum] using hB.2.1⟩, ?_⟩
  have hup (j : Fin K) (hj : j ∈ Finset.univ.erase k) :
      Function.update (fun _ : Fin K => d) k x j = d := by
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  simp only [payoff, if_neg hne, Prod.fst, Prod.snd]
  simp_rw [Finset.sum_congr rfl (fun j hj => congrArg (u (B/((K : ℝ)-1))) (hup j hj))]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, hcard]
  rfl

lemma raising_excludes (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hK : 2 ≤ K) (Abar : ℝ≥0∞) (d A B x : ℝ) (hd : 0 ≤ d)
    (hA : IsPerspMax u C Abar (K : ℝ) d A)
    (hB : IsPerspMax u C Abar ((K : ℝ)-1) d B)
    (he : perspObj u C (K : ℝ) d A = perspObj u C ((K : ℝ)-1) d B)
    (k : Fin K) (hx : d < x) (choice : Choice K)
    (hop : ConsumerOpt u C Abar (Function.update (fun _ : Fin K => d) k x) choice) :
    k ∉ choice.1 := by
  classical
  intro hk
  have hne : choice.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k,hk⟩
  have hless : payoff u C (Function.update (fun _ : Fin K => d) k x) choice <
      payoff u C (fun _ : Fin K => d) choice := by
    simp only [payoff, if_neg hne]
    apply sub_lt_sub_right
    apply Finset.sum_lt_sum
    · intro j hj
      by_cases hjk : j = k
      · subst j
        simp only [Function.update_self]
        exact (hS.assumption1.strictAntiOn_d _ (hop.1.1 k hk)
          hd (hd.trans hx.le) hx).le
      · simp only [Function.update_of_ne hjk]
        exact le_rfl
    · refine ⟨k,hk,?_⟩
      simp only [Function.update_self]
      exact hS.assumption1.strictAntiOn_d _ (hop.1.1 k hk) hd (hd.trans hx.le) hx
  have hopt := uniform_threshold_opt u C hS hK hd hA hB he
  have hu := hopt.2 choice hop.1
  have hcard : K ≠ 0 := by omega
  have hkr : (K : ℝ) ≠ 0 := by exact_mod_cast hcard
  have hsum : (∑ _j : Fin K, A/(K : ℝ)) = A := by
    simp [Finset.sum_const,nsmul_eq_mul,mul_div_cancel₀ _ hkr]
  have huniv : (Finset.univ : Finset (Fin K)) ≠ ∅ := by
    intro hh
    have hc := congrArg Finset.card hh
    exact hcard (by simpa using hc)
  have hpay : payoff u C (fun _ : Fin K => d) (Finset.univ, fun _ => A/(K : ℝ)) =
      perspObj u C (K : ℝ) d A := by
    simp [payoff,huniv,hsum,perspObj,Finset.sum_const,nsmul_eq_mul]
  rw [hpay] at hu
  have hout := excluded_uniform u C hK k d x B Abar hB
  have hv := hop.2 _ hout.1
  rw [hout.2, ← he] at hv
  exact (hless.trans_le hu).not_ge hv

lemma utility_difference_strict (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {d e : ℝ} (hd : 0 ≤ d) (hde : d < e) :
    StrictMonoOn (fun a => u a e - u a d) (Ici 0) := by
  have he := hd.trans hde.le
  have hdif (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun a => u a t) (u1 u x t) x :=
    ((AttentionComparative.slice_diff u C hS ht) x hx.le).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hx)
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    ((AttentionComparative.slice_diff u C hS he).continuousOn.sub
      (AttentionComparative.slice_diff u C hS hd).continuousOn)
    (f' := fun a => u1 u a e - u1 u a d)
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact ((hdif e he x hx').sub (hdif d hd x hx')).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x := (show 0 < x by simpa only [interior_Ici,mem_Ioi] using hx).le
    exact sub_pos.mpr (hS.assumption1.strictMonoOn_u1 x hx' hd he hde)

lemma payoff_difference {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (d : Fin K → ℝ) (k : Fin K) (x y : ℝ) (choice : Choice K) (hk : k ∈ choice.1) :
    payoff u C (Function.update d k y) choice - payoff u C (Function.update d k x) choice =
      u (choice.2 k) y - u (choice.2 k) x := by
  classical
  have hne : choice.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k,hk⟩
  simp only [payoff, if_neg hne, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp only [Function.update_self]
  · intro j hj hjk
    simp only [Function.update_of_ne hjk, sub_self]
  · intro hn
    exact (hn hk).elim

lemma own_attention_monotone {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (Abar : ℝ≥0∞) (d : Fin K → ℝ) (k : Fin K)
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y)
    (a b : Choice K) (ha : ConsumerOpt u C Abar (Function.update d k x) a)
    (hb : ConsumerOpt u C Abar (Function.update d k y) b)
    (hka : k ∈ a.1) (hkb : k ∈ b.1) :
    a.2 k ≤ b.2 k := by
  have hab := ha.2 b hb.1
  have hba := hb.2 a ha.1
  have hdiffa := payoff_difference u C d k x y a hka
  have hdiffb := payoff_difference u C d k x y b hkb
  have hd : u (a.2 k) y-u (a.2 k) x ≤ u (b.2 k) y-u (b.2 k) x := by
    linarith
  by_contra hn
  have ht := utility_difference_strict u C hS hx hxy
    (hb.1.1 k hkb) (ha.1.1 k hka) (lt_of_not_ge hn)
  exact ht.not_ge hd

end AttentionDeviation
#print axioms AttentionDeviation.raising_excludes
#print axioms AttentionDeviation.own_attention_monotone

/-- Full equilibrium existence, including every unilateral platform deviation.
    The uniqueness and monopoly-comparison clauses of Propositions 2–3 remain open. -/
theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (K : ℕ) (hK : 2 ≤ K) (hE : UncOptExists u C K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃ dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar ∧
      ∃ σ : ConsumerStrategy K, IsSPE u C Abar (fun _ : Fin K => dstar) σ := by
  classical
  obtain ⟨d,A,σ,hd,heq,hA,hon,hopt,_⟩ :=
    local_consumer_support u C hS K hK hE Abar hAbar
  obtain ⟨A',B,hA',hB,he⟩ := heq
  have hval : perspObj u C (K : ℝ) d A = perspObj u C ((K : ℝ)-1) d B := by
    rw [← he]
    exact le_antisymm (hA'.2.2 A hA.1 hA.2.1) (hA.2.2 A' hA'.1 hA'.2.1)
  have hkpos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hbpay (k : Fin K) : platformPayoff k (σ (fun _ => d)) = A/(K : ℝ) := by
    rw [hon]
    simp [platformPayoff]
  refine ⟨d,hd,⟨A,B,hA,hB,hval⟩,σ,⟨fun _ => hd.le,hopt,?_⟩⟩
  intro k x hx
  have hupdate : Function.update (fun _ : Fin K => d) k d = (fun _ : Fin K => d) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  have hdev : ConsumerOpt u C Abar (Function.update (fun _ : Fin K => d) k x)
      (σ (Function.update (fun _ : Fin K => d) k x)) := by
    apply hopt
    intro j
    by_cases hj : j = k
    · subst j
      simpa using hx
    · simpa [Function.update_of_ne hj] using hd.le
  rcases lt_trichotomy x d with hxd | hexd | hdx
  · rw [hbpay]
    by_cases hjoin : k ∈ (σ (Function.update (fun _ : Fin K => d) k x)).1
    · rw [platformPayoff, if_pos hjoin]
      have hbase : ConsumerOpt u C Abar (Function.update (fun _ : Fin K => d) k d)
          (σ (fun _ : Fin K => d)) := by
        rw [hupdate]
        exact hopt _ (fun _ => hd.le)
      have hkb : k ∈ (σ (fun _ : Fin K => d)).1 := by rw [hon]; simp
      have hh := AttentionDeviation.own_attention_monotone u C hS Abar
        (fun _ : Fin K => d) k x d hx hxd _ _ hdev hbase hjoin hkb
      simpa only [hon] using hh
    · rw [platformPayoff, if_neg hjoin]
      exact div_nonneg hA.1 hkpos.le
  · subst x
    rw [hupdate]
  · have hn := AttentionDeviation.raising_excludes u C hS hK Abar d A B x hd.le
      hA hB hval k hdx _ hdev
    rw [hbpay, platformPayoff, if_neg hn]
    exact div_nonneg hA.1 hkpos.le
#print axioms solution
