-- Prove2me | solution 1 for AddictivePlatforms.Compete.proposition_2_step_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T15:51:31.72029+00:00
-- url     : https://prove2.me/submissions/3f9bc723-d278-4d3f-a36d-6884b1158230

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
theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (K : ℕ)
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
#print axioms solution
