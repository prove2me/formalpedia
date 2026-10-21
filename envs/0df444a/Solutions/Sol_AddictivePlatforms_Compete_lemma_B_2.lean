-- Prove2me | solution 1 for AddictivePlatforms.Compete.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T12:12:58.756607+00:00
-- url     : https://prove2.me/submissions/89da072f-7255-46a4-ab50-e5bf34aa5d5c

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

theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞)
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
#print axioms solution
