-- Prove2me | solution 1 for AddictivePlatforms.Compete.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T12:59:34.168983+00:00
-- url     : https://prove2.me/submissions/56f33f40-9299-442b-b574-9d8c3eabdb6b

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


open Set
open scoped ENNReal
open AddictivePlatforms.Compete AttentionComparative
set_option autoImplicit false

namespace AttentionB3

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
    have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact ((hdif e he x hx').sub (hdif d hd x hx')).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x := (show 0 < x by simpa only [interior_Ici, mem_Ioi] using hx).le
    exact sub_nonneg.2 ((hS.assumption1.strictMonoOn_u1 x hx').monotoneOn hd he hde)

lemma cost_increment_monotone (C : ℝ → ℝ) (hf : DifferentiableOn ℝ C (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) C) {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun t => C (t+r)-C t) (Ici 0) := by
  have hcont : ContinuousOn (fun t => C (t+r)) (Ici 0) :=
    hf.continuousOn.comp (continuousOn_id.add continuousOn_const) (fun t ht => add_nonneg ht hr)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (hcont.sub hf.continuousOn)
    (f' := fun t => derivWithin C (Ici 0) (t+r)-derivWithin C (Ici 0) t)
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have htr : 0 < t+r := by linarith
    have h1 := (hf (t+r) htr.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds htr)
    have h2 := (hf t ht'.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht')
    have h3 : HasDerivAt (fun t => C (t+r)) (derivWithin C (Ici 0) (t+r)) t := by
      convert h1.comp t ((hasDerivAt_id t).add_const r) using 1 <;> first | rfl | ring
    exact (h3.sub h2).hasDerivWithinAt
  · intro t ht
    have ht' : 0 ≤ t := (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    exact sub_nonneg.2 (hc.monotoneOn_derivWithin hf ht' (add_nonneg ht' hr)
      (le_add_of_nonneg_right hr))

lemma cost_cross (C : ℝ → ℝ) (hf : DifferentiableOn ℝ C (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) C) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    C (c+b)+C (a+d) ≤ C (a+b)+C (c+d) := by
  have h := cost_increment_monotone C hf hc (sub_nonneg.2 hac)
    (add_nonneg ha hb) (add_nonneg ha (hb.trans hbd)) (add_le_add le_rfl hbd)
  have h1 : a+b+(c-a) = c+b := by ring
  have h2 : a+d+(c-a) = c+d := by ring
  dsimp only at h
  rw [h1,h2] at h
  linarith

lemma value_cross (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (d' : ℝ) (hd' : 0 ≤ d') (Abar : ℝ≥0∞)
    {x y z d e : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≤ z) (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e)
    {A B D E' : ℝ × ℝ}
    (hA : IsB3Max u C Abar d' x y d A) (hB : IsB3Max u C Abar d' x z e B)
    (hD : IsB3Max u C Abar d' x y e D) (hE : IsB3Max u C Abar d' x z d E') :
    objB3 u C d' x y d A.1 A.2 + objB3 u C d' x z e B.1 B.2 ≤
      objB3 u C d' x y e D.1 D.2 + objB3 u C d' x z d E'.1 E'.2 := by
  have hF {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      x*(u (a/x) e-u (a/x) d) ≤ x*(u (b/x) e-u (b/x) d) :=
    mul_le_mul_of_nonneg_left (utility_difference u C hS hd he hde
      (div_nonneg ha hx.le) (div_nonneg hb hx.le)
      (div_le_div_of_nonneg_right hab hx.le)) hx.le
  have hG := benefit_difference (fun a => u a d') (slice_diff u C hS hd')
    (hS.assumption1.concaveOn_a d' hd') hy hz hyz
  by_cases hac : A.1 ≤ B.1
  · by_cases hbd : A.2 ≤ B.2
    · have hcap1 : ENNReal.ofReal (B.1+A.2) ≤ Abar :=
        (ENNReal.ofReal_le_ofReal (by linarith : B.1+A.2 ≤ B.1+B.2)).trans hB.2.2.1
      have hcap2 : ENNReal.ofReal (A.1+B.2) ≤ Abar :=
        (ENNReal.ofReal_le_ofReal (by linarith : A.1+B.2 ≤ B.1+B.2)).trans hB.2.2.1
      have h1 := hD.2.2.2 (B.1,A.2) hB.1 hA.2.1 hcap1
      have h2 := hE.2.2.2 (A.1,B.2) hA.1 hB.2.1 hcap2
      have hc := cost_cross C hS.assumption2.differentiableOn hS.assumption2.convexOn hA.1 hA.2.1 hac hbd
      dsimp only [objB3, Prod.fst, Prod.snd] at h1 h2 ⊢
      linarith
    · have h1 := hD.2.2.2 B hB.1 hB.2.1 hB.2.2.1
      have h2 := hE.2.2.2 A hA.1 hA.2.1 hA.2.2.1
      have hg := hG hB.2.1 hA.2.1 (le_of_not_ge hbd)
      dsimp only [objB3] at h1 h2 ⊢
      linarith
  · have hca : B.1 ≤ A.1 := le_of_not_ge hac
    by_cases hbd : A.2 ≤ B.2
    · have h1 := hD.2.2.2 A hA.1 hA.2.1 hA.2.2.1
      have h2 := hE.2.2.2 B hB.1 hB.2.1 hB.2.2.1
      have hf := hF hB.1 hA.1 hca
      dsimp only [objB3] at h1 h2 ⊢
      nlinarith
    · have hdb : B.2 ≤ A.2 := le_of_not_ge hbd
      have hcap1 : ENNReal.ofReal (A.1+B.2) ≤ Abar :=
        (ENNReal.ofReal_le_ofReal (by linarith : A.1+B.2 ≤ A.1+A.2)).trans hA.2.2.1
      have hcap2 : ENNReal.ofReal (B.1+A.2) ≤ Abar :=
        (ENNReal.ofReal_le_ofReal (by linarith : B.1+A.2 ≤ A.1+A.2)).trans hA.2.2.1
      have h1 := hD.2.2.2 (A.1,B.2) hA.1 hB.2.1 hcap1
      have h2 := hE.2.2.2 (B.1,A.2) hB.1 hA.2.1 hcap2
      have hc := cost_cross C hS.assumption2.differentiableOn hS.assumption2.convexOn hB.1 hB.2.1 hca hdb
      have hf := hF hB.1 hA.1 hca
      have hg := hG hB.2.1 hA.2.1 hdb
      dsimp only [objB3, Prod.fst, Prod.snd] at h1 h2 ⊢
      nlinarith

end AttentionB3

theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (d' : ℝ) (hd' : 0 ≤ d')
    (Abar : ℝ≥0∞) (_hAbar : 0 < Abar) (Astar : ℝ → ℝ → ℝ → ℝ × ℝ)
    (hA : ∀ x : ℝ, 0 < x → ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d →
      IsB3Max u C Abar d' x y d (Astar x y d)) :
    ∀ x : ℝ, 0 < x → ∀ y₁ y₂ : ℝ, 0 < y₁ → y₁ < y₂ →
      AntitoneOn (fun d => objB3 u C d' x y₂ d (Astar x y₂ d).1 (Astar x y₂ d).2 -
        objB3 u C d' x y₁ d (Astar x y₁ d).1 (Astar x y₁ d).2) (Ici 0) := by
  intro x hx y z hy hyz d hd e he hde
  have hz : 0 < z := hy.trans hyz
  have h := AttentionB3.value_cross u C hS d' hd' Abar hx hy hz hyz.le hd he hde
    (hA x hx y hy d hd) (hA x hx z hz e he) (hA x hx y hy e he) (hA x hx z hz d hd)
  linarith

#print axioms solution
