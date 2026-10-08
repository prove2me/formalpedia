-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.exists_primitive_of_polyInt_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:13.276809+00:00
-- url     : https://prove2.me/submissions/feb051a7-325d-45be-8478-4e6419ed4ad1

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_append
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_reverse
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_exists_polyIn_of_isConnected

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

/-- Parametrisation of a segment in `ℂ`. -/
lemma pk_mem_segment_iff (a b z : ℂ) :
    z ∈ segment ℝ a b ↔ ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ a + (t : ℂ) * (b - a) = z := by
  rw [segment_eq_image' ℝ a b]
  simp [Complex.real_smul]

lemma pk_polyInt_append' (g : ℂ → ℂ) {l : List ℂ} {a : ℂ} (m : List ℂ)
    (h : l.getLast? = some a) :
    polyInt g (l ++ m) = polyInt g l + polyInt g (a :: m) := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at h
  exact polyInt_append g hl (List.cons_ne_nil a m) h

lemma pk_polyIn_append_aux {U : Set ℂ} (x : ℂ) (l : List ℂ) (a : ℂ) (m : List ℂ)
    (h : (x :: l).getLast? = some a) (hl : PolyIn U (x :: l)) (hm : PolyIn U (a :: m)) :
    PolyIn U ((x :: l) ++ m) := by
  induction l generalizing x with
  | nil =>
    have hx : x = a := by simpa using h
    subst hx
    simpa using hm
  | cons y l ih =>
    have h' : (y :: l).getLast? = some a := by
      simpa [List.getLast?_cons_cons] using h
    have e1 : (x :: y :: l) ++ m = x :: y :: (l ++ m) := rfl
    rw [e1, polyIn_cons_cons]
    exact ⟨hl.1, ih y h' hl.2⟩

lemma pk_polyIn_append' {U : Set ℂ} {l : List ℂ} {a : ℂ} (m : List ℂ)
    (h : l.getLast? = some a) (hl : PolyIn U l) (hm : PolyIn U (a :: m)) :
    PolyIn U (l ++ m) := by
  cases l with
  | nil => simp at h
  | cons x l => exact pk_polyIn_append_aux x l a m h hl hm

lemma pk_polyIn_reverse {U : Set ℂ} (l : List ℂ) (hl : PolyIn U l) : PolyIn U l.reverse := by
  induction l with
  | nil => exact hl
  | cons a t ih =>
    cases t with
    | nil => simpa using hl
    | cons b rest =>
      have hlast : (b :: rest).reverse.getLast? = some b := by simp
      rw [polyIn_cons_cons] at hl
      rw [List.reverse_cons]
      refine pk_polyIn_append' [a] hlast (ih hl.2) ?_
      rw [polyIn_cons_cons, polyIn_singleton]
      refine ⟨?_, ?_⟩
      · rw [segment_symm]; exact hl.1
      · exact hl.1 (left_mem_segment ℝ a b)

lemma pk_seg_integrand_continuousOn {U : Set ℂ} {g : ℂ → ℂ} (hg : ContinuousOn g U) {a b : ℂ}
    (hab : segment ℝ a b ⊆ U) :
    ContinuousOn (fun t : ℝ => g (a + (t : ℂ) * (b - a)) * (b - a)) (uIcc (0 : ℝ) 1) := by
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, a + (t : ℂ) * (b - a) ∈ U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hab ((pk_mem_segment_iff a b _).2 ⟨t, ht, rfl⟩)
  refine ContinuousOn.mul ?_ continuousOn_const
  exact hg.comp (by fun_prop : Continuous fun t : ℝ => a + (t : ℂ) * (b - a)).continuousOn hmem

/-- If closed polygon integrals vanish, the integral along a polygon from `z₀` to `z` depends
only on the endpoints. -/
lemma pk_polyInt_path_indep {Ω : Set ℂ} {g : ℂ → ℂ}
    (h0 : ∀ l : List ℂ, IsClosedPoly l → PolyIn Ω l → polyInt g l = 0)
    {z₀ z : ℂ} {l₁ l₂ : List ℂ}
    (h₁ : PolyIn Ω l₁) (h₁h : l₁.head? = some z₀) (h₁l : l₁.getLast? = some z)
    (h₂ : PolyIn Ω l₂) (h₂h : l₂.head? = some z₀) (h₂l : l₂.getLast? = some z) :
    polyInt g l₁ = polyInt g l₂ := by
  have hrev : l₂.reverse.head? = some z := by rw [List.head?_reverse]; exact h₂l
  obtain ⟨r, hr⟩ : ∃ r, l₂.reverse = z :: r := by
    cases h : l₂.reverse with
    | nil => rw [h] at hrev; simp at hrev
    | cons y r => rw [h] at hrev; simp at hrev; exact ⟨r, by rw [hrev]⟩
  have hrevIn : PolyIn Ω (z :: r) := hr ▸ pk_polyIn_reverse l₂ h₂
  have hclosedIn : PolyIn Ω (l₁ ++ r) := pk_polyIn_append' r h₁l h₁ hrevIn
  have hlastzr : (z :: r).getLast? = some z₀ := by
    rw [← hr, List.getLast?_reverse]; exact h₂h
  have hheadc : (l₁ ++ r).head? = some z₀ := by simp [List.head?_append, h₁h]
  have hlastc : (l₁ ++ r).getLast? = some z₀ := by
    rw [List.getLast?_append, h₁l]
    rcases hrl : r.getLast? with _ | w
    · rw [List.getLast?_cons, hrl] at hlastzr
      simpa using hlastzr
    · rw [List.getLast?_cons, hrl] at hlastzr
      simpa using hlastzr
  have hclosed : IsClosedPoly (l₁ ++ r) := by
    refine ⟨?_, by rw [hheadc, hlastc]⟩
    intro h
    rw [h] at hheadc
    simp at hheadc
  have := h0 _ hclosed hclosedIn
  rw [pk_polyInt_append' g r h₁l, ← hr, polyInt_reverse] at this
  linear_combination this

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {g : ℂ → ℂ} (hg : ContinuousOn g Ω)
    (h0 : ∀ l : List ℂ, IsClosedPoly l → PolyIn Ω l → polyInt g l = 0) :
    ∃ G : ℂ → ℂ, ∀ z ∈ Ω, HasDerivAt G (g z) z := by
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  choose! P hP using fun z (hz : z ∈ Ω) => exists_polyIn_of_isConnected hΩo hΩc hz₀ hz
  refine ⟨fun z => polyInt g (P z), ?_⟩
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo z hz
  have hsegball : ∀ z' ∈ Metric.ball z r, segment ℝ z z' ⊆ Ω := fun z' hz' =>
    ((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hz').trans hball
  have step : ∀ z' ∈ Metric.ball z r,
      polyInt g (P z') = polyInt g (P z) + segInt g z z' := by
    intro z' hz'
    have hz'Ω := hball hz'
    obtain ⟨hPz, hPzh, hPzl⟩ := hP z hz
    obtain ⟨hPz', hPz'h, hPz'l⟩ := hP z' hz'Ω
    have hin : PolyIn Ω (P z ++ [z']) := pk_polyIn_append' [z'] hPzl hPz ⟨hsegball z' hz', hz'Ω⟩
    have hh : (P z ++ [z']).head? = some z₀ := by simp [List.head?_append, hPzh]
    have := pk_polyInt_path_indep h0 hin hh (by simp) hPz' hPz'h hPz'l
    rw [pk_polyInt_append' g [z'] hPzl] at this
    rw [← this, polyInt_cons_cons]
    simp
  have hgc : ContinuousAt g z := hg.continuousAt (hΩo.mem_nhds hz)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hgc ε hε
  filter_upwards [Metric.ball_mem_nhds z (lt_min hr hδ)] with z' hz'
  have hz'r : z' ∈ Metric.ball z r := Metric.ball_subset_ball (min_le_left _ _) hz'
  have hz'δ : dist z' z < δ := lt_of_lt_of_le (Metric.mem_ball.1 hz') (min_le_right _ _)
  have hseg := hsegball z' hz'r
  show ‖polyInt g (P z') - polyInt g (P z) - (z' - z) • g z‖ ≤ ε * ‖z' - z‖
  rw [step z' hz'r, smul_eq_mul]
  have e : polyInt g (P z) + segInt g z z' - polyInt g (P z) - (z' - z) * g z
      = ∫ t in (0 : ℝ)..1, (g (z + (t : ℂ) * (z' - z)) - g z) * (z' - z) := by
    have hi := (pk_seg_integrand_continuousOn hg hseg).intervalIntegrable
      (μ := MeasureTheory.volume)
    have : ∫ t in (0 : ℝ)..1, (g (z + (t : ℂ) * (z' - z)) - g z) * (z' - z)
        = segInt g z z' - (z' - z) * g z := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub hi (by simp)]
      simp [segInt]
      ring
    rw [this]; ring
  rw [e]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ε * ‖z' - z‖) (f := fun t : ℝ => (g (z + (t : ℂ) * (z' - z)) - g z) * (z' - z)) ?_
  · simpa using hb
  · intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hd : dist (z + (t : ℂ) * (z' - z)) z < δ := by
      have : dist (z + (t : ℂ) * (z' - z)) z = t * ‖z' - z‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ht.1.le]
      rw [this]
      calc (t : ℝ) * ‖z' - z‖ ≤ 1 * ‖z' - z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = dist z' z := by rw [one_mul, dist_eq_norm]
        _ < δ := hz'δ
    have h2 := hδg hd
    rw [dist_eq_norm] at h2
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)

#print axioms solution
