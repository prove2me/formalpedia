-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.polyInt_eq_sub_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:09.839471+00:00
-- url     : https://prove2.me/submissions/2bf624eb-748f-442b-9c6f-4fc23ebebcf7

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

/-- Parametrisation of a segment in `ℂ`. -/
lemma pk_mem_segment_iff (a b z : ℂ) :
    z ∈ segment ℝ a b ↔ ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ a + (t : ℂ) * (b - a) = z := by
  rw [segment_eq_image' ℝ a b]
  simp [Complex.real_smul]

lemma pk_seg_integrand_continuousOn {U : Set ℂ} {g : ℂ → ℂ} (hg : ContinuousOn g U) {a b : ℂ}
    (hab : segment ℝ a b ⊆ U) :
    ContinuousOn (fun t : ℝ => g (a + (t : ℂ) * (b - a)) * (b - a)) (uIcc (0 : ℝ) 1) := by
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, a + (t : ℂ) * (b - a) ∈ U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hab ((pk_mem_segment_iff a b _).2 ⟨t, ht, rfl⟩)
  refine ContinuousOn.mul ?_ continuousOn_const
  exact hg.comp (by fun_prop : Continuous fun t : ℝ => a + (t : ℂ) * (b - a)).continuousOn hmem

lemma pk_segInt_eq_sub {U : Set ℂ} {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U) {a b : ℂ}
    (hab : segment ℝ a b ⊆ U) : segInt g a b = G b - G a := by
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, a + (t : ℂ) * (b - a) ∈ U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hab ((pk_mem_segment_iff a b _).2 ⟨t, ht, rfl⟩)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (a + (s : ℂ) * (b - a))) (g (a + (t : ℂ) * (b - a)) * (b - a)) t := by
    intro t ht
    have h1 : HasDerivAt (fun w : ℂ => a + w * (b - a)) (b - a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b - a)).const_add a
    have h2 := (hG _ (hmem t ht)).comp (t : ℂ) h1
    exact h2.comp_ofReal
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (pk_seg_integrand_continuousOn hg hab).intervalIntegrable
  simpa [segInt] using this

lemma pk_polyInt_eq_sub_aux {U : Set ℂ} {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U) (x : ℂ) (l : List ℂ)
    (hl : PolyIn U (x :: l)) :
    polyInt g (x :: l) = G ((x :: l).getLast (List.cons_ne_nil _ _)) - G x := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
    rw [polyIn_cons_cons] at hl
    rw [polyInt_cons_cons, pk_segInt_eq_sub hG hg hl.1, ih y hl.2, List.getLast_cons_cons]
    ring

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution {U : Set ℂ} (hU : IsOpen U) {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U) {l : List ℂ}
    (hl : PolyIn U l) (hne : l ≠ []) :
    polyInt g l = G (l.getLast hne) - G (l.head hne) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x l => simpa using pk_polyInt_eq_sub_aux hG hg x l hl

#print axioms solution
