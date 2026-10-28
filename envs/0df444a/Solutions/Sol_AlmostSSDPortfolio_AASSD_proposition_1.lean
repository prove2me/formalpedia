-- Prove2me | solution 1 for AlmostSSDPortfolio.AASSD.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:00:37.120884+00:00
-- url     : https://prove2.me/submissions/97ce6f6a-2770-4d30-9829-9b18d6e0d761

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

noncomputable def Lin (fl fr dl dr z : ℝ) : ℝ := fl + (fr - fl) / (dr - dl) * (z - dl)

lemma max_le_lin (c dl dr z : ℝ) (h : dl < dr) (hz : dl ≤ z) (hz' : z ≤ dr) :
    max (z - c) 0 ≤ Lin (max (dl - c) 0) (max (dr - c) 0) dl dr z := by
  unfold Lin
  have hw : 0 < dr - dl := sub_pos.mpr h
  have e : max (dl - c) 0 + (max (dr - c) 0 - max (dl - c) 0) / (dr - dl) * (z - dl)
      = ((dr - z) * max (dl - c) 0 + (z - dl) * max (dr - c) 0) / (dr - dl) := by
    field_simp; ring
  rw [e, le_div_iff₀ hw]
  have h1 := le_max_left (dl - c) 0
  have h2 := le_max_left (dr - c) 0
  have h3 := le_max_right (dl - c) 0
  have h4 := le_max_right (dr - c) 0
  have a1 : 0 ≤ dr - z := by linarith
  have a2 : 0 ≤ z - dl := by linarith
  have m1 := mul_nonneg a1 (sub_nonneg.mpr h1)
  have m2 := mul_nonneg a2 (sub_nonneg.mpr h2)
  have m3 := mul_nonneg a1 h3
  have m4 := mul_nonneg a2 h4
  rcases le_total (z - c) 0 with hc | hc
  · rw [max_eq_right hc]; nlinarith
  · rw [max_eq_left hc]; nlinarith

lemma lpm_le_lin {T : Type*} [Fintype T] (p v : T → ℝ) (hp : ∀ t, 0 ≤ p t) (dl dr z : ℝ)
    (h : dl < dr) (hz : dl ≤ z) (hz' : z ≤ dr) :
    lpm p v z ≤ Lin (lpm p v dl) (lpm p v dr) dl dr z := by
  unfold lpm
  have key : ∀ t, p t * max (z - v t) 0 ≤
      p t * max (dl - v t) 0 + (p t * max (dr - v t) 0 - p t * max (dl - v t) 0) / (dr - dl) * (z - dl) := by
    intro t
    have := max_le_lin (v t) dl dr z h hz hz'
    unfold Lin at this
    have := mul_le_mul_of_nonneg_left this (hp t)
    calc _ ≤ _ := this
      _ = _ := by ring
  have := Finset.sum_le_sum (s := Finset.univ) (fun t _ => key t)
  unfold Lin
  simpa [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, Finset.sum_sub_distrib] using this

end AlmostSSDPortfolio.AASSD

open AlmostSSDPortfolio.AASSD

theorem solution {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∀ x : ℝ, S.F2 lam x ≤ D.hatF2 lam x := by
  intro x
  unfold Discretization.hatF2
  split_ifs with h
  · obtain ⟨hs1, hs2⟩ := h.choose_spec
    have hp : ∀ t, 0 ≤ S.p t := fun t => hS.2.1.1 t
    have hlt : D.d h.choose.castSucc < D.d h.choose.succ := D.strictMono (Fin.castSucc_lt_succ)
    have := lpm_le_lin S.p (S.ret lam) hp _ _ x hlt hs1 hs2
    exact this
  · exact le_refl _

