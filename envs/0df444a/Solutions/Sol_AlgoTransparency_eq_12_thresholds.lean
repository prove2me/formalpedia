-- Prove2me | solution 1 for AlgoTransparency.eq_12_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:20:59.3324+00:00
-- url     : https://prove2.me/submissions/0093d161-9fd0-439d-b4e5-e34771a526d4

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_marginO
import Definitions.Def_AlgoTransparency_marginT

namespace Aux_AlgoT_eq12

theorem thr (H L α R e c : ℝ) (hM : 0 < H + L) (hα : 0 < α) (hc : c = R - e) :
    (H * (α + e - R) + L * (e - R) = 0 ↔ H / (H + L) = c / α) ∧
    (0 < H * (α + e - R) + L * (e - R) ↔ c / α < H / (H + L)) ∧
    (H * (α + e - R) + L * (e - R) < 0 ↔ H / (H + L) < c / α) := by
  subst hc
  have hM' : H + L ≠ 0 := hM.ne'
  have hα' : α ≠ 0 := hα.ne'
  have key : H * (α + e - R) + L * (e - R) =
      ((H + L) * α) * (H / (H + L) - (R - e) / α) := by
    field_simp <;> ring
  have hp : 0 < (H + L) * α := mul_pos hM hα
  rw [key]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hp.ne'
      · exact sub_eq_zero.1 h
    · intro h
      rw [h, sub_self, mul_zero]
  · constructor
    · intro h
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.2 hc)
      linarith
    · intro h
      exact mul_pos hp (sub_pos.2 h)
  · constructor
    · intro h
      by_contra hc
      push_neg at hc
      have := mul_nonneg hp.le (sub_nonneg.2 hc)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hp (sub_neg.2 h)

end Aux_AlgoT_eq12

open AlgoTransparency in
theorem solution (p : Params) (hp : Standing p) :
    (0 < (p.R - p.β) / p.α ∧ (p.R - p.β) / p.α < p.R / p.α ∧ p.R / p.α < 1) ∧
    (∀ (qH qL : ℝ) (S : OState), 0 < massHO p qH S + massLO p qL S →
      let γ := massHO p qH S / (massHO p qH S + massLO p qL S)
      let γth : ℝ := match S with
        | .A => p.R / p.α
        | .B => (p.R - p.β) / p.α
        | .C => p.R / p.α
        | .D => (p.R - p.β) / p.α
      (marginO p qH qL S = 0 ↔ γ = γth) ∧ (0 < marginO p qH qL S ↔ γth < γ) ∧
        (marginO p qH qL S < 0 ↔ γ < γth)) ∧
    (∀ (qH qL : ℝ) (S : TState), 0 < massHT p qH S + massLT p qL S →
      let γ := massHT p qH S / (massHT p qH S + massLT p qL S)
      let γth : ℝ := match S with
        | .E => p.R / p.α
        | .F => (p.R - p.β) / p.α
      (marginT p qH qL S = 0 ↔ γ = γth) ∧ (0 < marginT p qH qL S ↔ γth < γ) ∧
        (marginT p qH qL S < 0 ↔ γ < γth)) := by
  obtain ⟨_, _, ⟨hb0, hbR, hRa⟩, _, _⟩ := hp
  have hα : 0 < p.α := by linarith
  refine ⟨⟨div_pos (by linarith) hα, ?_, (div_lt_one hα).2 hRa⟩, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hα hα]
    nlinarith
  · intro qH qL S hpos
    cases S
    · exact Aux_AlgoT_eq12.thr (massHO p qH .A) (massLO p qL .A) p.α p.R 0 p.R hpos hα (by ring)
    · exact Aux_AlgoT_eq12.thr (massHO p qH .B) (massLO p qL .B) p.α p.R p.β (p.R - p.β) hpos hα
        rfl
    · exact Aux_AlgoT_eq12.thr (massHO p qH .C) (massLO p qL .C) p.α p.R 0 p.R hpos hα (by ring)
    · exact Aux_AlgoT_eq12.thr (massHO p qH .D) (massLO p qL .D) p.α p.R p.β (p.R - p.β) hpos hα
        rfl
  · intro qH qL S hpos
    cases S
    · exact Aux_AlgoT_eq12.thr (massHT p qH .E) (massLT p qL .E) p.α p.R 0 p.R hpos hα (by ring)
    · exact Aux_AlgoT_eq12.thr (massHT p qH .F) (massLT p qL .F) p.α p.R p.β (p.R - p.β) hpos hα
        rfl
