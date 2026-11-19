-- Prove2me | solution 1 for AehligSchwichtenberg2002.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:34:05.175193+00:00
-- url     : https://prove2.me/submissions/6a709561-395f-4b9a-9823-a54dd7212bd4

import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002.Prop36Aux
open AehligSchwichtenberg2002

def Canon (t : Term) : Ty → Prop
  | .diamond => ∃ x : Var, x.ty = .diamond ∧ t = .var x
  | .bool => t = .const .tt ∨ t = .const .ff
  | .list _ => IsListTerm t
  | .prod _ _ => ∃ a b, t = .pair a b
  | .tensor τ ρ => ∃ a b, t = .app (.app (.const (.tensorPair τ ρ)) a) b
  | .lolli A B => (∃ x b, t = .lam x b) ∨ (∃ c, t = .const c ∧ c.ty = .lolli A B) ∨
      (∃ τ d, t = .app (.const (.cons τ)) d ∧ A = τ ∧ B = .lolli (.list τ) (.list τ)) ∨
      (∃ τ d a, t = .app (.app (.const (.cons τ)) d) a ∧ A = .list τ ∧ B = .list τ) ∨
      (∃ τ ρ a, t = .app (.const (.tensorPair τ ρ)) a ∧ A = ρ ∧ B = .tensor τ ρ) ∨
      (∃ l s, t = .app l (.brace s) ∧ IsListTerm l ∧ A = B)

theorem listCases (l : Term) (h : IsListTerm l) :
    (∃ τ, l = .const (.nil τ)) ∨
      ∃ τ d a l', l = .app (.app (.app (.const (.cons τ)) d) a) l' ∧ IsListTerm l' := by
  obtain ⟨n, hn⟩ := h
  unfold listEntryCount at hn
  split at hn
  · exact Or.inl ⟨_, rfl⟩
  · rename_i τ d a l'
    refine Or.inr ⟨τ, d, a, l', rfl, ?_⟩
    split at hn
    · rename_i k hk; exact ⟨k, hk⟩
    · simp at hn
  · simp at hn

theorem normal_left {t s : Term} (h : IsNormal (.app t s)) : IsNormal t :=
  fun ⟨t', ht⟩ => h ⟨_, RedStep.appLeft s ht⟩

theorem normal_right {t s : Term} (h : IsNormal (.app t s)) : IsNormal s :=
  fun ⟨s', hs⟩ => h ⟨_, RedStep.appRight t hs⟩

theorem not_normal {t t' : Term} (h : ConvStep t t') : ¬ IsNormal t :=
  fun hn => hn ⟨t', RedStep.conv h⟩

theorem canon {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    (∀ v ∈ Γ, v.ty = .diamond) → IsNormal t → Canon t τ := by
  induction h with
  | var x hx =>
    intro hac _
    have hxd : x.ty = .diamond := hac x ((hx.2 x).2 (Or.inr (by simp)))
    rw [hxd]; exact ⟨x, hxd, rfl⟩
  | const _ c =>
    intro _ _
    cases c with
    | tt => exact Or.inl rfl
    | ff => exact Or.inr rfl
    | nil τ => exact ⟨0, rfl⟩
    | cons τ => exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
    | tensorPair τ ρ => exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | lam x _ _ _ => intro _ _; exact Or.inl ⟨_, _, rfl⟩
  | @app Γ₁ Γ₂ Γ t s τ ρ hd ht hs iht ihs =>
    intro hac hn
    have hac1 : ∀ v ∈ Γ₁, v.ty = .diamond := fun v hv => hac v ((hd.2 v).2 (Or.inl hv))
    have hac2 : ∀ v ∈ Γ₂, v.ty = .diamond := fun v hv => hac v ((hd.2 v).2 (Or.inr hv))
    have ct := iht hac1 (normal_left hn)
    rcases ct with ⟨x, b, rfl⟩ | ⟨c, rfl, hc⟩ | ⟨τ', d, rfl, rfl, rfl⟩ |
        ⟨τ', d, a, rfl, rfl, rfl⟩ | ⟨τ', ρ', a, rfl, rfl, rfl⟩ | ⟨l, s', rfl, hl, rfl⟩
    · exact absurd hn (not_normal (ConvStep.beta x b s))
    · cases c with
      | tt => simp [Constructor.ty] at hc
      | ff => simp [Constructor.ty] at hc
      | nil _ => simp [Constructor.ty] at hc
      | cons τ' =>
        simp only [Constructor.ty, Ty.lolli.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Or.inr (Or.inr (Or.inl ⟨τ', s, rfl, rfl, rfl⟩))
      | tensorPair τ' ρ' =>
        simp only [Constructor.ty, Ty.lolli.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨τ', ρ', s, rfl, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, d, s, rfl, rfl, rfl⟩)))
    · obtain ⟨k, hk⟩ : IsListTerm s := ihs hac2 (normal_right hn)
      exact ⟨k + 1, by simp [listEntryCount, hk]⟩
    · exact ⟨a, s, rfl⟩
    · rcases listCases l hl with ⟨τ', rfl⟩ | ⟨τ', d, a, l', rfl, hl'⟩
      · exact absurd hn (not_normal (ConvStep.iterNil τ' s' s))
      · exact absurd hn (not_normal (ConvStep.iterCons τ' d a l' s' s hl'))
  | pair _ _ _ _ => intro _ _; exact ⟨_, _, rfl⟩
  | @projLeft Γ t τ ρ ht iht =>
    intro hac hn
    obtain ⟨a, b, rfl⟩ := iht hac (normal_left hn)
    exact absurd hn (not_normal (ConvStep.projTt a b))
  | @projRight Γ t τ ρ ht iht =>
    intro hac hn
    obtain ⟨a, b, rfl⟩ := iht hac (normal_left hn)
    exact absurd hn (not_normal (ConvStep.projFf a b))
  | @boolElim Γ₁ Γ₂ Γ t s r τ hd ht _ _ iht _ _ =>
    intro hac hn
    have hac1 : ∀ v ∈ Γ₁, v.ty = .diamond := fun v hv => hac v ((hd.2 v).2 (Or.inl hv))
    rcases iht hac1 (normal_left hn) with rfl | rfl
    · exact absurd hn (not_normal (ConvStep.ifTt s r))
    · exact absurd hn (not_normal (ConvStep.ifFf s r))
  | @tensorElim Γ₁ Γ₂ Γ₂' Γ t s x y σ hxy _ hd ht _ iht _ =>
    intro hac hn
    have hac1 : ∀ v ∈ Γ₁, v.ty = .diamond := fun v hv => hac v ((hd.2 v).2 (Or.inl hv))
    obtain ⟨a, b, rfl⟩ := iht hac1 (normal_left hn)
    exact absurd hn (not_normal (ConvStep.tensorBeta x.ty y.ty a b x y s rfl rfl hxy))
  | @listElim Γ t s τ ρ ht _ iht _ =>
    intro hac hn
    have hl : IsListTerm t := iht hac (normal_left hn)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, s, rfl, hl, rfl⟩))))

end AehligSchwichtenberg2002.Prop36Aux

open AehligSchwichtenberg2002 AehligSchwichtenberg2002.Prop36Aux in
theorem solution {Γ : Context} {t : Term}
    (hac : ∀ v ∈ Γ, v.ty = .diamond) (hnorm : IsNormal t) :
    (∀ τ : Ty, HasType Γ t (.list τ) → IsListTerm t) ∧
    (HasType Γ t .bool → t = .const .tt ∨ t = .const .ff) ∧
    (HasType Γ t .diamond → ∃ x : Var, x.ty = .diamond ∧ t = .var x) :=
  ⟨fun _ h => canon h hac hnorm, fun h => canon h hac hnorm, fun h => canon h hac hnorm⟩
