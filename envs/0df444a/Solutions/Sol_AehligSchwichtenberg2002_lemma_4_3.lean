-- Prove2me | solution 1 for AehligSchwichtenberg2002.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:15:21.973513+00:00
-- url     : https://prove2.me/submissions/936261c7-001c-49f2-a1d5-6cdbd39fcf38

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002.Lemma43Aux
open AehligSchwichtenberg2002

/-- Inhabitation of the set-theoretic reading with `⋄ = ∅`. -/
def Inh : Ty → Prop
  | .diamond => False
  | .bool => True
  | .lolli τ ρ => Inh τ → Inh ρ
  | .tensor τ ρ => Inh τ ∧ Inh ρ
  | .prod τ ρ => Inh τ ∧ Inh ρ
  | .list _ => True

theorem inh_of_typed {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    (∀ v ∈ freeVarOccurrences t, Inh v.ty) → Inh τ := by
  induction h with
  | var x _ => intro hv; exact hv x (by simp [freeVarOccurrences])
  | const _ c =>
    intro _
    cases c <;> simp [Constructor.ty, Inh]
    all_goals (intro a b; exact ⟨a, b⟩)
  | lam x _ _ ih =>
    intro hv hx
    apply ih
    intro v hvt
    by_cases hvx : v = x
    · subst hvx; exact hx
    · exact hv v (by simp [freeVarOccurrences, List.mem_filter, hvt, hvx])
  | app _ _ _ iht ihs =>
    intro hv
    exact iht (fun v h => hv v (by simp [freeVarOccurrences, h]))
      (ihs (fun v h => hv v (by simp [freeVarOccurrences, h])))
  | pair _ _ iht ihs =>
    intro hv
    exact ⟨iht (fun v h => hv v (by simp [freeVarOccurrences, h])),
      ihs (fun v h => hv v (by simp [freeVarOccurrences, h]))⟩
  | projLeft _ ih =>
    intro hv; exact (ih (fun v h => hv v (by simp [freeVarOccurrences, h]))).1
  | projRight _ ih =>
    intro hv; exact (ih (fun v h => hv v (by simp [freeVarOccurrences, h]))).2
  | boolElim _ _ _ _ _ ihs _ =>
    intro hv; exact ihs (fun v h => hv v (by simp [freeVarOccurrences, h]))
  | tensorElim x y hxy _ _ _ _ iht ihs =>
    intro hv
    have hxyI := iht (fun v h => hv v (by simp [freeVarOccurrences, h]))
    apply ihs
    intro v hvs
    by_cases hvx : v = x
    · subst hvx; exact hxyI.1
    by_cases hvy : v = y
    · subst hvy; exact hxyI.2
    exact hv v (by simp [freeVarOccurrences, List.mem_filter, hvs, hvx, hvy])
  | listElim _ _ _ _ => intro _; simp [Inh]

theorem fv_sub {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    ∀ v ∈ freeVarOccurrences t, v ∈ Γ := by
  induction h with
  | var x hx =>
    intro v hv
    simp [freeVarOccurrences] at hv; subst hv
    exact (hx.2 _).2 (Or.inr (by simp))
  | const _ c => intro v hv; simp [freeVarOccurrences] at hv
  | lam x hu _ ih =>
    intro v hv
    simp [freeVarOccurrences, List.mem_filter] at hv
    rcases (hu v).1 (ih v hv.1) with h | h
    · exact h
    · simp at h; exact absurd h hv.2
  | app hd _ _ iht ihs =>
    intro v hv
    simp [freeVarOccurrences] at hv
    rcases hv with h | h
    · exact (hd.2 v).2 (Or.inl (iht v h))
    · exact (hd.2 v).2 (Or.inr (ihs v h))
  | pair _ _ iht ihs =>
    intro v hv
    simp [freeVarOccurrences] at hv
    rcases hv with h | h
    · exact iht v h
    · exact ihs v h
  | projLeft _ ih => intro v hv; simp [freeVarOccurrences] at hv; exact ih v hv
  | projRight _ ih => intro v hv; simp [freeVarOccurrences] at hv; exact ih v hv
  | boolElim hd _ _ _ iht ihs ihr =>
    intro v hv
    simp [freeVarOccurrences] at hv
    rcases hv with h | h | h
    · exact (hd.2 v).2 (Or.inl (iht v h))
    · exact (hd.2 v).2 (Or.inr (ihs v h))
    · exact (hd.2 v).2 (Or.inr (ihr v h))
  | tensorElim x y _ h2 hd _ _ iht ihs =>
    intro v hv
    simp only [freeVarOccurrences, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hv
    rcases hv with h | ⟨⟨h, hy⟩, hx⟩
    · exact (hd.2 v).2 (Or.inl (iht v h))
    · rcases (h2.2 v).1 (ihs v h) with h' | h'
      · exact (hd.2 v).2 (Or.inr h')
      · simp at h'; rcases h' with h' | h'
        · exact absurd h' hx
        · exact absurd h' hy
  | listElim _ _ iht ihs =>
    intro v hv
    simp [freeVarOccurrences] at hv
    rcases hv with h | h
    · exact iht v h
    · exact absurd (ihs v h) (by simp)

end AehligSchwichtenberg2002.Lemma43Aux

open AehligSchwichtenberg2002 AehligSchwichtenberg2002.Lemma43Aux in
theorem solution {Γ : Context} {t : Term}
    (ht : HasType Γ t .diamond) :
    Γ ≠ [] ∧ freeVars t ≠ [] := by
  have hocc : freeVarOccurrences t ≠ [] := by
    intro h
    exact inh_of_typed ht (by simp [h])
  have hfv : freeVars t ≠ [] := by
    intro h
    apply hocc
    rcases hl : freeVarOccurrences t with _ | ⟨a, l⟩
    · rfl
    · have : a ∈ freeVars t := by
        simp only [freeVars]; rw [List.mem_eraseDups, hl]; simp
      rw [h] at this; simp at this
  refine ⟨?_, hfv⟩
  intro hΓ
  apply hocc
  rcases hl : freeVarOccurrences t with _ | ⟨a, l⟩
  · rfl
  · have := fv_sub ht a (by rw [hl]; simp)
    rw [hΓ] at this; simp at this
