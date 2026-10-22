-- Prove2me | solution 1 for AtomicDynFlow.IDNE.idne_is_ne
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:49:33.511141+00:00
-- url     : https://prove2.me/submissions/8c100e51-91b6-41fc-963e-b29653054ba3

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium

open AtomicDynFlow.IDNE

private lemma pathTo_last {V E : Type} (tail head : E → V) (d : V) :
    ∀ (P : List E) (v : V), PathTo tail head d v P → P ≠ [] → ∃ e ∈ P, head e = d := by
  intro P
  induction P with
  | nil => intro v _ h; exact absurd rfl h
  | cons e P ih =>
    intro v h _
    rcases h with ⟨_, hP⟩
    cases P with
    | nil => exact ⟨e, by simp, hP⟩
    | cons e' P' =>
      obtain ⟨f, hf, hfd⟩ := ih (head e) hP (by simp)
      exact ⟨f, List.mem_cons_of_mem _ hf, hfd⟩

private lemma onPath_d {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Instance V E A) (a : A) (P : List E) (h : G.IsStrategy a P) : G.OnPath a P G.d := by
  rcases h with ⟨e, _, hhead, hpath⟩ | ⟨r, v, hin, hpath⟩
  · right
    have hne : P ≠ [] := by
      intro hP; simp [hP] at hhead
    exact pathTo_last G.tail G.head G.d P _ hpath hne
  · by_cases hP : P = []
    · left
      subst hP
      have hv : v = G.d := hpath
      subst hv
      exact ⟨r, Or.inr hin⟩
    · right
      exact pathTo_last G.tail G.head G.d P _ hpath hP

theorem solution {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (p : A → List E)
    (h : G.IsIDNE p) : G.IsNE p := by
  obtain ⟨σ, hstrat, hinj, _, hopt⟩ := h
  refine ⟨hstrat, ?_⟩
  intro i P' hP'
  have hq : ∀ b, G.IsStrategy b (p b) := hstrat
  have key := hopt i G.d (onPath_d G i (p i) (hstrat i)) p hq (fun _ _ => rfl)
  rw [key]
  have hr : (∀ b, G.IsStrategy b (Function.update p i P' b)) ∧
      ∀ b, σ b < σ i → Function.update p i P' b = p b := by
    refine ⟨fun b => ?_, fun b hb => ?_⟩
    · by_cases hbi : b = i
      · subst hbi; simpa using hP'
      · simpa [Function.update_of_ne hbi] using hstrat b
    · have hbi : b ≠ i := by rintro rfl; exact lt_irrefl _ hb
      simp [Function.update_of_ne hbi]
  exact iInf₂_le_of_le i le_rfl (iInf₂_le_of_le (Function.update p i P') hr le_rfl)
