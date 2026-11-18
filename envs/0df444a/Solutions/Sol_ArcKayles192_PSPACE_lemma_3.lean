-- Prove2me | solution 1 for ArcKayles192.PSPACE.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:07:14.768365+00:00
-- url     : https://prove2.me/submissions/9a526641-35d3-40a2-a3f1-b620332ab0b7

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

open ArcKayles192.PSPACE

namespace AKAux3

variable {V : Type*} [DecidableEq V]

lemma sg_eq (G : SimpleGraph V) (S : Finset V) :
    sg G S = mex {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x} := by
  rw [sg]

lemma fpw_eq (G : SimpleGraph V) (S : Finset V) :
    FirstPlayerWins G S ↔ ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, ¬ FirstPlayerWins G (S \ {u, v}) := by
  rw [FirstPlayerWins]

lemma sg_zero_iff (G : SimpleGraph V) (S : Finset V) :
    sg G S = 0 ↔ ¬ ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = 0 := by
  rw [sg_eq]
  unfold mex
  constructor
  · intro h ⟨u, v, hh, hz⟩
    have : (0 : ℕ) ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x} :=
      ⟨u, v, hh, hz⟩
    have hmem : sInf {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ ∈
        {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      apply Nat.sInf_mem
      apply Set.Infinite.nonempty
      apply Set.Finite.infinite_compl
      apply Set.Finite.subset ((S ×ˢ S).finite_toSet.image (fun p : V × V => sg G (S \ {p.1, p.2})))
      rintro x ⟨u, v, ⟨hu, hv, _⟩, rfl⟩
      exact ⟨(u, v), by simp [hu, hv], rfl⟩
    rw [h] at hmem
    exact hmem this
  · intro h
    apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    intro ⟨u, v, hh, hz⟩
    exact h ⟨u, v, hh, hz⟩

end AKAux3

theorem solution {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ¬ FirstPlayerWins G S ↔ sg G S = 0 := by
  induction' hn : S.card using Nat.strong_induction_on with n ih generalizing S
  rw [AKAux3.sg_zero_iff, AKAux3.fpw_eq]
  have key : ∀ u v, ∀ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v,
      (¬ FirstPlayerWins G (S \ {u, v}) ↔ sg G (S \ {u, v}) = 0) := by
    intro u v h
    exact ih _ (hn ▸ card_sdiff_pair_lt _ h.1) (S \ {u, v}) rfl
  constructor
  · intro h ⟨u, v, hh, hz⟩
    exact h ⟨u, v, hh, (key u v hh).2 hz⟩
  · intro h ⟨u, v, hh, hz⟩
    exact h ⟨u, v, hh, (key u v hh).1 hz⟩
