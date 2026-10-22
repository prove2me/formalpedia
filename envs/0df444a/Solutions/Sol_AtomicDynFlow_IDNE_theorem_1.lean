-- Prove2me | solution 1 for AtomicDynFlow.IDNE.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:52:45.868987+00:00
-- url     : https://prove2.me/submissions/5d72af42-1944-4130-abea-0352db0f2e61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium
import Theorems.Thm_AtomicDynFlow_IDNE_special_seq_exists
import Theorems.Thm_AtomicDynFlow_IDNE_theorem_EC_2
import Theorems.Thm_AtomicDynFlow_IDNE_idne_is_ne

open AtomicDynFlow.IDNE

theorem solution {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) :
    ∃ p : A → List E, (∀ a, G.IsStrategy a (p a)) ∧ G.IsIDNE p ∧ G.IsNE p := by
  obtain ⟨σ, p, hsp⟩ := special_seq_exists G
  have hid : G.IsIDNEWith σ p := theorem_EC_2 G σ p hsp
  exact ⟨p, hid.1, ⟨σ, hid⟩, idne_is_ne G p ⟨σ, hid⟩⟩
