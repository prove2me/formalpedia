-- Prove2me | solution 1 for ArcKayles192.PSPACE.observation_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:07:15.281856+00:00
-- url     : https://prove2.me/submissions/c5217b07-487d-4cec-bf5e-cb2fdfd37fcd

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

open ArcKayles192.PSPACE

namespace AKAux

variable {V : Type*} [DecidableEq V]

lemma sg_eq (G : SimpleGraph V) (S : Finset V) :
    sg G S = mex {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x} := by
  rw [sg]

lemma opt_finite (G : SimpleGraph V) (S : Finset V) :
    {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}.Finite := by
  apply Set.Finite.subset ((S ×ˢ S).finite_toSet.image (fun p : V × V => sg G (S \ {p.1, p.2})))
  rintro x ⟨u, v, ⟨hu, hv, _⟩, rfl⟩
  exact ⟨(u, v), by simp [hu, hv], rfl⟩

lemma compl_nonempty (G : SimpleGraph V) (S : Finset V) :
    ({x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ).Nonempty := by
  have h := (opt_finite G S).infinite_compl
  exact h.nonempty

end AKAux

theorem solution {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    (∀ i < sg G S, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i) ∧
    (∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ sg G S) := by
  have hne := AKAux.compl_nonempty G S
  have hmex : sg G S = sInf {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
    rw [AKAux.sg_eq]; rfl
  constructor
  · intro i hi
    rw [hmex] at hi
    by_contra hcon
    have hmem : i ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      intro ⟨u, v, ⟨hu, hv, ha⟩, h⟩
      exact hcon ⟨u, v, hu, hv, ha, h⟩
    exact absurd (Nat.sInf_le hmem) (by omega)
  · intro u v hu hv ha h
    have hmem : sg G S ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      rw [hmex]; exact Nat.sInf_mem hne
    exact hmem ⟨u, v, ⟨hu, hv, ha⟩, h⟩
