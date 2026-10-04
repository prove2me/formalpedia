-- Prove2me | solution 1 for AppliedComb.InclExcl.inclusion_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:03:54.900237+00:00
-- url     : https://prove2.me/submissions/9ef7c779-4a4a-408a-80be-411e1b6a2c75

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N

set_option autoImplicit false

open AppliedComb.InclExcl in
theorem solution {X : Type*} [Fintype X] (m : ℕ) (P : Fin m → X → Prop)
    [∀ i, DecidablePred (P i)] :
    ((Finset.univ.filter (fun x : X => ∀ i : Fin m, ¬ P i x)).card : ℤ) =
      ∑ S : Finset (Fin m), (-1 : ℤ) ^ S.card * (N P S : ℤ) := by
  classical
  have h := Finset.inclusion_exclusion_card_inf_compl (Finset.univ : Finset (Fin m))
    (fun i => Finset.univ.filter (fun x : X => P i x))
  have h1 : (Finset.univ.inf fun i => (Finset.univ.filter (fun x : X => P i x))ᶜ)
      = Finset.univ.filter (fun x : X => ∀ i : Fin m, ¬ P i x) := by
    ext x; simp [Finset.mem_inf]
  have h2 : ∀ t : Finset (Fin m), (t.inf fun i => Finset.univ.filter (fun x : X => P i x))
      = Finset.univ.filter (fun x : X => ∀ i ∈ t, P i x) := by
    intro t; ext x; simp [Finset.mem_inf]
  rw [h1] at h
  rw [h, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h2 t]
  unfold N
  congr 2
