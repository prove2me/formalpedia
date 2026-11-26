-- Prove2me | solution 1 for Arxiv2610_39302.platonic_representation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T07:37:56.143618+00:00
-- url     : https://prove2.me/submissions/c1da7509-09c8-4778-b790-6a2daa7d2a5d

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open Matrix MeasureTheory

namespace PLX
open Arxiv2610_39302

lemma mod_eq {Z X : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (π : Z → Z → ℝ)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal) (g : Z → X)
    (f : X → Fin k → ℝ) : modalityLoss p π ℓ Om g f = worldLoss p π ℓ Om (fun z => f (g z)) := rfl

lemma min_transfer {Z X : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (π : Z → Z → ℝ)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal) (g : Z → X)
    (hg : Function.Injective g) (f : X → Fin k → ℝ)
    (hf : ∀ f' : X → Fin k → ℝ, modalityLoss p π ℓ Om g f ≤ modalityLoss p π ℓ Om g f') :
    ∀ h'', worldLoss p π ℓ Om (fun z => f (g z)) ≤ worldLoss p π ℓ Om h'' := by
  intro h''
  have := hf (Function.extend g h'' 0)
  rw [mod_eq, mod_eq] at this
  have e : (fun z => Function.extend g h'' 0 (g z)) = h'' := funext fun z => hg.extend_apply _ _ _
  rwa [e] at this

end PLX

open PLX Arxiv2610_39302 MeasureTheory in
theorem solution {Z ι : Type*} [Fintype Z] [Fintype ι] {k : ℕ}
    (hM : 2 ≤ Fintype.card ι) (X : ι → Type*)
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal)
    (hObj : IsJEPAObjective p ℓ Om)
    (g : ∀ m, Z → X m) (hg : ∀ m, Function.Injective (g m))
    (huniq : UniqueUpToRotation (worldLoss p π ℓ Om)) :
    ∃ hstar : Z → Fin k → ℝ,
      (∀ m (f : X m → Fin k → ℝ),
        (∀ f' : X m → Fin k → ℝ, modalityLoss p π ℓ Om (g m) f ≤ modalityLoss p π ℓ Om (g m) f') →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, f (g m z) = rot Q (hstar z)) ∧
      (∀ m m' (f : X m → Fin k → ℝ) (f' : X m' → Fin k → ℝ),
        (∀ f'' : X m → Fin k → ℝ, modalityLoss p π ℓ Om (g m) f ≤ modalityLoss p π ℓ Om (g m) f'') →
        (∀ f'' : X m' → Fin k → ℝ,
          modalityLoss p π ℓ Om (g m') f' ≤ modalityLoss p π ℓ Om (g m') f'') →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, f (g m z) = rot Q (f' (g m' z))) := by
  classical
  have part2 : ∀ m m' (f : X m → Fin k → ℝ) (f' : X m' → Fin k → ℝ),
      (∀ f'' : X m → Fin k → ℝ, modalityLoss p π ℓ Om (g m) f ≤ modalityLoss p π ℓ Om (g m) f'') →
      (∀ f'' : X m' → Fin k → ℝ,
        modalityLoss p π ℓ Om (g m') f' ≤ modalityLoss p π ℓ Om (g m') f'') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, f (g m z) = rot Q (f' (g m' z)) :=
    fun m m' f f' hf hf' =>
      huniq _ _ (min_transfer p π ℓ Om (g m') (hg m') f' hf') (min_transfer p π ℓ Om (g m) (hg m) f hf)
  by_cases hex : ∃ h0 : Z → Fin k → ℝ, ∀ h'', worldLoss p π ℓ Om h0 ≤ worldLoss p π ℓ Om h''
  · obtain ⟨h0, hh0⟩ := hex
    exact ⟨h0, fun m f hf => huniq _ _ hh0 (min_transfer p π ℓ Om (g m) (hg m) f hf), part2⟩
  · refine ⟨0, fun m f hf => ?_, part2⟩
    exact absurd ⟨_, min_transfer p π ℓ Om (g m) (hg m) f hf⟩ hex
