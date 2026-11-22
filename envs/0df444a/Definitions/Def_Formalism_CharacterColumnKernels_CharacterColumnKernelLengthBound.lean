-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelLengthBound
-- name    : Formalism_CharacterColumnKernels_CharacterColumnKernelLengthBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:52.131734+00:00
-- url     : https://prove2.me/theorems/c3a866c7-0e93-401a-8ae3-99076d60b8a9
-- title:
--   Character Column Kernel Length Bound
-- statement:
--   Definitions and structural lemmas for Character Column Kernel Length Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/CharacterColumnKernelLengthBound.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.NG
def characterColumnKernelLengthBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ a b : ℕ, a < b → padicValInt l (x ^ b - x ^ a) = s₀ + padicValNat l (b - a)
def characterColumnKernelBlockBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
      padicValInt l (delta (fun i : Fin (t + 1) => u * x ^ (w + (i : ℕ)))) =
        t * s₀ + padicValNat l t.factorial
def characterColumnKernelLengthEquality : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
      padicValInt l (delta (fun i : Fin (t + 1) => u * x ^ (w + t - (i : ℕ)))) =
        t * s₀ + padicValNat l t.factorial
end Formalism.NG


