-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:27.71278+00:00
-- url     : https://prove2.me/theorems/2004fe09-1ffe-43c6-bde6-feae8370ee2c
-- title:
--   Capelli Abstract Character
-- statement:
--   Definitions and structural lemmas for Capelli Abstract Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_main
import Theorems.Thm_PI_QmLemDWork_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
def IsPol {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) (f : ℂ → X) : Prop :=
  ∃ c : ℕ → X, ∀ u : ℂ, f u = ∑ s ∈ Finset.range d, (u ^ s) • c s
def shiftC {X : Type} [Zero X] (c : ℕ → X) : ℕ → X
  | 0 => 0
  | s + 1 => c s
section pol
variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
end pol
section ring
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
theorem isCov_zero : IsCov E (fun _ => (0 : A)) := by
  intro a b c
  simp
theorem isCov_add {η η' : Fin n → A} (h : IsCov E η) (h' : IsCov E η') : IsCov E (fun j => η j + η' j) := by
  intro a b c
  rw [mul_add, add_mul]
  rw [show ∀ x y z w : A, x + y - (z + w) = (x - z) + (y - w) from fun x y z w => by abel, h a b c, h' a b c]
  split_ifs <;> simp
theorem isCov_smul (k : ℂ) {η : Fin n → A} (h : IsCov E η) : IsCov E (fun j => k • η j) := by
  intro a b c
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, h a b c]
  split_ifs <;> simp
end ring
section cov
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
def Th (u : ℂ) : Module.End ℂ (Fin (N + 1) → V) :=
  LinearMap.pi fun x => ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) •
    (qminor E a.succAbove x.succAbove u ∘ₗ LinearMap.proj a)
def EE : Module.End ℂ (Fin (N + 1) → V) := LinearMap.pi fun j => ∑ l, E j l ∘ₗ LinearMap.proj l
def Gd (v : V) : Submodule ℂ (Fin (N + 1) → V) where
  carrier := {X | ∃ η : Fin (N + 1) → Module.End ℂ V, IsCov E η ∧ ∀ j, X j = η j v}
  add_mem' := by
    rintro X Y ⟨η, hη, hX⟩ ⟨η', hη', hY⟩
    exact ⟨_, isCov_add hη hη', fun j => by simp [hX, hY]⟩
  zero_mem' := ⟨_, isCov_zero, fun j => by simp⟩
  smul_mem' := by
    rintro k X ⟨η, hη, hX⟩
    exact ⟨_, isCov_smul k hη, fun j => by simp [hX]⟩
end cov
section main
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
def KK : Module.End ℂ (Fin (N + 1) → V) := ((N : ℂ) + 1) • 1 - EE E
end main
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter


