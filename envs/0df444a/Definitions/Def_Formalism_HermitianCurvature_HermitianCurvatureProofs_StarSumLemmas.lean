-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:13:15.9653+00:00
-- url     : https://prove2.me/theorems/a4390dda-88b4-4442-a232-975b7fa3daed
-- title:
--   Star Sum Lemmas
-- statement:
--   Definitions and structural lemmas for Star Sum Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
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
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
section ring
variable {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → A)
def Tch (u : ℂ) (j l : Fin (N + 1)) : A :=
  ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • qminor E j.succAbove l.succAbove u
theorem vec_add {y z : Fin (N + 1) → A} (hy : IsVec E y) (hz : IsVec E z) : IsVec E (fun l => y l + z l) := by
  intro a b c
  have h1 := hy a b c
  have h2 := hz a b c
  simp only [mul_add, add_mul]
  rw [add_sub_add_comm, h1, h2]
  split_ifs <;> simp [add_comm]
theorem vec_smul (k : ℂ) {y : Fin (N + 1) → A} (hy : IsVec E y) : IsVec E (fun l => k • y l) := by
  intro a b c
  have h1 := hy a b c
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← smul_sub, h1]
  split_ifs <;> simp
end ring
section abs
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end abs
section mod
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
def Gd (v : V) : Submodule ℂ (Fin (N + 1) → V) where
  carrier := {x | ∃ y : Fin (N + 1) → Module.End ℂ V, IsVec E y ∧ ∀ l, x l = y l v}
  add_mem' := by
    rintro x x' ⟨y, hy, hx⟩ ⟨y', hy', hx'⟩
    exact ⟨_, vec_add E hy hy', fun l => by rw [Pi.add_apply, hx, hx']; rfl⟩
  zero_mem' := ⟨fun _ => 0, fun a b c => by simp, fun l => rfl⟩
  smul_mem' := by
    rintro k x ⟨y, hy, hx⟩
    exact ⟨_, vec_smul E k hy, fun l => by rw [Pi.smul_apply, hx]; rfl⟩
def EE : Module.End ℂ (Fin (N + 1) → V) := LinearMap.pi fun l => ∑ c, (E c l) ∘ₗ LinearMap.proj c
def MM (T : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) : Module.End ℂ (Fin (N + 1) → V) :=
  LinearMap.pi fun j => ∑ l, (T j l) ∘ₗ LinearMap.proj l
end mod
end Formalism.FourierDecayAlt.P.DeterminantVectorSums


