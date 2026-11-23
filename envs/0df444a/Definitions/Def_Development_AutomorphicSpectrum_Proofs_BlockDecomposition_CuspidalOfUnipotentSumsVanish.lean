-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:50.212267+00:00
-- url     : https://prove2.me/theorems/62f5473f-ead4-45ba-9a89-7e06041901dd
-- title:
--   Cuspidal Of Unipotent Sums Vanish
-- statement:
--   Definitions and structural lemmas for Cuspidal Of Unipotent Sums Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalOfUnipotentSumsVanish.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.CuspIff
def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }
end GlobalTheory.CompanionTheory.TyFin.CuspIff


