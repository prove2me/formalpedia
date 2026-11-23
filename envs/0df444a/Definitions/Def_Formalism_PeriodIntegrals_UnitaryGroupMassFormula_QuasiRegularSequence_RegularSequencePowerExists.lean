-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_RegularSequencePowerExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_RegularSequencePowerExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:54.460987+00:00
-- url     : https://prove2.me/theorems/762bf04f-4e67-40fd-a145-8fe1b60eacb4
-- title:
--   Regular Sequence Power Exists
-- statement:
--   Definitions and structural lemmas for Regular Sequence Power Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuasiRegularSequence/RegularSequencePowerExists.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_StepPowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI.RSQR
open MvPolynomial
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R] {n : ℕ}
def lowSet (n i : ℕ) : Set (Fin n) := {j | (j : ℕ) < i}
theorem isHom_iff {σ : Type*} {F : MvPolynomial σ R} {k : ℕ} :
    F.IsHomogeneous k ↔ ∀ d, F.coeff d ≠ 0 → Finsupp.degree d = k := by
  rw [Finsupp.degree_eq_weight_one]; rfl
theorem C_mem_sup {σ : Type*} {s : Set σ} (c : R) : (C c : MvPolynomial σ R) ∈ supported R s := by
  rw [← MvPolynomial.algebraMap_eq]; exact (supported R s).algebraMap_mem c
def T (x : Fin n → R) (s : Set (Fin n)) (k : ℕ) (J : Ideal R) : Ideal R where
  carrier := {a | ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous k ∧ F ∈ supported R s ∧
    (∀ m, F.coeff m ∈ J) ∧ eval x F = a}
  add_mem' := by
    rintro a b ⟨F, h1, h2, h3, rfl⟩ ⟨G, g1, g2, g3, rfl⟩
    exact ⟨F + G, h1.add g1, add_mem h2 g2,
      fun m => by rw [coeff_add]; exact add_mem (h3 m) (g3 m), by simp⟩
  zero_mem' := ⟨0, isHom_iff.2 (fun d hd => by simp at hd), zero_mem _, fun m => by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨F, h1, h2, h3, rfl⟩
    exact ⟨C c * F, h1.C_mul c, mul_mem (C_mem_sup c) h2,
      fun m => by rw [coeff_C_mul]; exact J.mul_mem_left c (h3 m), by simp⟩
end SlopeTestRemainingChoices
end PI.RSQR


