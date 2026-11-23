-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:12.501049+00:00
-- url     : https://prove2.me/theorems/902f4285-a004-49e4-8cb7-867172f1108b
-- title:
--   Step ACleared
-- statement:
--   Definitions and structural lemmas for Step ACleared, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
def RInvA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) : Prop :=
  ∀ (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a b : Fin (n + 1)) (t : ℂ), a < b → b.val < n →
    φ (lhwline_rowOp a b t x) = φ x
def stepA (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b ∧ b.val < n) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y
def elimA : ℕ → (Fin (n + 1) × Fin (n + 1) → ℂ) → (Fin (n + 1) × Fin (n + 1) → ℂ)
  | 0, x => x
  | k + 1, x =>
    if h : k < n then stepA ⟨k, by omega⟩ ⟨k, by omega⟩ (elimA k x) else elimA k x
def clearedA (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ (a j : Fin (n + 1)), a.val < n → a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0
end PI.WGB


