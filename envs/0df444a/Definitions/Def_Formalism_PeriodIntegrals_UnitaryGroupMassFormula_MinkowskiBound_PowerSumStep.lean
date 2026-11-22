-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:11.95097+00:00
-- url     : https://prove2.me/theorems/d0688f83-8ed9-4218-b8dc-87c18f2dfa7a
-- title:
--   Power Sum Step
-- statement:
--   Definitions and structural lemmas for Power Sum Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSumStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Mk
open Matrix
def TraceStep : Prop :=
  ∀ (N ℓ a : ℕ), ℓ.Prime → ∀ g : Matrix (Fin N) (Fin N) ℤ, g ^ (ℓ ^ a) = 1 →
    ∃ y : ℕ, y ≤ N / (ℓ - 1) ∧ g.trace = (N : ℤ) - (ℓ : ℤ) * (y : ℤ) ∧ (y = 0 → g = 1)
def PowerSumStep : Prop :=
  ∀ (N : ℕ) (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (k : ℕ),
    (Fintype.card P : ℤ) ∣ ∑ g : P, (Matrix.trace ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) :
      Matrix (Fin N) (Fin N) ℤ)) ^ k
def PGroupStep : Prop :=
  ∀ (N ℓ : ℕ), ℓ.Prime → ∀ P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ), Finite P →
    IsPGroup ℓ P → Nat.card P ∣ ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial
end PI.Mk


