-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:30.561665+00:00
-- url     : https://prove2.me/theorems/e0c3f877-c433-4965-b938-8eb2b19933d3
-- title:
--   Transfer Step
-- statement:
--   Definitions and structural lemmas for Transfer Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/TransferStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UConjT
open Matrix
def OnbReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
    Module.finrank ℂ E = m → ∀ T : E →ₗ[ℂ] E, (∀ x y, inner ℂ (T x) (T y) = inner ℂ x y) →
    ∀ e : E, ∃ b : Fin m → E, Orthonormal ℂ b ∧ (∀ i, ∃ c : ℂ, T (b i) = c • b i) ∧
      ∀ i, (inner ℂ (b i) e).im = 0
def SpecReal : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ →
    ∃ u ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∃ d : Fin (n + 1) → ℂ,
      g * u = u * Matrix.diagonal d ∧ ∀ i, (u (Fin.last n) i).im = 0
def TransferStep : Prop := OnbReal → SpecReal
def BlockStep : Prop := SpecReal → PI.UMultOne.ConjTranspose
end PI.UConjT


