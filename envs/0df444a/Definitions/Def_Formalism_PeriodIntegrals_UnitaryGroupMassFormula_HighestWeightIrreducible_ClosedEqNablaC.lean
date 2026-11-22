-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:37.528845+00:00
-- url     : https://prove2.me/theorems/7a8c5c67-b44e-46fa-8ba1-4858598507e4
-- title:
--   Closed Eq Nabla C
-- statement:
--   Definitions and structural lemmas for Closed Eq Nabla C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ClosedEqNablaC.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def StableClosedC : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N) (U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    U ≤ nablaSq ℂ N lam → (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) →
    RowDivClosed U
def FixedKilledC : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ f ∈ nablaSq ℂ N lam,
    (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
    ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k f = 0
def HWInClosedC : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ), M ≤ dualWeyl ℂ r n ν → RowDivClosed M → M ≠ ⊥ →
      hw ℂ hn ν ∈ M
def ClosedEqNablaC : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ), M ≤ dualWeyl ℂ r n ν → RowDivClosed M →
      hw ℂ hn ν ∈ M → M = dualWeyl ℂ r n ν
end PI.WHw


