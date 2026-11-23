-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:49.408806+00:00
-- url     : https://prove2.me/theorems/931827df-fce6-4c24-8d65-fe2d908eb747
-- title:
--   Schur Step
-- statement:
--   Definitions and structural lemmas for Schur Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/SchurStep.lean

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
namespace PI.UnitaryGroupMassFormula.CommMult
open Matrix
def SchurStep : Prop :=
  ∀ (G : Type) [Group G] (M : ℕ) (σ : G →* GL (Fin M) ℂ), PI.UMultOne.Irr σ →
    ∀ C : Matrix (Fin M) (Fin M) ℂ,
      (∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * C = C * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      ∃ c : ℂ, C = c • (1 : Matrix (Fin M) (Fin M) ℂ)
def InjStep : Prop :=
  ∀ (G : Type) [Group G] (N M : ℕ) (π : G →* GL (Fin N) ℂ) (σ : G →* GL (Fin M) ℂ), PI.UMultOne.Irr σ →
    ∀ T : Matrix (Fin N) (Fin M) ℂ,
      (∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      T ≠ 0 → ∃ X : Matrix (Fin M) (Fin N) ℂ, X * T = 1
def AvStep : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    (N M : ℕ) (π : H →* GL (Fin N) ℂ) (σ : H →* GL (Fin M) ℂ),
    PI.UMultOne.Cont π → PI.UMultOne.Cont σ →
    ∀ (T : Matrix (Fin N) (Fin M) ℂ) (X : Matrix (Fin M) (Fin N) ℂ),
      (∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      X * T = 1 →
      ∃ S : Matrix (Fin M) (Fin N) ℂ,
        (∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * S = S * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) ∧
        S * T = 1
end PI.UnitaryGroupMassFormula.CommMult


