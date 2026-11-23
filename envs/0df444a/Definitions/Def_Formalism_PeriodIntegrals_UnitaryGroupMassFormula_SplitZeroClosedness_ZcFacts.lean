-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:39.624022+00:00
-- url     : https://prove2.me/theorems/4b5b4482-7ec4-4acb-a745-b87b7ef796e2
-- title:
--   Zc Facts
-- statement:
--   Definitions and structural lemmas for Zc Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitZeroClosedness/ZcFacts.lean

import Definitions.Def_Formalism_PeriodIntegrals_SplitZeroG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.SZGW
def ZpSimeq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]),
    PI.BeDiagZp.ContPf.CC G → (∀ n : ℕ, PI.BeDiagZp.Simeq (G (n : ℂ_[p])) 0) →
    ∀ c : ℤ_[p], PI.BeDiagZp.Simeq (G (PI.BeDiagZp.zc c)) 0
def ZpInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]),
    PI.BeDiagZp.ContPf.CC G → (∀ n : ℕ, PI.BeDiagZp.IntegralMv (G (n : ℂ_[p]))) →
    ∀ c : ℤ_[p], PI.BeDiagZp.IntegralMv (G (PI.BeDiagZp.zc c))
def ZcFacts : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    (∀ a b : ℤ_[p], PI.BeDiagZp.zc (a * b) = PI.BeDiagZp.zc a * PI.BeDiagZp.zc b) ∧
    (∀ a b : ℤ_[p], PI.BeDiagZp.zc (a - b) = PI.BeDiagZp.zc a - PI.BeDiagZp.zc b) ∧
    PI.BeDiagZp.zc (1 : ℤ_[p]) = 1 ∧ PI.BeDiagZp.zc (-1 : ℤ_[p]) = -1 ∧ PI.BeDiagZp.zc (2 : ℤ_[p]) = 2 ∧
    IsUnit (2 : ℤ_[p])
end PI.SZGW


