-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:53.951242+00:00
-- url     : https://prove2.me/theorems/8f566f83-b4d0-4aec-8c19-d584d956b1d9
-- title:
--   Constant Coeff Subst Eq Zero
-- statement:
--   Definitions and structural lemmas for Constant Coeff Subst Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
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
namespace PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
def CC {σ : Type} (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, Continuous fun c => MvPowerSeries.coeff n (G c)
end PI.BeDiagZp.ContPf
namespace PI.BeDiagZp
open ContPf
end PI.BeDiagZp


