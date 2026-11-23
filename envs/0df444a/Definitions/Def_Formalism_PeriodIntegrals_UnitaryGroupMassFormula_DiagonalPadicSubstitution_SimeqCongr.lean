-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:51.63068+00:00
-- url     : https://prove2.me/theorems/5ee7b81c-9550-4424-a1d7-3c84e311f7a2
-- title:
--   Simeq Congr
-- statement:
--   Definitions and structural lemmas for Simeq Congr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/SimeqCongr.lean

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
namespace PI.BeDiagZp
def IntSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    IntegralMv f → IntegralMv (MvPowerSeries.subst s f)
namespace Asm
variable {p : ℕ} [Fact p.Prime]
end Asm
open Asm
end PI.BeDiagZp


