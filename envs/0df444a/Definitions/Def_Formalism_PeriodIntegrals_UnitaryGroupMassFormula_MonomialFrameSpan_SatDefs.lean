-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:32.446088+00:00
-- url     : https://prove2.me/theorems/b1a36b8e-900c-493a-ba3e-a105e5799948
-- title:
--   Sat Defs
-- statement:
--   Definitions and structural lemmas for Sat Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace GenFrameSpan
open CutKW
def ProjZ : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 : ℕ) (nu : Lt → YoungDiagram),
    ∃ T : MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      (∀ P, T P ∈ Submodule.span ℤ (Set.range (nablaX N0 nu))) ∧ ∀ J, T (nablaX N0 nu J) = nablaX N0 nu J
end GenFrameSpan


