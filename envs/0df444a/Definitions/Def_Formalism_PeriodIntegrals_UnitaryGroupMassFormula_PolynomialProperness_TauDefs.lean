-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:13.967162+00:00
-- url     : https://prove2.me/theorems/8db74d6e-afde-4d00-b315-9d248f788016
-- title:
--   Tau Defs
-- statement:
--   Definitions and structural lemmas for Tau Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/TauDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.PolynomialProperness
def MXFacts : Prop :=
  ∀ (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ), vX ∈ UTset r →
    mX k r vX ∈ Nset k r ∧ (∀ p : Fin r → ℂ, mX k r vX *ᵥ xiV k r p = xiV k r (vX *ᵥ p)) ∧
    ∀ w : Fin (2 * r + k + 1) → ℂ, inWb k r w → mX k r vX *ᵥ w = w
def NEFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ ξ : Fin r → ℂ,
    nEich k r z ξ ∈ Nset k r ∧ (∀ p : Fin r → ℂ, nEich k r z ξ *ᵥ xiV k r p = xiV k r p) ∧
    nEich k r z ξ *ᵥ z = z + xiV k r ξ
end PI.PolynomialProperness


