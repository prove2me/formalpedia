-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:48.5018+00:00
-- url     : https://prove2.me/theorems/146ffc57-f33f-4dbc-9a6f-8a8c140ecaa2
-- title:
--   Derivative Divided Integral
-- statement:
--   Definitions and structural lemmas for Derivative Divided Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section D
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end D
section U
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
noncomputable def DDop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  Wm p K a ∘ₗ eulW p K r + ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
end U
end Formalism.InvariantFactorPaths.L4


