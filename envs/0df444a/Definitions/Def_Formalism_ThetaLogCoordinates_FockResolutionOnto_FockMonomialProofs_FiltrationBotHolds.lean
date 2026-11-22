-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:33.20906+00:00
-- url     : https://prove2.me/theorems/3d85eb67-da63-4704-8939-b2aa77a03d95
-- title:
--   Filtration Bot Holds
-- statement:
--   Definitions and structural lemmas for Filtration Bot Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type}
noncomputable def grMap (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  ((LinearMap.mulLeft ℚ_[p] (X v ^ e : MvPolynomial σ ℚ_[p])).restrictScalars ℤ_[p]) ∘ₗ initL p v 0
end Gen
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
end Last
end Formalism.InvariantFactorPaths.L4


