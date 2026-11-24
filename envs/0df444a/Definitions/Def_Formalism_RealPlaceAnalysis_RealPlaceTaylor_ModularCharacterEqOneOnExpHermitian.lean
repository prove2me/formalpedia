-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:45.776805+00:00
-- url     : https://prove2.me/theorems/64e1cf05-3f85-4da7-bfb6-45f032de3d46
-- title:
--   Modular Character Eq One On Exp Hermitian
-- statement:
--   Definitions and structural lemmas for Modular Character Eq One On Exp Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Theorems.Thm_Formalism_REAL_indefinite_unitary_inv_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
namespace Formalism.REAL
def indefiniteUnitaryMk {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) : UJ ε :=
  ⟨⟨m, Jm ε * mᴴ * Jm ε, (indefinite_unitary_inv_closed n ε m h).1, (indefinite_unitary_inv_closed n ε m h).2⟩, h⟩
abbrev modularCharacterAlt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : ℝ≥0 := Measure.modularCharacterFun g
end Formalism.REAL


