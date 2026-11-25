-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:59.960933+00:00
-- url     : https://prove2.me/theorems/5446dff4-ddc7-4b18-93a4-2465f9956692
-- title:
--   Pair Matrix Second Split
-- statement:
--   Definitions and structural lemmas for Pair Matrix Second Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K)
def pm (a b : Matrix n n K) : Matrix n n T := Matrix.of fun i j => θ.symm (a i j, b i j)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T) (P : GL n K)
end MassDataIdxCore


