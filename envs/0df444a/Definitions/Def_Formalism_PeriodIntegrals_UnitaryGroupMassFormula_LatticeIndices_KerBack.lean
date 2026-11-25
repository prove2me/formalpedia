-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:46.230871+00:00
-- url     : https://prove2.me/theorems/6ff382e3-456d-4430-a5a8-3f034549bd5b
-- title:
--   Ker Back
-- statement:
--   Definitions and structural lemmas for Ker Back, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/KerBack.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
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
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)
end MassDataIdxCore


