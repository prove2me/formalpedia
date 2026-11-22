-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:22.203322+00:00
-- url     : https://prove2.me/theorems/dd5debe7-e9b9-4228-a6d8-284be10d1209
-- title:
--   Rename Pull LCoef Out
-- statement:
--   Definitions and structural lemmas for Rename Pull LCoef Out, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
def pullL : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K :=
  lsup fun ζ => monomial (D.pullE j ζ) 1
variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
end TwistData
end Formalism.MainNotions.PlaneGram


