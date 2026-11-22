-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:54.745593+00:00
-- url     : https://prove2.me/theorems/ed9afec6-1b9c-42dc-b862-5a6494f0f147
-- title:
--   Substituted Exponent Apply Label
-- statement:
--   Definitions and structural lemmas for Substituted Exponent Apply Label, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
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
variable {K : Type} [Field K] (D : TwistData K)
def GM (F : MvPolynomial (D.OL × Fin D.r) K) (M : D.EA) : MvPolynomial (D.OL × Fin D.r) K :=
  dg (fun α => (D.ga α)⁻¹) (ddiv M (D.gaAct F))
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
end TwistData
end Formalism.MainNotions.PlaneGram


