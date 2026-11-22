-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_DualMu
-- name    : Formalism_QuotientMetricDivisors_DualMu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:53.610464+00:00
-- url     : https://prove2.me/theorems/b791dac7-ff3a-45c7-bcc5-05c22b7d5ed5
-- title:
--   Dual Mu
-- statement:
--   Definitions and structural lemmas for Dual Mu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/DualMu.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.DivisionValues
def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D
end Formalism.DivisionValues


