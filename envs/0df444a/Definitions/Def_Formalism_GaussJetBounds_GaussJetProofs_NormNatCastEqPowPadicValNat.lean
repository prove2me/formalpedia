-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
-- name    : Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:39.259604+00:00
-- url     : https://prove2.me/theorems/31183f09-9fc0-421f-8b24-43d7a90d5b38
-- title:
--   Norm Nat Cast Eq Pow Padic Val Nat
-- statement:
--   Definitions and structural lemmas for Norm Nat Cast Eq Pow Padic Val Nat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
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
universe u v
namespace Formalism.DworkPowerSeriesWeights
section Norms
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Norms
end Formalism.DworkPowerSeriesWeights


