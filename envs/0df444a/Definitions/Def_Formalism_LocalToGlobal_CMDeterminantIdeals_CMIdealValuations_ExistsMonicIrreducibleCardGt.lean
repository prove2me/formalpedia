-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:06.176537+00:00
-- url     : https://prove2.me/theorems/bc627aed-a13b-4e83-a140-8f88c46396b3
-- title:
--   Exists Monic Irreducible Card Gt
-- statement:
--   Definitions and structural lemmas for Exists Monic Irreducible Card Gt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsMonicIrreducibleCardGt.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open Polynomial IsLocalRing
def quotResidueEquiv {V : Type} [CommRing V] [IsLocalRing V] (g : V[X]) :
    AdjoinRoot g ⧸ Ideal.map (algebraMap V (AdjoinRoot g)) (maximalIdeal V) ≃+*
      AdjoinRoot (g.map (residue V)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal V) g
end Formalism.L2.LamCM


