-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:11.152302+00:00
-- url     : https://prove2.me/theorems/c56c1e1c-bf46-4bd4-8033-3fa223ea5a2a
-- title:
--   Position Update Sums
-- statement:
--   Definitions and structural lemmas for Position Update Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
section Slot
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
def flipA (a : S) (u : Ix S) : Ix S := Function.update u a (Fin.rev (u a))
end Slot
section Vec
variable {A S V : Type} [Ring A] [Fintype S] [DecidableEq S] [AddCommGroup V] [Module A V]
end Vec
end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums


