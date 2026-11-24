-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:30.616416+00:00
-- url     : https://prove2.me/theorems/5cceb6a8-2042-4ee3-8b93-505e489a0e73
-- title:
--   Pr Star Fst
-- statement:
--   Definitions and structural lemmas for Pr Star Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
section Act
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
def actP (M : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : Ix S → V := fun a => ∑ b, (M a b).1 (X b)
end Act
end Formalism.FourierDecayAlt.P.PBF


