-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:32.182267+00:00
-- url     : https://prove2.me/theorems/86f51169-f1b1-4716-a2ad-5d45a193a019
-- title:
--   Free Action Expansion
-- statement:
--   Definitions and structural lemmas for Free Action Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
section Ops
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
end Ops
section Vec
variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]
end Vec
section Main
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
end Main
end Formalism.FourierDecayAlt.P.FreeActionExpansion


