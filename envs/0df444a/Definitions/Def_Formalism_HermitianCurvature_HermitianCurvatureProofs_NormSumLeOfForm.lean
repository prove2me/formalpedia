-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:15.610285+00:00
-- url     : https://prove2.me/theorems/6f1cc7e2-fba5-41f0-9405-9b4d528a8740
-- title:
--   Norm Sum Le Of Form
-- statement:
--   Definitions and structural lemmas for Norm Sum Le Of Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities
open Finset
open scoped ComplexConjugate InnerProductSpace
noncomputable section
section hilbert
variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
end hilbert
end
end Formalism.FourierDecayAlt.P.FormNormSumIdentities


