-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:49.190634+00:00
-- url     : https://prove2.me/theorems/3809b55d-9c2b-52a3-871a-c3877191c1e4
-- title:
--   Germ Loc Tail
-- statement:
--   Definitions and structural lemmas for Germ Loc Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocTail.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoRatioPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}
end
end Formalism.FourierDecayAlt.P.PBK


