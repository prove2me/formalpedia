-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:10:11.776652+00:00
-- url     : https://prove2.me/theorems/fbe9394c-22eb-451a-991c-149d18761370
-- title:
--   Aestrongly Measurable Main D
-- statement:
--   Definitions and structural lemmas for Aestrongly Measurable Main D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
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
section abar
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def abar (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : ℝ := ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖
end abar
section moving
end moving
section cut
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end cut
end
end Formalism.FourierDecayAlt.P.PBK


