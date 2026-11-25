-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:57:19.43873+00:00
-- url     : https://prove2.me/theorems/1f0d3af5-fdf9-488a-88dc-95e0d29075da
-- title:
--   Block PSDCongr
-- statement:
--   Definitions and structural lemmas for Block PSDCongr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockPSDCongr.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
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
section gram
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end gram
end
end Formalism.FourierDecayAlt.P.PBK


