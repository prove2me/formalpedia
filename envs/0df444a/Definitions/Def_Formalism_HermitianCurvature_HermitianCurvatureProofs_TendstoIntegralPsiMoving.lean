-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:42:22.917522+00:00
-- url     : https://prove2.me/theorems/8bb54d5f-f871-4ba9-8e95-cb99bc8279b3
-- title:
--   Tendsto Integral Psi Moving
-- statement:
--   Definitions and structural lemmas for Tendsto Integral Psi Moving, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def freq (β w : ℂ) : ℂ := ((2 * Real.pi)⁻¹ : ℝ) • (-(conj (β * w)))
end
end Formalism.FourierDecayAlt.P.PBK


