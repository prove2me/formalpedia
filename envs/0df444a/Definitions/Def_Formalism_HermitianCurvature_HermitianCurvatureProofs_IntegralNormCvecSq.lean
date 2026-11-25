-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:51.31023+00:00
-- url     : https://prove2.me/theorems/ee2bffa1-90a2-4c1b-bf3b-9368665d1eee
-- title:
--   Integral Norm Cvec Sq
-- statement:
--   Definitions and structural lemmas for Integral Norm Cvec Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
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
section cpic
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def cvec (s : ℕ) (F : ℂ → ℂ → H) (x c : ℂ) : H :=
  (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x (c / x ^ (s - 1))
end cpic
section cpicMain
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end cpicMain
end
end Formalism.FourierDecayAlt.P.PBK


