-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:24.716386+00:00
-- url     : https://prove2.me/theorems/96c13aa3-3298-4a8e-a015-dcef7b1ce8ea
-- title:
--   Gram Conjugation Norm
-- statement:
--   Definitions and structural lemmas for Gram Conjugation Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
section gram
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end gram
section words
variable {W : Type} [Fintype W]
end words
end Formalism.FourierDecayAlt.P.GramConjugationNorm
namespace Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt.TA Formalism.FourierDecayAlt.P.GramConjugationNorm
open scoped InnerProductSpace ComplexConjugate
end Formalism.FourierDecayAlt.P


