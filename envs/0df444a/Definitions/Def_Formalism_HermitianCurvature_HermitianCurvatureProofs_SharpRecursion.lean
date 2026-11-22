-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:01.693189+00:00
-- url     : https://prove2.me/theorems/b129c774-ec9a-416e-b158-81bc9b9ea597
-- title:
--   Sharp Recursion
-- statement:
--   Definitions and structural lemmas for Sharp Recursion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Rec
open Finset Real
noncomputable def Pp (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, √(1 + e l)
end Formalism.FourierDecayAlt.P.Rec
namespace Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.Rec
end Formalism.FourierDecayAlt.P


