-- Prove2me | Definitions.Def_CLRS_Chapter4_Master_CaseTwo
-- name    : CLRS_Chapter4_Master_CaseTwo
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:03:07.541893+00:00
-- url     : https://prove2.me/theorems/6620dc18-d697-4c38-bba9-bca74a13a05c
-- title:
--   Canonical real logarithmic tolls for the critical master case
-- statement:
--   The canonical real extension of the logarithmic toll is x^p*(max(0,log x))^q. On every natural input it equals n^p*(log n)^q, where log is the natural logarithm and real powers use Lean’s total definitions. Clamping the logarithm affects only the bounded real interval below one. Elementary nonnegativity and comparison facts support the critical master-theorem case, including noninteger q. Substantial summation and recurrence bounds are separate theorem nodes.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Master.CaseTwo, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Master/CaseTwo.lean

import Definitions.Def_CLRS_Chapter4_Master_Basic
import Definitions.Def_CLRS_Chapter4_Master_Rounding
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Computability.AkraBazzi.AkraBazzi
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
# The critical case of the master theorem

The logarithmic exponent is a real number. The summation estimate is proved by
comparing each summand with the increment of an antiderivative, then telescoping.
-/

open Filter Asymptotics Finset Real
open scoped Topology

namespace Chapter4Master







/-- A nonnegative real extension of the critical-case toll. The `max` affects
only the bounded real interval below one, never its values on natural inputs. -/
noncomputable def logarithmicToll (p k x : ℝ) : ℝ :=
  x ^ p * (max 0 (log x)) ^ k















end Chapter4Master

end CLRS


