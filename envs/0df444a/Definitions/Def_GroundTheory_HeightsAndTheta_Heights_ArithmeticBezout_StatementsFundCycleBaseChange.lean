-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:05.396233+00:00
-- url     : https://prove2.me/theorems/1538d962-a930-404a-a011-2900d8b1e469
-- title:
--   Statements Fund Cycle Base Change
-- statement:
--   Definitions and structural lemmas for Statements Fund Cycle Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsFundCycleBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))
end GroundTheory.Heights₂.Heights


