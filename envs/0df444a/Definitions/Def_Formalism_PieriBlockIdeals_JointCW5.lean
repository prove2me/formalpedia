-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_JointCW5
-- name    : Formalism_PieriBlockIdeals_JointCW5
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:03.496231+00:00
-- url     : https://prove2.me/theorems/c4d02968-f8cd-4956-b0af-fc3dc1e9e8b2
-- title:
--   Joint CW5
-- statement:
--   Definitions and structural lemmas for Joint CW5, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/JointCW5.lean

import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CohomologicalDescent
open Formalism.RankGapBounds.ChebyshevFactorialBounds
def JointCW5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (τ : ι) (l : ℕ), l.Prime → τ ∈ D.T2 → D.Params → D.h < l ^ 2 →
    ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)) + (D.ecl τ l : ℝ) +
        labelLHS l D.k D.t (D.depth τ l : ℝ) (D.xlo τ) (D.xhi τ) (D.maxB τ) ≤
      Cor.coefficientBoundTau D τ l
end Formalism.CohomologicalDescent


