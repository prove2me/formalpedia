-- Prove2me | Definitions.Def_ShiQMACenteredGapDominatingSchedule
-- name    : ShiQMACenteredGapDominatingSchedule
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-02T01:01:18.594973+00:00
-- url     : https://prove2.me/theorems/6da184d5-6369-4dae-aa7c-a0d6908ddd9c
-- title:
--   Polynomial schedule for the concrete QMA amplifier generator
-- statement:
--   Defines a monomial schedule parameter and a derived polynomial parameter for the concrete uniform amplifier.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L11-L12; https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L26-L29

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false

namespace ShiQMACenteredGap

noncomputable def schedulePolynomial (A D : Nat) : Polynomial ℕ :=
  Polynomial.monomial D (2 ^ A)
noncomputable def gapPolynomial (q p : Polynomial ℕ) : Polynomial ℕ :=
  schedulePolynomial
    (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4)
    (3 * q.natDegree + p.natDegree)

end ShiQMACenteredGap


