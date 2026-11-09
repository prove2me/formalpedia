-- Prove2me | Definitions.Def_CEPolytopeHard_Assumption_2_2
-- name    : CEPolytopeHard_Assumption_2_2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:10.357357+00:00
-- url     : https://prove2.me/theorems/80abe6bc-1739-4311-a78c-4d88a3020d68
-- title:
--   Assumption 2.2 (PCP-for-PPAD)
-- statement:
--   **Assumption 2.2 (PCP-for-PPAD).** There are absolute constants $0 < \tau < 1/4$ and $0 < \gamma < 1$ such that the following problem is PPAD-hard: given a generalized circuit with fan-out two, compute an assignment satisfying at least $(1 - \gamma)d$ gates at tolerance $\tau$.
--
--   It is a proposition, used only as the hypothesis of Theorem 4(ii); the mission does not assert it. (Footnote 1 of the paper: a proof has been claimed but is not yet verified, so the paper states (ii) conditionally.)
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Assumption 2.2, p.13

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_CEPolytopeHard_gcircuitProblem

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Assumption 2.2 (PCP-for-PPAD)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Assumption 2.2, p.13: "There are absolute constants
0 < τ < 1/4 and 0 < γ < 1 such that the following problem is PPAD-hard: given a generalized
circuit with fan-out two, compute an assignment satisfying at least (1 − γ)d gates at tolerance
τ"). A proposition, used as a hypothesis of Theorem 4(ii); it is not asserted. -/
def Assumption_2_2 : Prop :=
  ∃ τ γ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧ 0 < γ ∧ γ < 1 ∧ PPADHard (gcircuitProblem τ γ)

end CEPolytopeHard


