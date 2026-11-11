-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_successProb
-- name    : GapAgnosticGS_OracleAlg_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:02.849316+00:00
-- url     : https://prove2.me/theorems/3d591860-589b-4a49-b411-992104fdb823
-- title:
--   Probability that an oracle algorithm halts with an output satisfying an event
-- statement:
--   For an adaptive oracle algorithm $\mathcal A$, an oracle $U$ and an event $E(o,\rho)$ on the classical output $o$ and the output state $\rho$,
--
--   $$\Pr[\mathcal A^U\text{ succeeds}]=\sum_{h:\ \mathcal A\text{ halts at }h\text{ with output }o,\ E(o,\rho_h)}\|\psi_h\|^2 .$$
--
--   Runs that never halt contribute nothing. Statements "with probability at least $1-\delta$, output $\rho$ with $\langle\phi_0|\rho|\phi_0\rangle\ge1-\epsilon$" are lower bounds on this quantity.
--
--   **Formalization Note** Valued in $[0,\infty]$ so that the infinite sum over histories is never a junk value.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3): "an algorithm outputs, with probability at least 1 − δ, a state ρ …"

import Definitions.Def_GapAgnosticGS_OracleAlg_outState

namespace GapAgnosticGS

open scoped ENNReal

open Classical in
/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3): "an algorithm outputs, with probability at least 1 − δ, a
state ρ satisfying …". The probability that the run of `A` with oracle `U` halts with a classical
output `o` and an output state `ρ` satisfying the event `E o ρ`: the sum, over the histories at
which `A` halts, of the squared norm of the branch vector, counted when the event holds.

**Formalization Note.** `ℝ≥0∞`-valued, so the infinite sum over histories is never a junk value.
Runs that never halt contribute nothing. -/
noncomputable def OracleAlg.successProb {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) (E : O → Matrix Y Y ℂ → Prop) :
    ℝ≥0∞ :=
  ∑' h : List ℕ, match A.step h with
    | .halt o => if E o (A.outState U h) then (‖A.branch U h‖₊ : ℝ≥0∞) ^ 2 else 0
    | _ => 0

end GapAgnosticGS


