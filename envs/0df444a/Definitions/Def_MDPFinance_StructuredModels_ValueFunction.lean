-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_ValueFunction
-- name    : MDPFinance_StructuredModels_ValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:36:41.886983+00:00
-- url     : https://prove2.me/theorems/91a2cda8-7bb2-4e5b-bf7d-67f09087f060
-- title:
--   The value function $V_n$ via the Bellman recursion (restated)
-- statement:
--   The **value function** $V_n(x)$, the maximal expected total reward attainable from time $n$
--   in state $x$, is given by the Bellman recursion $V_N = g_N$, $V_n = T_n V_{n+1}$ for $n =
--   N-1,\dots,0$ (equivalently, $V_n = T_n T_{n+1} \cdots T_{N-1} g_N$).
--
--   **Formalization Note.** This is the recursive characterization of $V_n$ established as
--   Theorem 2.3.8 (chunk `02a`), used here directly since Theorem 2.4.23 (the only result of this
--   mission referencing $V_n$) only needs the recursion, not the sup-over-policies primitive
--   definition and its supporting history/policy machinery.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 18, PDF 33 (unnumbered display) and p. 22, Theorem 2.3.8

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- Auxiliary for the value function: `k` applications of the maximal-reward operator starting
at time `n`, innermost first, i.e. `T_n T_{n+1} ⋯ T_{n+k-1}` applied to a terminal function.
Restated from `MDPFinance.Bellman.TChain` (chunk `02a`, "Auxiliary for Theorem 2.3.8b"). -/
noncomputable def TChain (M : MarkovDecisionModel E A N) : (k : ℕ) → (n : ℕ) → (E → EReal) →
    (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => T M n (TChain M k (n + 1) v)

/-- The value function `V_n(x)`, the maximal expected total reward from time `n` in state `x`
(Bäuerle–Rieder, p. 18, PDF 33, unnumbered display, `V_n(x) := sup_π V_n^π(x)`). Given here via
its recursive characterization `V_N = g_N`, `V_n = T_n V_{n+1}`, established as Theorem 2.3.8
(chunk `02a`) rather than by re-deriving the sup-over-policies primitive definition and its
supporting history/policy machinery, which this chunk's results (Theorem 2.4.23) do not need
beyond the recursion itself (see `MODERATION_NOTES.md`). -/
noncomputable def V (M : MarkovDecisionModel E A N) (n : ℕ) : E → EReal :=
  TChain M (N - n) n (fun x => (M.g x : EReal))

end MDPFinance.StructuredModels


