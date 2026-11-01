-- Prove2me | Definitions.Def_LocalDOvS_SUS_susGo
-- name    : LocalDOvS_SUS_susGo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:32.056419+00:00
-- url     : https://prove2.me/theorems/21f12424-914f-4d21-b6c8-40af9c9a4767
-- title:
--   Replay of the corrected algorithm on a history
-- statement:
--   The corrected shrinking uniform sampling algorithm, replayed on a history $h$ from a state:
--
--   1. while $|S|\ge3$: if some active point has fewer than $n(|S|)$ outputs in $h$, the next step is to simulate the first such point (lines 4–9); otherwise the test is made with the outputs of $h$ (lines 10–20) and the replay continues from the new state;
--   2. when $|S|\le2$: if some active point has fewer than $\max(\text{current},n_{\mathrm{fin}})$ outputs, simulate it (line 22); otherwise stop and return the final comparison (line 23).
--
--   It returns the state of the iteration in progress and the next step. At most $N$ tests can occur, since each removes at least one point.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, pp.15–16 (corrected)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_lookStep
import Definitions.Def_LocalDOvS_SUS_finalChoice
import Definitions.Def_LocalDOvS_SUS_ptVals
import Definitions.Def_LocalDOvS_SUS_Step

open scoped NNReal

namespace LocalDOvS.SUS

/-- The corrected shrinking uniform sampling algorithm, replayed on a history `h`
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, pp.15–16, corrected). From state `st`:

1. while `|S| ≥ 3`: if some active point `x` (the first in `S`) has fewer than `n(|S|)` outputs
   in `h`, the next step is to simulate `x` (lines 4–9); otherwise make the test `lookStep`
   with the outputs of `h` (lines 10–20) and continue from the new state;
2. when `|S| ≤ 2`: if some active point has fewer than `max(cnt x, n_fin)` outputs, simulate it
   (line 22); otherwise stop and return `finalChoice` (line 23).

Returns the current state (the state of the iteration in progress) and the next step. `fuel`
bounds the number of tests; `N` suffices, since each test removes at least one point.

**Formalization Note.** The `(j+1)`-th output of `x` in `h` is `(ptVals h x).getD j 0`;
the algorithm reads only outputs it has already observed. -/
noncomputable def susGo (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
    (h : List (ℕ × ℝ)) : ℕ → SUSState → SUSState × Step
  | fuel + 1, st =>
    if 3 ≤ st.M then
      match (List.range st.M).find?
          (fun j => decide ((ptVals h (st.x0 + j * st.s)).length < nLook N σ ε δ st.M)) with
      | some j => (st, Step.sample (st.x0 + j * st.s))
      | none => susGo N σ ε δ pick tie h fuel
          (lookStep N σ ε δ pick (fun x j => (ptVals h x).getD j 0) st)
    else
      match (List.range st.M).find? (fun j => decide ((ptVals h (st.x0 + j * st.s)).length <
          max (st.cnt (st.x0 + j * st.s)) (nFin N σ ε δ))) with
      | some j => (st, Step.sample (st.x0 + j * st.s))
      | none => (st, Step.stop (finalChoice N σ ε δ tie (fun x j => (ptVals h x).getD j 0) st))
  | 0, st =>
      match (List.range st.M).find? (fun j => decide ((ptVals h (st.x0 + j * st.s)).length <
          max (st.cnt (st.x0 + j * st.s)) (nFin N σ ε δ))) with
      | some j => (st, Step.sample (st.x0 + j * st.s))
      | none => (st, Step.stop (finalChoice N σ ε δ tie (fun x j => (ptVals h x).getD j 0) st))

end LocalDOvS.SUS


