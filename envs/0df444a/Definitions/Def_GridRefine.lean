-- Prove2me | Definitions.Def_GridRefine
-- name    : GridRefine
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:16:04.524985+00:00
-- url     : https://prove2.me/theorems/06d09162-b914-4d6b-9acb-8cd074d3917e
-- title:
--   Grid-then-refine strategy: probes, opening phase, and the refinement loop
-- statement:
--   This module formalises strategy 5 of the portfolio in the space `GridSpace N = EuclideanSpace ℝ (Fin (2N+1))`, statement for statement against the frozen implementation. The probe list is the origin together with the $\pm 2 e_a$ points on the coordinate axes; `probeAt D i` gives the $i$-th probe — the origin at $i = 0$, $+2e_a$ at $i = 1 + 2a$ and $-2e_a$ at $i = 2 + 2a$. The opening length is $\mathrm{opening} = \min(2D+1,\; \max(1, \lfloor N/2 \rfloor))$ (source line 2565). The refinement loop moves the incumbent along coordinate `step mod D` by a signed, geometrically halved size: `refineAxis D s = s % D`, `refineSize D s = (1/2)^{s/D}` (since exactly $s/D$ halvings have happened before step $s$), `refineSign D s = +1` when $(s/D) \bmod 2 = 0$ and $-1$ otherwise, and `refineCandidate` shifts the incumbent by `sign * size` along that axis. `openQueries` and `openBest` run the opening phase with strict-improvement incumbent updates seeded at the origin, `refineLoop` iterates the proposal-and-update rule for a fixed number of steps, and `GridRefine.out` returns the final incumbent. All arithmetic is in $\mathbb N$ and $\mathbb R$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §30 source lines 2561-2626 (with the dimension (23.1)); Lean: FullFormalization.GridRefine lines 1-256

-- Generated from F:/20261008/FullFormalization\FullFormalization\GridRefine.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.GridRefine

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 30
  (source lines 2561-2626), strategy 5 of section 21 (source line 2083).

  The source states, in lines 2565-2585:

      opening = min (2D+1, max(1, floor(N/2)))
      the opening probes contain 0, the other probes are fixed-amplitude points
      on the positive and negative coordinate axes; within the N budget the
      coordinate indices involved are < N; the axes of the refinement steps are
      `step mod D`, and since N < D = 2N+1 no high-index coordinate is reached
      inside the budget.

  The complete semantics are those of the frozen implementation that section 19
  authorises and section 35's cross-check script imports
  (`F:\Hardy_Run_2026-10-07_001215\workflow\hgcore\blackbox_algos.py`,
  `probe_list` and `_grid_then_refine`):

      points = [(0,)*dimension]
      for axis in range(dimension):
          for sign in (2, -2):
              point = [0]*dimension; point[axis] = sign; points.append(point)

      opening = min(len(points), max(1, spec.query_budget // 2))
      for index in range(opening):
          point = points[index]; answer = oracle.query(point)
          if best_value is None or answer["value"] < best_value: best = point
      size = 1
      for step in range(spec.query_budget - opening):
          axis = step % dimension
          sign = 1 if (step // dimension) % 2 == 0 else -1
          candidate = list(best); candidate[axis] += sign * size
          answer = oracle.query(candidate)
          if answer["value"] < best_value: best = candidate
          if (step + 1) % dimension == 0: size = size / 2
      oracle.finish(best)

  `probeList`, `probeAt`, `opening`, `refineAxis`, `refineSize`, `refineSign`,
  `refineCandidate`, `openQueries`, `openBest`, `refineLoop` and `run` below are
  that program, statement for statement:

  * `probeList D` is `[0] ++ [+2 e_0, -2 e_0, +2 e_1, -2 e_1, ...]`, so its
    length is `2*D+1` (`probeList_length`), and the index-to-axis/sign rule is
    `probeAxis` / `probeSign` (`probeAt_odd`, `probeAt_even`);
  * `opening N D = min (2*D+1) (max 1 (N/2))` is line 2565 verbatim, with the
    budget written `N` (`opening`, `opening_eq`);
  * the opening best is seeded by the first probe, which is the origin
    (`one_le_opening`: the opening is never empty), exactly as the frozen
    `best_value = None` makes the first query the initial incumbent — and the
    first query is the origin, so the fold from `0` below is that same program;
  * `refineAxis D s = s % D` is line 2579 verbatim;
  * `refineSign D s` uses `(s / D) % 2`, and `refineSize D s = (1/2)^(s / D)`,
    because the number of halvings completed before step `s` is exactly
    `s / D` (source line 2581: `if (step+1) % D == 0: size /= 2`);
  * the query count is exactly the budget (`run_queries_length`).

  All arithmetic below is in `ℕ` and `ℝ`; the source's "grid" is the coordinate
  grid of `EuclideanSpace ℝ (Fin D)`, and section 23's dimension `D = 2N+1`
  enters as `gridDim N`.

  A note on notation: every scalar multiple of a vector is written with an
  explicitly typed scalar (`(2 : ℝ) • v`, not `2 • v`), because a bare numeral
  in a `•` is elaborated at `ℕ` and would silently mean `nsmul`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ### The dimension of Theorem B (source (23.1)) -/

/-- Source (23.1): `D = 2N+1`.  The strategies of section 21 run in
`EuclideanSpace ℝ (Fin D)`. -/
def gridDim (N : ℕ) : ℕ := 2 * N + 1





/-- The space the five strategies live in for Theorem B. -/
abbrev GridSpace (N : ℕ) : Type := EuclideanSpace ℝ (Fin (gridDim N))

/-! ### The coordinate unit vectors and the probes -/

/-- The `a`-th coordinate unit vector of `EuclideanSpace ℝ (Fin D)`. -/
noncomputable def axisVec (D : ℕ) (a : Fin D) : EuclideanSpace ℝ (Fin D) :=
  PiLp.single 2 a 1



/-- The same vector addressed by a natural number, guarded so that the
definition is total: only `a < D` can be nonzero. -/
noncomputable def axisVecOf (D : ℕ) (a : ℕ) : EuclideanSpace ℝ (Fin D) :=
  if h : a < D then axisVec D ⟨a, h⟩ else 0







/-- The axis of the `i`-th probe of `probeList D`: probe `0` is the origin, and
the probes `1 + 2a` and `2 + 2a` both sit on axis `a`. -/
def probeAxis (i : ℕ) : ℕ := (i - 1) / 2

/-- The sign of the `i`-th probe: `+2` at `1 + 2a`, `-2` at `2 + 2a`. -/
noncomputable def probeSign (i : ℕ) : ℝ := if (i - 1) % 2 = 0 then 2 else -2

/-- The `i`-th probe of the frozen `probe_list`: `0` at `i = 0`, then
`+2 e_a` at `1 + 2a` and `-2 e_a` at `2 + 2a`. -/
noncomputable def probeAt (D : ℕ) (i : ℕ) : EuclideanSpace ℝ (Fin D) :=
  if i = 0 then 0 else probeSign i • axisVecOf D (probeAxis i)























/-! ### The opening (source lines 2565-2572) -/

/-- Source lines 2565-2572: `opening = min(2D+1, max(1, floor(N/2)))`, where
`N` is the query budget and `D` the dimension.  The frozen implementation is
`min(len(probe_list(dimension)), max(1, query_budget // 2))`, and
`len(probe_list D) = 2*D+1` (`probeList_length`). -/
def opening (N D : ℕ) : ℕ := min (2 * D + 1) (max 1 (N / 2))

















/-! ### The refinement loop (source lines 2579-2585) -/

/-- Source line 2579: `axis = step mod D`. -/
def refineAxis (D : ℕ) (s : ℕ) : ℕ := s % D

/-- The `size` of the frozen loop at step `s`: it starts at `1` and is halved
after every `D`-th step, so exactly `s / D` halvings have happened before step
`s` (source line 2581: `if (step+1) % D == 0: size /= 2`). -/
noncomputable def refineSize (D : ℕ) (s : ℕ) : ℝ := (1 / 2 : ℝ) ^ (s / D)

/-- Source line 2580: `sign = +1 if (step // D) % 2 == 0 else -1`. -/
noncomputable def refineSign (D : ℕ) (s : ℕ) : ℝ := if (s / D) % 2 = 0 then 1 else -1

/-- Source lines 2579-2581: the step-`s` proposal is the incumbent moved by
`sign * size` along coordinate `step % D`. -/
noncomputable def refineCandidate (D : ℕ) (b : EuclideanSpace ℝ (Fin D)) (s : ℕ) :
    EuclideanSpace ℝ (Fin D) :=
  b + (refineSign D s * refineSize D s) • axisVecOf D (refineAxis D s)

















/-! ### The run -/

/-- The opening phase's queries: the first `opening` probes, in order. -/
noncomputable def openQueries (N : ℕ) : List (GridSpace N) :=
  (List.range (opening N (gridDim N))).map (probeAt (gridDim N))



/-- The incumbent after the opening phase.  The frozen loop's `best_value` is
`None` until the first query, and the first probe is the origin
(`one_le_opening`), so folding from `0` with the strict-improvement rule is
exactly that program. -/
noncomputable def openBest (N : ℕ) (o : Oracle (GridSpace N)) : GridSpace N :=
  (openQueries N).foldl (fun b q => if o.value q < o.value b then q else b) 0

/-- The refinement phase: `steps` iterations of the frozen loop, returning the
final incumbent and the list of the proposals it queried, in order. -/
noncomputable def refineLoop (N : ℕ) (o : Oracle (GridSpace N)) (b : GridSpace N) :
    ℕ → GridSpace N × List (GridSpace N)
  | 0 => (b, [])
  | s + 1 =>
      let p := refineLoop N o b s
      let c := refineCandidate (gridDim N) p.1 s
      (if o.value c < o.value p.1 then c else p.1, p.2 ++ [c])









namespace GridRefine

/-- Strategy 5's output: the final incumbent. -/
noncomputable def out (N : ℕ) (o : Oracle (GridSpace N)) : GridSpace N :=
  (refineLoop N o (openBest N o) (N - opening N (gridDim N))).1









end GridRefine

end FullFormalization


