-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsMonotoneProfile
-- name    : FlowAllocationGames_UnitRanking_IsMonotoneProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:13.956884+00:00
-- url     : https://prove2.me/theorems/a3349fd1-fd62-4559-88a3-a02b8f90f511
-- title:
--   Profile of monotone strategies
-- statement:
--   A strategy profile $a$ consists of **monotone strategies** when, for every edge $e$, every node $v$ and all integers $y \ge y' \ge 0$:
--
--   1. (capacity constraint) $0 \le a_e(y) \le c_e$;
--   2. (weak flow conservation constraint) $\sum_{e\in E^+(v)} a_e(y) \le y$;
--   3. (monotonicity constraint) $a_e(y) \ge a_e(y')$.
--
--   These are the constraints (1), (2) and (5) of the paper. For monotone strategies feasible flows exist and form a complete lattice (Theorem 2).
--
--   **Formalization Note** Supplies range over the natural numbers, as in the integral model of unit-ranking games. The no-fraud constraint (3) is not part of this notion.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, pp. 10–11, constraints (1), (2), (5)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile

namespace FlowAllocationGames.UnitRanking

/-- **Profile of monotone strategies.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, pp. 10–11:
constraints (1) `0 ≤ ae(y) ≤ ce` (capacity) and (2) `Σ_{e∈E⁺(v)} ae(y) ≤ y` (weak flow
conservation), and p. 11: "Monotone strategies are characterized by capacity and weak-flow
conservation constraints, and, for every y, y′ ∈ ℝ≥0 with y ≥ y′, ae(y) ≥ ae(y′)" (5).

`IsMonotoneProfile Γ a` holds when (1), (2) and (5) hold for every edge, node and supply value.

**Formalization Note.** Supplies range over `ℕ` (the integral model of §2.2, p. 13); the lower
bound `0 ≤ ae(y)` of (1) is automatic in `ℕ`. The no-fraud constraint (3) is not part of this
predicate, as in p. 11's definition of monotone strategies. -/
def IsMonotoneProfile {n m : ℕ} (Γ : Game n m) (a : Profile m) : Prop :=
  (∀ e y, a e y ≤ Γ.c e) ∧
  (∀ v y, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), a e y ≤ y) ∧
  ∀ e, Monotone (a e)

end FlowAllocationGames.UnitRanking


