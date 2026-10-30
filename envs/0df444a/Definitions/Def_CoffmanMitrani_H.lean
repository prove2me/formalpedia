-- Prove2me | Definitions.Def_CoffmanMitrani_H
-- name    : CoffmanMitrani_H
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:42.316983+00:00
-- url     : https://prove2.me/theorems/67df08dd-5141-45b1-bace-da56fa279ed0
-- title:
--   The set $H$ of definition (3)
-- statement:
--   A vector $W$ belongs to $H$ if there are $M$ preemptive priority disciplines (repetitions allowed) with performance vectors $P_1,\dots,P_M$, each achieved by a scheduling strategy following that discipline, and numbers $\alpha_1,\dots,\alpha_M \ge 0$ with $\alpha_1+\dots+\alpha_M = 1$, such that
--   $$W = \sum_{m=1}^M \alpha_m P_m. \qquad (3)$$
--
--   $H$ is the convex hull of the $M!$ performance vectors $P(1,2,\dots,M),\dots,P(M,M-1,\dots,1)$ of the preemptive priority disciplines.
--
--   **Formalization Note** The points $P_m$ are the performance vectors achieved by the priority strategies in the model, not a closed formula. The paper prints "$\alpha_1 + \dots + \alpha_m = 1$"; this is read as $\alpha_M$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 815, definition (3)

import Mathlib
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves

namespace CoffmanMitrani

/-- **The set `H`, definition (3).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 815: "Let H be the convex hull defined by these points; i.e. W ∈ H if and only if
there exist M points P1, P2, ···, PM from the set P(1, 2, ···, M), ···, P(M, M − 1, ···, 1) and M
numbers α1, α2, ···, αM satisfying αi ≥ 0 (i = 1, 2, ···, M) and α1 + α2 + ··· + αM = 1, such that
W = Σ_{i=1}^M αi Pi (3)".

`W ∈ H D` when there are `M` priority orders `π m` (repetitions allowed), vectors `Pv m` such that
`Pv m` is achieved by a scheduling strategy implementing the preemptive priority discipline `π m`,
and weights `α m ≥ 0` summing to `1`, with `W = Σ_m α m • Pv m`.

**Formalization Note.** The points are the performance vectors achieved by the priority strategies
in the model, not a closed-form formula. The printed "α1 + ··· + αm = 1" is read with `αM`. -/
def H (D : Data) : Set (Fin D.M → ℝ) :=
  {W | ∃ (π : Fin D.M → Equiv.Perm (Fin D.M)) (Pv : Fin D.M → Fin D.M → ℝ) (α : Fin D.M → ℝ),
    (∀ m, ∃ S : Schedule D.M, IsPriority D (π m) S ∧ IsStrategy D S ∧ Achieves D S (Pv m)) ∧
    (∀ m, 0 ≤ α m) ∧ ∑ m, α m = 1 ∧ W = ∑ m, α m • Pv m}

end CoffmanMitrani


