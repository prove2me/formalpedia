-- Prove2me | Definitions.Def_ProjSchedTW_Temporal_TimeQuantities
-- name    : ProjSchedTW_Temporal_TimeQuantities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:33:07.981439+00:00
-- url     : https://prove2.me/theorems/f1f5db5e-0c36-48cb-b5ff-993e821bcf2e
-- title:
--   §1.3–1.4 — earliest and latest start times, total float, critical activities, base time intervals, and the distance order
-- statement:
--   Fix a project with network $N$ and an integer $L=LS_{n+1}$, and let $d_{ij}$ be the distances in the temporal scheduling network $N^+$ (with backward arc weight $-L$). Following §1.3 (pp. 12–13):
--
--   1. the **earliest start time** is $ES_i=d_{0i}$ and the **latest start time** is $LS_i=-d_{i0}$;
--   2. the **earliest completion time** is $EC_i=ES_i+p_i$;
--   3. the **total float** is $TF_i=LS_i-ES_i$; activity $i$ is **critical** if $TF_i=0$ and **near-critical** if $0<TF_i<p_i$;
--   4. the **base time interval** (Definition 1.3.7) of activity $i$ is the half-open interval of time points
--   $$[LS_i,EC_i[\;=\;\{t\in\mathbb R: LS_i\le t<EC_i\}.$$
--
--   The **distance order** $\prec_D$ (Definition 1.4.3) is the relation on $V$ given, for $i\ne j$, by
--   $$i\prec_D j\iff d_{ij}>0\ \text{ or }\ \bigl(d_{ij}=0\text{ and }d_{ji}<0\bigr).$$
--
--   These quantities are the output of temporal project scheduling (earliest and latest schedules, floats, critical activities) and the input of the priority-rule methods of later chapters (the distance order).
--
--   **Formalization Note.** $ES_i$ and $LS_i$ are integers obtained from the `WithBot ℤ` distances by replacing $-\infty$ with the junk value $0$. When $N^+$ has no cycle of positive length and the standing assumption holds, the relevant distances are finite (this is part of the milestone on the earliest and latest schedules), so the junk value is never used in the milestones; each milestone that uses $ES$ or $LS$ carries both hypotheses. The base time interval is a set of real numbers. The comparisons in $\prec_D$ are taken in `WithBot ℤ`, where $-\infty<0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, §1.3 pp. 11–15 (ES_i = d_0i, LS_i = −d_i0, EC_i, TF_i, critical and near-critical activities, Definition 1.3.7) and p. 17, Definition 1.4.3

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Project

namespace ProjSchedTW.Temporal

variable {n : ℕ}

/-- The earliest start time `ES_i := d_0i`, the longest path length from `0` to `i` in the
temporal scheduling network `N⁺` with `LS_{n+1} = L` (§1.3, pp. 12–13). The value `0` for
`d_0i = -∞` is a junk value, never reached when `N⁺` has no positive cycle and the standing
assumption holds. -/
noncomputable def Project.ES (P : Project n) (L : ℤ) (i : Fin (n + 2)) : ℤ :=
  (dist (P.N.plus L) 0 i).unbotD 0

/-- The latest start time `LS_i := -d_i0` in `N⁺` with `LS_{n+1} = L` (§1.3, pp. 12–13);
junk value `0` for `d_i0 = -∞`, as for `ES`. -/
noncomputable def Project.LS (P : Project n) (L : ℤ) (i : Fin (n + 2)) : ℤ :=
  -(dist (P.N.plus L) i 0).unbotD 0

/-- The earliest completion time `EC_i = ES_i + p_i` (§1.3, p. 14). -/
noncomputable def Project.EC (P : Project n) (L : ℤ) (i : Fin (n + 2)) : ℤ :=
  P.ES L i + P.p i

/-- The total float `TF_i = LS_i - ES_i` (§1.3, p. 15). -/
noncomputable def Project.TF (P : Project n) (L : ℤ) (i : Fin (n + 2)) : ℤ :=
  P.LS L i - P.ES L i

/-- Activity `i` is critical: `TF_i = 0` (§1.3, p. 15). -/
def Project.IsCritical (P : Project n) (L : ℤ) (i : Fin (n + 2)) : Prop :=
  P.TF L i = 0

/-- Activity `i` is near-critical: `0 < TF_i < p_i` (§1.3, p. 15). -/
def Project.IsNearCritical (P : Project n) (L : ℤ) (i : Fin (n + 2)) : Prop :=
  0 < P.TF L i ∧ P.TF L i < P.p i

/-- The base time interval `[LS_i, EC_i[` of activity `i` (Definition 1.3.7), a half-open
interval of real time points. -/
def Project.baseInterval (P : Project n) (L : ℤ) (i : Fin (n + 2)) : Set ℝ :=
  Set.Ico (P.LS L i : ℝ) (P.EC L i : ℝ)

/-- The distance order `≺_D` (Definition 1.4.3): for `i ≠ j`, `i ≺_D j` iff
`d_ij > 0`, or `d_ij = 0` and `d_ji < 0`, with `d` the distances in `N⁺`. -/
def Project.distOrder (P : Project n) (L : ℤ) (i j : Fin (n + 2)) : Prop :=
  i ≠ j ∧ (0 < dist (P.N.plus L) i j ∨
    (dist (P.N.plus L) i j = 0 ∧ dist (P.N.plus L) j i < 0))

end ProjSchedTW.Temporal


