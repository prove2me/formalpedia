-- Prove2me | Definitions.Def_ProjSchedTW_DelayingModes_Distance
-- name    : ProjSchedTW_DelayingModes_Distance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T22:40:50.122493+00:00
-- url     : https://prove2.me/theorems/705887ef-ac7a-45f2-bb9b-de52e41c2a14
-- title:
--   §1.3 and §2.5.2 — longest path lengths $d_{ij}$ in the network $N^+$ with $\delta_{n+1,0}=-UB$
-- statement:
--   This file defines the distances $d_{ij}$ used by the preprocessing of §2.5.2.
--
--   For a directed network on $V$ with arc set $A$ and integer arc weights $w$, the length of a path $v_0,v_1,\dots,v_m$ is $\sum_{l=0}^{m-1}w_{v_lv_{l+1}}$. The *longest path length* from $i$ to $j$ is the maximum length of a simple path from $i$ to $j$ using arcs of $A$, and $-\infty$ if there is no such path; the one-node path gives $d_{ii}\ge 0$. When the network has no cycle of positive length, this is the distance $d_{ij}$ of §1.3 (p. 11), with $d_{ii}=0$.
--
--   Given an upper bound $UB\in\mathbb Z$ on the project duration, the *temporal scheduling network* $N^+$ is obtained from the project network $N$ by adding the backward arc $\langle n+1,0\rangle$ with weight
--   $$\delta_{n+1,0}=-UB,$$
--   which encodes the maximum time lag $d^{\max}_{0,n+1}=UB$ (p. 54). If $N$ already contains an arc $\langle n+1,0\rangle$, both maximum time lags apply and the arc receives the weight $\max(\delta_{n+1,0},-UB)$. The distance $d_{ij}$ of §2.5.2 is the longest path length from $i$ to $j$ in $N^+$.
--
--   Every feasible schedule with $S_{n+1}\le UB$ satisfies $S_j-S_i\ge d_{ij}$; this is what makes the distances usable for preprocessing.
--
--   **Formalization Note.** Distances take values in `WithBot ℝ`, with `⊥` playing the role of $-\infty$; the arc weights are integers cast to reals. The maximum is over simple paths (a finite set). If $N^+$ contained a cycle of positive length, this maximum would not be the book's distance, but then no schedule satisfies the temporal constraints together with $S_{n+1}\le UB$, so the statements that use $d_{ij}$ are vacuous in that case, as in the book, which assumes throughout that no such cycle exists.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 11 (distances d_ij in N+, Eq. (1.3.3)), p. 54 (arc <n+1,0> with weight -UB)

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

namespace ProjSchedTW.DelayingModes

/-- The longest path length from `i` to `j` in the network with arc set `A` and integer arc
weights `w`: the maximum of the lengths of the simple paths from `i` to `j`, as a value in
`WithBot ℝ`, where `⊥` stands for `-∞` (no path from `i` to `j`). The one-node path gives
`0` for `i = j`. When the network contains no cycle of positive length, this is the longest
path length (distance) `d_ij` of §1.3, p. 11. -/
noncomputable def longestPathLength {n : ℕ} (A : Finset (Fin (n + 2) × Fin (n + 2)))
    (w : Fin (n + 2) → Fin (n + 2) → ℤ) (i j : Fin (n + 2)) : WithBot ℝ :=
  open Classical in
  (Finset.univ.filter (fun Q : SimplePath n => Q.IsFromTo A i j)).sup
    (fun Q => (((Q.length w : ℤ) : ℝ) : WithBot ℝ))

/-- The arc set `E⁺` of the temporal scheduling network `N⁺` (§1.3, p. 11; §2.5.2, p. 54): the
arcs of `E` together with the backward arc `⟨n+1, 0⟩`. -/
def Project.plusArcs {n : ℕ} {K : Type} [Fintype K] (P : Project n K) :
    Finset (Fin (n + 2) × Fin (n + 2)) :=
  insert (Fin.last (n + 1), 0) P.E

/-- The arc weights of `N⁺` for the upper bound `UB` on the project duration (§2.5.2, p. 54):
the backward arc `⟨n+1, 0⟩` carries the weight `δ_{n+1,0} = -UB` (the maximum time lag
`d^max_{0,n+1} = UB`); if the project network already has an arc `⟨n+1, 0⟩`, the two maximum
time lags are combined into the weight `max(δ_{n+1,0}, -UB)`. All other weights are those of
`N`. -/
def Project.plusWeight {n : ℕ} {K : Type} [Fintype K] (P : Project n K) (UB : ℤ) :
    Fin (n + 2) → Fin (n + 2) → ℤ :=
  fun i j =>
    if i = Fin.last (n + 1) ∧ j = 0 then
      (if (Fin.last (n + 1), (0 : Fin (n + 2))) ∈ P.E then max (P.δ (Fin.last (n + 1)) 0) (-UB)
        else -UB)
    else P.δ i j

/-- The distance `d_ij` in the temporal scheduling network `N⁺` with `δ_{n+1,0} = -UB`
(§2.5.2, p. 54): the longest path length from `i` to `j` in `N⁺`, `-∞` (`⊥`) if there is no
path. -/
noncomputable def Project.distPlus {n : ℕ} {K : Type} [Fintype K] (P : Project n K) (UB : ℤ)
    (i j : Fin (n + 2)) : WithBot ℝ :=
  longestPathLength P.plusArcs (P.plusWeight UB) i j

end ProjSchedTW.DelayingModes


