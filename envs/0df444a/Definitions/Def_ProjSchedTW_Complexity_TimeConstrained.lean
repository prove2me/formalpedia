-- Prove2me | Definitions.Def_ProjSchedTW_Complexity_TimeConstrained
-- name    : ProjSchedTW_Complexity_TimeConstrained
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:53:04.427455+00:00
-- url     : https://prove2.me/theorems/87af4fd3-1ead-4a62-bef1-7f758e8d35d0
-- title:
--   The decision version of PS∞|temp,d̄| −ΣΣ w_ij|S_j − S_i|, and the SIMPLE MAX CUT instance
-- statement:
--   This file defines the time-constrained project scheduling problem with the weighted start-time deviation objective (§3.1 of Neumann, Schwindt and Zimmermann) as a decision problem, and the instance built in the proof of Proposition 3.4.2.
--
--   **Instances.** Activities $V=\{0,1,\dots,n+1\}$ with durations $p_i\in\mathbb N$, a project network with arcs $E$ and integer weights $\delta_{ij}$, a maximum project duration $\bar d\in\mathbb N$, weights $w_{ij}\in\mathbb N$ ($w_{ij}\ge0$, p. 200) and a threshold $M\in\mathbb N$. It is well formed if $n\ge1$, $p_0=p_{n+1}=0$, $p_i>0$ for the real activities, and the network has no loops.
--
--   **Time-feasible schedules** of $PS\infty|temp,\bar d|f$: real $S$ with $S_0=0$, $S_i\ge0$, $S_j-S_i\ge\delta_{ij}$ for $\langle i,j\rangle\in E$, and $S_{n+1}\le\bar d$ (Eq. (3.1.1)). The objective is $f(S)=-\sum_{i\in V}\sum_{j\in V:\,j>i}w_{ij}|S_j-S_i|$.
--
--   **Decision problem.** A yes-instance has a time-feasible $S$ with $f(S)\le-M$, i.e.
--   $$\sum_{i\in V}\sum_{j\in V:\,j>i} w_{ij}\,|S_j-S_i|\ \ge\ M.$$
--   Instances are coded in binary as $n$, the durations, the arc indicators and weights $\delta_{ij}$ for all ordered pairs, $\bar d$, the $w_{ij}$, and $M$.
--
--   **The SIMPLE MAX CUT instance** (proof of Proposition 3.4.2). From a graph $G$ on $V^G=\{1,\dots,\nu\}$ and $M$: $n=\nu$, $p_i=1$ for $i\in V^G$, arcs $\langle0,i\rangle$ with $d^{\min}_{0i}=0$ and $\langle i,n+1\rangle$ with $d^{\min}_{i,n+1}=1$, $\bar d=2$, and $w_{ij}=1$ if $i$ and $j$ are adjacent in $G$, $w_{ij}=0$ otherwise.
--
--   **Formalization Note** Activities are `Fin (n + 2)`; node $l$ of $G$ (`Fin ν`) is activity $l+1$. The deadline $S_{n+1}\le\bar d$ is imposed directly instead of through the backward arc $\langle n+1,0\rangle$ of weight $-\bar d$. Weights and thresholds are natural numbers so that instances have finite codes. The book's standing requirement $\bar d\ge ES_{n+1}$ (a time-feasible schedule exists) is not added to well-formedness: it holds for every yes-instance, so it does not change the language.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 197–198 (§3.1, Eq. (3.1.1), problem (3.1.2), PS∞|temp,d̄|f), p. 200 (objective −ΣΣ w_ij|S_j − S_i|, w_ij ≥ 0), p. 241 (the instance of the proof of Proposition 3.4.2)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace ProjSchedTW.Complexity

open CookPvsNP

/-- An instance of the decision version of `PS∞|temp,d̄| −∑∑ w_ij|S_j − S_i|`, the
time-constrained project scheduling problem with the weighted start-time deviation objective
(§3.1, pp. 197–200). Activities are `V = Fin (n + 2)` (`0` the project beginning,
`Fin.last (n + 1)` the project completion).
* `p i ∈ ℕ` is the duration of activity `i`; `E` the arc set and `δ i j ∈ ℤ` the arc weights;
* `dbar ∈ ℕ` is the maximum project duration `d̄` (Eq. (3.1.1));
* `w i j ∈ ℕ` is the weight `w_ij ≥ 0` of the pair `i < j` (p. 200);
* `M ∈ ℕ` is the threshold of the decision question
  "is there a time-feasible `S` with `∑_{i<j} w_ij |S_j − S_i| ≥ M`?", i.e. `f(S) ≤ −M`. -/
structure TCInstance where
  n : ℕ
  p : Fin (n + 2) → ℕ
  E : Finset (Fin (n + 2) × Fin (n + 2))
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  dbar : ℕ
  w : Fin (n + 2) → Fin (n + 2) → ℕ
  M : ℕ

namespace TCInstance

/-- The standing assumptions (§1.1, §1.2 and p. 32): `n ≥ 1`; the fictitious activities `0`
and `n+1` have duration `0` and every real activity a positive duration; no loops. -/
def WellFormed (x : TCInstance) : Prop :=
  1 ≤ x.n ∧ x.p 0 = 0 ∧ x.p (Fin.last (x.n + 1)) = 0 ∧
    (∀ i : Fin (x.n + 2), i ≠ 0 → i ≠ Fin.last (x.n + 1) → 0 < x.p i) ∧ (∀ e ∈ x.E, e.1 ≠ e.2)

/-- A time-feasible schedule of `PS∞|temp,d̄|f` (§3.1, problem (3.1.2) without resource
constraints): `S_0 = 0`, `S_i ≥ 0`, `S_j − S_i ≥ δ_ij` for every arc, and `S_{n+1} ≤ d̄`. -/
def TimeFeasible (x : TCInstance) (S : Fin (x.n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ (∀ e ∈ x.E, (x.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1) ∧
    S (Fin.last (x.n + 1)) ≤ x.dbar

/-- The weighted start-time deviation `∑_{i ∈ V} ∑_{j ∈ V, j > i} w_ij |S_j − S_i|`
(p. 200); the objective function of the problem is its negative. -/
noncomputable def deviation (x : TCInstance) (S : Fin (x.n + 2) → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (x.w i j : ℝ) * |S j - S i|

/-- The yes-instances: some time-feasible schedule `S` has `f(S) = −∑∑ w_ij |S_j − S_i| ≤ −M`. -/
def Yes (x : TCInstance) : Prop :=
  ∃ S, x.TimeFeasible S ∧ (x.M : ℝ) ≤ x.deviation S

/-- The numbers describing an instance, in order: `n`; the durations; for every ordered pair
`(i, j)` (row by row) the arc indicator and the weight `δ_ij`; `d̄`; the weights `w_ij` (row by
row); `M`. -/
def code (x : TCInstance) : List ℤ :=
  [(x.n : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++
    (List.ofFn fun i => List.ofFn fun j =>
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j]).flatten.flatten ++
    [(x.dbar : ℤ)] ++ (List.ofFn fun i => List.ofFn fun j => (x.w i j : ℤ)).flatten ++
    [(x.M : ℤ)]

end TCInstance

/-- The decision language of `PS∞|temp,d̄| −∑∑ w_ij|S_j − S_i|`: binary codes of the
well-formed yes-instances. -/
def deviationLang : Lang BSym :=
  { w | ∃ x : TCInstance, x.WellFormed ∧ x.Yes ∧ w = encInts x.code }

open Classical in
/-- The instance of the proof of Proposition 3.4.2 (p. 241) built from a graph `G` on the
nodes `V^G = Fin ν` (node `l` is activity `l + 1`) and a number `M`: `p_i = 1` for `i ∈ V^G`,
arcs `⟨0, i⟩` with `d_{0i}^min = 0` and `⟨i, n+1⟩` with `d_{i,n+1}^min = 1` (`i ∈ V^G`),
`d̄ = 2`, and `w_ij = 1` if `i, j ∈ V^G` are adjacent in `G`, `w_ij = 0` otherwise. -/
noncomputable def maxCutProject {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : TCInstance where
  n := ν
  p := fun i => if i = 0 ∨ i = Fin.last (ν + 1) then 0 else 1
  E := Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
    (e.1 = 0 ∧ e.2 ≠ 0 ∧ e.2 ≠ Fin.last (ν + 1)) ∨
      (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1))
  δ := fun i j => if i ≠ 0 ∧ j = Fin.last (ν + 1) then 1 else 0
  dbar := 2
  w := fun i j =>
    if h : 0 < i.val ∧ i.val < ν + 1 ∧ 0 < j.val ∧ j.val < ν + 1 then
      (if G.Adj ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ then 1 else 0)
    else 0
  M := M

end ProjSchedTW.Complexity


