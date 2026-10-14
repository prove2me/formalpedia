-- Prove2me | Definitions.Def_PigeonholeDesign_Lower_Setting
-- name    : PigeonholeDesign_Lower_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:39.473158+00:00
-- url     : https://prove2.me/theorems/b6b4b13e-1fb3-4c5c-912f-87a124158d35
-- title:
--   pp. 11, 16, ec15 — discrepancy (display (1)), pigeonhole design, interval partitions of [0,1], the alternating instance
-- statement:
--   This file sets up the sequential experimental design model of Zhao and Zhou with a single continuous covariate, together with the interval partitions and the arrival instance used in the proof of their Lemma 4.
--
--   **Subjects and assignments.** A horizon of $T$ subjects (with $T$ even) arrives one at a time; subject $t$ carries a covariate $x_t$ in a metric space $E$ (in this mission $E=\mathbb R$ with $x_t\in[0,1]$). An assignment is a vector $w\in\{0,1\}^T$: $w_t=0$ puts subject $t$ in the control group $A$, and $w_t=1$ puts it in the treated group $B$.
--
--   **Discrepancy** (display (1), p. 11). The discrepancy between $A$ and $B$ is the cost of a minimum-weight perfect matching between them:
--   $$d_{A,B}=\min_{y}\ \sum_{t\in A}\sum_{t'\in B} |x_t-x_{t'}|\,y_{t,t'}\quad\text{over perfect matchings } y \text{ of } A \text{ and } B .$$
--   Program (1) is an assignment problem, so its optimum is the minimum, over all bijections $e:A\to B$, of $\sum_{a\in A} |x_a-x_{e(a)}|$.
--
--   **Pigeonhole design** (Definition 3, p. 16). The covariate space is partitioned into pigeonholes $S_k$, here given as the fibres of a labelling map. When subject $t$ arrives:
--
--   1. if the control or the treated group already holds $T/2$ subjects, $t$ goes to the other group;
--   2. otherwise, let $n^0_{k,t-1}$ and $n^1_{k,t-1}$ be the numbers of control and treated subjects already in the pigeonhole $k$ of $x_t$. Subject $t$ goes to control if $n^0_{k,t-1}<n^1_{k,t-1}$, to treatment if $n^0_{k,t-1}>n^1_{k,t-1}$, and to either group with probability $1/2$ in case of a tie.
--
--   The **expected discrepancy** of the design on the arrival sequence $x$ is the average of $d_{A,B}$ over all $2^T$ equally likely coin vectors, where coin $t$ is consulted only when subject $t$ meets a tie. This gives each tie an independent fair coin, which is exactly the law of the paper's design.
--
--   **Interval partitions** (proof of Lemma 4, p. ec15). Breakpoints $0=l_0<l_1<\dots<l_K=1$ define the partition $\{[l_0,l_1),[l_1,l_2),\dots,[l_{K-1},l_K]\}$ of $[0,1]$ into $K$ intervals, the last one closed. The cell lengths are $L_k=l_k-l_{k-1}$.
--
--   **The alternating instance** (p. ec15). Given even counts $n_1,\dots,n_K$ and $\epsilon>0$, the instance lists, cell after cell, $n_k/2$ consecutive pairs $(l_{k-1},\,l_k-\epsilon)$; in the last cell the pairs are $(l_{K-1},\,l_K)$. Its length is $\sum_k n_k$, and cell $k$ receives exactly $n_k$ subjects when $\epsilon<L_k$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** The discrepancy $d_{A,B}$, the recursion of the pigeonhole design and its expected discrepancy are imported from the definition `PigeonholeDesign.Upper.Setting` (the same objects, shared by all missions of this paper); the run of the design is exposed here as `assign`, a reducible alias of `PigeonholeDesign.Upper.assign`. This file itself adds the breakpoints, the interval labelling, the cell lengths and the alternating instance. Subjects and cells are indexed from $0$ (`Fin T`, `Fin K`), so the paper's subject $t$ is index $t-1$ and the paper's cell $k\in[K]$ is $[l_{k-1},l_k)$ at index $k-1$; `true` means treated. The discrepancy is an infimum over bijections between the two groups. When the groups differ in size there is no bijection and Lean returns the junk value $0$; the pigeonhole design always ends with $T/2$ subjects in each group, so this value is never reached on its runs (and a junk $0$ could only make a lower bound harder). The design is computed by recursion on the prefix of assigned subjects, with Step 1 checked before the pigeonhole rule, in the order of Definition 3. The partition is the labelling $z\mapsto\#\{i: 0<i<K,\ l_i\le z\}$, which sends $[l_k,l_{k+1})$ to $k$ and $1$ to $K-1$. The alternating instance is read at positions $0,\dots,T-1$ with value $0$ past its end; it is used only with $T=\sum_k n_k$ and all $n_k$ even, where no position is past the end.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. 10-11 display (1), p. 16 Definition 3, p. ec15 (proof of Lemma 4: partition and arrival instance)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Lower

/-- The pigeonhole design run on the arrival sequence `x` with partition `hole` (pigeonhole `k` is
the fibre `hole ⁻¹' {k}`) and coin vector `coin`: `assign hole x coin t = true` iff subject `t` is
treated. This is the same object as `PigeonholeDesign.Upper.assign` (whose expected discrepancy is
`PigeonholeDesign.Upper.phdExp`), kept under this name as a reducible alias. -/
abbrev assign {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : Fin T → Bool :=
  PigeonholeDesign.Upper.assign hole x coin

/-- The alias agrees with `PigeonholeDesign.Upper.assign` by definition. -/
theorem assign_eq_upper {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : assign hole x coin = PigeonholeDesign.Upper.assign hole x coin := rfl

/-- Breakpoints `0 = l₀ < l₁ < … < l_K = 1` of a partition of `[0,1]` into `K` intervals. -/
structure Breakpoints (K : ℕ) where
  l : Fin (K + 1) → ℝ
  strictMono : StrictMono l
  zero : l 0 = 0
  last : l (Fin.last K) = 1

/-- The interval partition `{[l₀,l₁), [l₁,l₂), …, [l_{K−1}, l_K]}` as a labelling: `z ↦ k` for
`z ∈ [l_k, l_{k+1})` (`k = 0, …, K−1`, 0-based), with the last cell closed, so `1 ↦ K − 1`. -/
noncomputable def intervalHole {K : ℕ} (b : Breakpoints K) (z : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin (K + 1))).filter
    (fun i : Fin (K + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < K ∧ b.l i ≤ z)).card

/-- Cell lengths `L_k = l_{k+1} − l_k` (0-based `k`). -/
def len {K : ℕ} (b : Breakpoints K) (k : Fin K) : ℝ := b.l k.succ - b.l k.castSucc

/-- The right point of the alternating pairs in cell `k`: `l_{k+1} − ε`, except in the last
(closed) cell, where it is `l_K = 1`. -/
def rightPt {K : ℕ} (b : Breakpoints K) (ε : ℝ) (k : Fin K) : ℝ :=
  if (k : ℕ) + 1 = K then b.l k.succ else b.l k.succ - ε

/-- The alternating instance of the proof of Lemma 4 (p. ec15): cell `k = 0, …, K−1` in turn
contributes `n k / 2` consecutive pairs `(l_k, rightPt k)`. The sequence is read at positions
`0, …, T−1` (value `0` past its end); it has length exactly `T` when every `n k` is even and
`∑ k, n k = T`. -/
noncomputable def altInstance {K : ℕ} (b : Breakpoints K) (n : Fin K → ℕ) (ε : ℝ) (T : ℕ) :
    Fin T → ℝ :=
  fun t => ((List.ofFn fun k : Fin K =>
    (List.replicate (n k / 2) [b.l k.castSucc, rightPt b ε k]).flatten).flatten).getD t 0

end PigeonholeDesign.Lower


