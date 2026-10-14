-- Prove2me | Definitions.Def_PigeonholeDesign_Upper_Setting
-- name    : PigeonholeDesign_Upper_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:24.971547+00:00
-- url     : https://prove2.me/theorems/5175acb8-670d-41c5-9c05-14c5dc6694f9
-- title:
--   pp. 11, 13, 16 — discrepancy (display (1)), completely randomized design, pigeonhole design, uniform pigeonholes
-- statement:
--   This file sets up the sequential experimental design model of Zhao and Zhou with a single continuous covariate.
--
--   **Subjects and assignments.** A horizon $T$ (even) of subjects arrives one at a time; subject $t$ carries a covariate $x_t$ in a metric space $E$ (in this mission $E=\mathbb R$ with $x_t\in[0,1]$). An assignment is a vector $w\in\{0,1\}^T$: $w_t=0$ puts subject $t$ in the control group $A$, $w_t=1$ in the treated group $B$.
--
--   **Discrepancy** (display (1), p. 11). The discrepancy between $A$ and $B$ is the cost of a minimum-weight perfect matching between them,
--   $$d_{A,B}=\min_{y}\ \sum_{t\in A}\sum_{t'\in B} d(x_t,x_{t'})\,y_{t,t'}\quad\text{over perfect matchings } y \text{ of } A \text{ and } B .$$
--   Since (1) is an assignment problem, its optimum is the minimum, over all bijections $e:A\to B$, of $\sum_{a\in A} d(x_a,x_{e(a)})$. The restricted discrepancy $d_{A\cap S,B\cap S}$ is the same quantity for the subjects of a set $S$ only.
--
--   **Completely randomized design** (Definition 2, p. 13). It chooses the control set $V$ uniformly among the $\binom{T}{T/2}$ subsets of size $T/2$; its expected discrepancy is
--   $$\mathrm{ALG}^{\mathsf C}(x)=\binom{T}{T/2}^{-1}\sum_{|V|=T/2} d_{V,[T]\setminus V}.$$
--
--   **Pigeonhole design** (Definition 3, p. 16). The covariate space is partitioned into pigeonholes $S_k$ (here: the fibres of a labelling map). Upon arrival of subject $t$: (1) if the control or the treated group already holds $T/2$ subjects, $t$ goes to the other group; (2) otherwise, with $n^0_{k,t-1},n^1_{k,t-1}$ the numbers of control and treated subjects already in the pigeonhole $k$ of $x_t$, $t$ goes to control if $n^0_{k,t-1}<n^1_{k,t-1}$, to treatment if $n^0_{k,t-1}>n^1_{k,t-1}$, and to either with probability $1/2$ in case of a tie. The expected discrepancy of the design is the average of $d_{A,B}$ over all $2^T$ equally likely coin vectors, where coin $t$ is consulted only when subject $t$ meets a tie; this gives each tie an independent fair coin, exactly the paper's law.
--
--   **Uniform pigeonholes** (Lemma 3, p. 18). For $K\ge1$, the uniform partition of $[0,1]$ into $K$ cells $[k/K,(k+1)/K)$, $k=0,\dots,K-2$, and the closed last cell $[(K-1)/K,1]$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Subjects are indexed from $0$ (`Fin T`), so the paper's subject $t$ is index $t-1$; `true` means treated. The discrepancy is an infimum over bijections between the two groups: when the groups differ in size there is no bijection and Lean returns the junk value $0$. Both designs are always balanced ($T/2$ subjects in each group; see the balance milestone), so this value is never reached on their runs. The pigeonhole design is computed by recursion on the prefix of assigned subjects, with Step 1 checked before the pigeonhole rule, exactly in the order of Definition 3. The paper's $T^{\eta}$ cells (not an integer in general) are pinned as $K=\lceil T^{\eta}\rceil$ cells of length $1/K\le T^{-\eta}$ by the theorems that use `uniformHole`.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. 10-11 display (1), p. 13 Definition 2, p. 16 Definition 3, p. 18 Lemma 3 (partition), p. ec4 (ALG^C)

import Mathlib

namespace PigeonholeDesign.Upper

/-- Display (1), p. 11: the discrepancy `d_{A,B}` between the control group `A = {t | w t = false}`
and the treated group `B = {t | w t = true}`, the minimum-weight perfect matching between them.
Program (1) is an assignment problem, so its optimum is the minimum over bijections `A ≃ B`.
If `|A| ≠ |B|` there is no bijection and the infimum is the junk value `0`; every design of the
paper is balanced, so this value is never reached by the designs. -/
noncomputable def discrepancy {E : Type*} [PseudoMetricSpace E] {T : ℕ}
    (x : Fin T → E) (w : Fin T → Bool) : ℝ :=
  ⨅ e : {t // w t = false} ≃ {t // w t = true},
    ∑ a : {t // w t = false}, dist (x a) (x (e a))

/-- `d_{A∩S, B∩S}`: the minimum-weight perfect matching between the control and the treated
subjects of `S` (junk value `0` if they differ in number). -/
noncomputable def discrepancyOn {E : Type*} [PseudoMetricSpace E] {T : ℕ}
    (x : Fin T → E) (w : Fin T → Bool) (S : Finset (Fin T)) : ℝ :=
  ⨅ e : {t // t ∈ S ∧ w t = false} ≃ {t // t ∈ S ∧ w t = true},
    ∑ a : {t // t ∈ S ∧ w t = false}, dist (x a) (x (e a))

/-- Definition 2, p. 13, and `ALG^C(x)`, p. ec4: the expected discrepancy of the completely
randomized design, the uniform average over the control sets `V` of size `T/2`. -/
noncomputable def crdExp {E : Type*} [PseudoMetricSpace E] {T : ℕ} (x : Fin T → E) : ℝ :=
  (∑ V ∈ (Finset.univ : Finset (Fin T)).powersetCard (T / 2),
      discrepancy x (fun t => decide (t ∉ V))) / (T.choose (T / 2) : ℝ)

/-- Definition 3, p. 16: the assignments of subjects `0, …, n−1` of the pigeonhole design (a list of
length `n`, `true` = treated). `cell s` is the pigeonhole of subject `s`, `coin s` its fair coin. -/
def prefixAssign {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) :
    ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let L := prefixAssign T cell coin n
    let a0 := ((List.range n).zip L).countP (fun sb => cell sb.1 = cell n ∧ sb.2 = false)
    let a1 := ((List.range n).zip L).countP (fun sb => cell sb.1 = cell n ∧ sb.2 = true)
    L ++ [if L.count false = T / 2 then true          -- Step 1: control full → treated
          else if L.count true = T / 2 then false     -- Step 1: treated full → control
          else if a0 < a1 then false                  -- Step 2: fewer control here → control
          else if a1 < a0 then true                   -- Step 2: fewer treated here → treated
          else coin n]                                -- Step 2: tie → fair coin

/-- The pigeonhole of subject `n` (`none` past the horizon). -/
def cellOf {E ι : Type*} {T : ℕ} (hole : E → ι) (x : Fin T → E) (n : ℕ) : Option ι :=
  if h : n < T then some (hole (x ⟨n, h⟩)) else none

/-- The coin of subject `n` (`false` past the horizon, never used). -/
def coinOf {T : ℕ} (coin : Fin T → Bool) (n : ℕ) : Bool :=
  if h : n < T then coin ⟨n, h⟩ else false

/-- The assignment produced by the pigeonhole design with partition `hole` (pigeonhole `k` is the
fibre of `hole` over `k`) on arrivals `x` with coin vector `coin`. -/
def assign {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : Fin T → Bool :=
  fun t => (prefixAssign T (cellOf hole x) (coinOf coin) T).getD t false

/-- The expected discrepancy of the pigeonhole design: the average over all `2^T` coin vectors. -/
noncomputable def phdExp {E ι : Type*} [PseudoMetricSpace E] [DecidableEq ι] {T : ℕ}
    (hole : E → ι) (x : Fin T → E) : ℝ :=
  (∑ coin : Fin T → Bool, discrepancy x (assign hole x coin)) / 2 ^ T

/-- Lemma 3's uniform pigeonholes on `[0,1]`: `K` cells `[k/K, (k+1)/K)`, the last one closed.
With `K = ⌈T^η⌉` every cell has length `1/K ≤ T^{-η}`. -/
noncomputable def uniformHole (K : ℕ) (z : ℝ) : ℕ := min ⌊z * K⌋₊ (K - 1)

end PigeonholeDesign.Upper


