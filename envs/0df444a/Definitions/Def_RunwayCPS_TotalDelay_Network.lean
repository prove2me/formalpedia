-- Prove2me | Definitions.Def_RunwayCPS_TotalDelay_Network
-- name    : RunwayCPS_TotalDelay_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:03.543247+00:00
-- url     : https://prove2.me/theorems/c4b0d098-d56e-4291-923e-723a0498ede8
-- title:
--   §2, §3, §3.1, §5.2: runway instance without time windows, k-CPS feasible schedules, the CPS network with precedence pruning, path lengths and θ
-- statement:
--   This file fixes the model of §5.2 of Balakrishnan and Chandran: single-runway scheduling under constrained position shifting, with separations and precedence constraints but **no time windows**, together with the CPS network on which the problem is solved.
--
--   **Instance.** There are $n$ aircraft, labelled $1,\dots,n$ by their position in the first-come-first-served (FCFS) sequence; a maximum position shift $k\in\mathbb N$; minimum separations $\delta_{ab}\in\mathbb R$, the minimum time required between leading aircraft $a$ and trailing aircraft $b$; and a finite set of precedence pairs $(x,y)$, meaning that $x$ must land before $y$.
--
--   **Feasible schedules.** A **$k$-CPS sequence** is a permutation $\sigma$ (position $\mapsto$ aircraft) with $|\sigma(p)-p|\le k$ for every position $p$. A feasible schedule is a $k$-CPS sequence $\sigma$ in which every precedence pair $(x,y)$ has $\sigma^{-1}(x)<\sigma^{-1}(y)$, together with landing times $t_1,\dots,t_n$ (by position) such that
--   $$t_p\ge 0\quad\text{for all }p,\qquad t_q-t_p\ge\delta_{\sigma(p)\sigma(q)}\quad\text{for all positions }p<q .$$
--   Delay is measured from time $0$, at which all aircraft are available. The **total delay** of the schedule is $t_1+\dots+t_n$.
--
--   **CPS network.** The network has stages $1,\dots,n$. A node in stage $p$ is a sequence of pairwise distinct aircraft of length $L=\min\{2k+1,p\}$ occupying positions $p-L+1,\dots,p$, each aircraft within $k$ of the position it occupies. Its last aircraft is the node's **final aircraft**. An arc joins a stage-$p$ node $i$ to a stage-$(p+1)$ node $j$ when the first $\min\{2k,p\}$ aircraft of $j$ are the last $\min\{2k,p\}$ aircraft of $i$. A source-sink path chooses one node per stage, joined by arcs. Its sequence places at position $p$ the final aircraft of its stage-$p$ node. A path from the source to a node $j$ in stage $p$ is the same for stages $1,\dots,p$, ending at $j$.
--
--   **Precedence pruning.** A node violates the pair $(x,y)$ if $y$ appears in it before $x$, or $y$ occupies a position less than $x-k$, or $x$ occupies a position greater than $y+k$. The last two conditions are the position-constrained network of Case II ($x>y$). The **pruned network** $G$ keeps the nodes that violate no pair, with the same arcs.
--
--   **Path length and θ.** For nodes $i,j$ let $\delta_i(j)$ be the separation between the final aircraft of $i$ (leading) and of $j$ (trailing). The arc $(i,j)$ from stage $p-1$ to stage $p$ has distance $(n-p+1)\delta_i(j)$, and source and sink arcs have distance $0$. The length of a source-sink path $v_1,\dots,v_n$ is therefore
--   $$\operatorname{len}(v)=\sum_{p=2}^{n}(n-p+1)\,\delta_{v_{p-1}}(v_p).$$
--   For a node $j$ of $G$ in stage $p$, a **partial schedule ending at $j$** is a path $v_1,\dots,v_p=j$ in $G$ together with times $t_1,\dots,t_p\ge0$ for the final aircraft of its nodes, with $t_r-t_q\ge\delta_{v_q}(v_r)$ for all $q<r\le p$. The set $\Theta_j(p)$ collects the values
--   $$\theta_j(p)=t_1+t_2+\dots+t_{p-1}+(n-p+1)\,t_p$$
--   over all partial schedules ending at $j$. Its least element, when it exists, is the paper's $\theta^*_j(p)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Aircraft and positions are `Fin n`, 0-based: label $a$ is the paper's aircraft $a+1$ and position $p$ the paper's position $p+1$. Stages are 0-based natural numbers: stage $s$ is the paper's stage $s+1$, so its nodes have length $\min(2k+1,s+1)$, entry $m$ of a node sits at 0-based position $s+1-L+m$, and the arc into stage $s$ has distance $(n-s)\delta_i(j)$. A path is a function `ℕ → List (Fin n)`, of which only the stages below $n$ matter. Separations are required between **every** pair of positions, as §2 states them, not only between consecutive ones. The precedence pruning uses the printed Case II rule ("a position that is less than $b-k$", "greater than $a+k$") and applies it to every pair, where it is vacuous when $x<y$. Removing nodes unreachable from the source or the sink does not change the set of source-sink paths and is not part of the definition. Final aircraft are read with `List.getLastD`/`List.getLast?`; the default values only arise on the empty list, which is never a stage node.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1651–1656: §2 items 1, 2, 4 and the triangle-inequality paragraph (pp. 1651–1652); §3 (pp. 1652–1653); §3.1, Cases I and II and the position-constrained network (pp. 1653–1654); Table 2 (p. 1654); §5.2, definition of θ_i(p) and the arc distances (pp. 1655–1656)

import Mathlib

namespace RunwayCPS.TotalDelay

/-- A runway instance without time windows (§2 and §5.2): `n` aircraft labelled `0, …, n-1` in
FCFS order (label `a` is the paper's aircraft `a + 1`), the maximum position shift `k`, the
minimum separations `δ a b` (leading `a`, trailing `b`), and precedence pairs: `(x, y) ∈ prec`
means that `x` must land before `y`. -/
structure Instance (n : ℕ) where
  k : ℕ
  δ : Fin n → Fin n → ℝ
  prec : Finset (Fin n × Fin n)

variable {n : ℕ}

/-- A `k`-CPS sequence (§1, §2 item 1): a permutation `σ` (position ↦ aircraft, both 0-based)
moving every aircraft at most `k` positions from its FCFS position. -/
def IsCPS (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p : Fin n, |((σ p : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (k : ℤ)

/-- The sequence `σ` respects every precedence pair: `x` is placed before `y`. -/
def RespectsPrec (prec : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x y : Fin n, (x, y) ∈ prec → σ.symm x < σ.symm y

/-- A feasible schedule of the §5.2 problem: a `k`-CPS sequence `σ` respecting the precedence
pairs, with landing times by position `t p ≥ 0` (delay is measured from time `0`) that meet the
separation requirement between **every** pair of positions `p < q`. -/
def IsFeasible (I : Instance n) (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) : Prop :=
  IsCPS I.k σ ∧ RespectsPrec I.prec σ ∧ (∀ p : Fin n, 0 ≤ t p) ∧
    ∀ p q : Fin n, p < q → I.δ (σ p) (σ q) ≤ t q - t p

/-- The total delay `t_1 + ⋯ + t_n` of a schedule (the objective of §5.2). -/
def totalDelay (t : Fin n → ℝ) : ℝ := ∑ p : Fin n, t p

/-- A node of the CPS network at stage `s` (0-based; the paper's stage `s + 1`, §3): a list `w`
of pairwise distinct aircraft of length `min (2k+1) (s+1)`, whose entry `m` occupies the
0-based position `s + 1 - length w + m` and is admissible there, i.e. within `k` of it. The
last entry is the node's *final aircraft*, placed at position `s`. -/
def IsStageNode (k s : ℕ) (w : List (Fin n)) : Prop :=
  w.length = min (2 * k + 1) (s + 1) ∧ w.Nodup ∧
    ∀ m : Fin w.length,
      |(((w.get m : Fin n) : ℕ) : ℤ) - ((s : ℤ) + 1 - (w.length : ℤ) + ((m : ℕ) : ℤ))| ≤ (k : ℤ)

/-- An arc from the stage-`s` node `i` to the stage-`(s+1)` node `j` (0-based stages, §3): the
first `min (2k) (s+1)` aircraft of `j` are the last `min (2k) (s+1)` aircraft of `i`. -/
def IsArc (k s : ℕ) (i j : List (Fin n)) : Prop :=
  j.take (min (2 * k) (s + 1)) = i.drop (i.length - min (2 * k) (s + 1))

/-- The stage-`s` node `w` violates the precedence pair `(x, y)` (§3.1): `y` appears in `w`
before `x`; or `y` sits at a position less than `x - k`; or `x` sits at a position greater than
`y + k` (positions 0-based, entry `m` at position `s + 1 - length w + m`). The last two are the
position-constrained-network rule of Case II, vacuous for admissible nodes when `x < y`. -/
def Violates (k s : ℕ) (w : List (Fin n)) (x y : Fin n) : Prop :=
  (∃ m₁ m₂ : Fin w.length, m₁ < m₂ ∧ w.get m₁ = y ∧ w.get m₂ = x) ∨
  (∃ m : Fin w.length, w.get m = y ∧
      (s : ℤ) + 1 - (w.length : ℤ) + ((m : ℕ) : ℤ) < ((x : ℕ) : ℤ) - (k : ℤ)) ∨
  (∃ m : Fin w.length, w.get m = x ∧
      ((y : ℕ) : ℤ) + (k : ℤ) < (s : ℤ) + 1 - (w.length : ℤ) + ((m : ℕ) : ℤ))

/-- A node of the precedence-pruned CPS network `G` (§3.1) at stage `s`: a stage node violating
no precedence pair of the instance. -/
def IsNodeG (I : Instance n) (s : ℕ) (w : List (Fin n)) : Prop :=
  IsStageNode I.k s w ∧ ∀ x y : Fin n, (x, y) ∈ I.prec → ¬ Violates I.k s w x y

/-- A source-sink path of the CPS network (without precedence pruning): a node `v s` at every
stage `s < n`, with an arc between consecutive stages. Source and sink arcs always exist. -/
def IsPath (k : ℕ) (v : ℕ → List (Fin n)) : Prop :=
  ∀ s : ℕ, s < n → IsStageNode k s (v s) ∧ (s + 1 < n → IsArc k s (v s) (v (s + 1)))

/-- A source-sink path of the precedence-pruned network `G`. -/
def IsPathIn (I : Instance n) (v : ℕ → List (Fin n)) : Prop :=
  ∀ s : ℕ, s < n → IsNodeG I s (v s) ∧ (s + 1 < n → IsArc I.k s (v s) (v (s + 1)))

/-- A path from the source to the node `j` at stage `s` in the CPS network without precedence
pruning: nodes at stages `0, …, s`, consecutive arcs, ending at `v s = j`. -/
def IsPathTo (k s : ℕ) (j : List (Fin n)) (v : ℕ → List (Fin n)) : Prop :=
  v s = j ∧ ∀ q : ℕ, q ≤ s → IsStageNode k q (v q) ∧ (q < s → IsArc k q (v q) (v (q + 1)))

/-- A path from the source to the node `j` at stage `s` in the precedence-pruned network `G`. -/
def IsPathToIn (I : Instance n) (s : ℕ) (j : List (Fin n)) (v : ℕ → List (Fin n)) : Prop :=
  v s = j ∧ ∀ q : ℕ, q ≤ s → IsNodeG I q (v q) ∧ (q < s → IsArc I.k q (v q) (v (q + 1)))

/-- The sequence of a path (§3): position `p` receives the final aircraft of the stage-`p` node.
(The default `p` is only used on an empty list, which is never a stage node.) -/
def pathSeq (v : ℕ → List (Fin n)) (p : Fin n) : Fin n := (v p).getLastD p

/-- `δ_i(j)` (Table 2): the separation between the final aircraft of node `i` (leading) and of
node `j` (trailing). (The value `0` is only used on an empty list, never a stage node.) -/
def nodeDelta (I : Instance n) (i j : List (Fin n)) : ℝ :=
  match i.getLast?, j.getLast? with
  | some a, some b => I.δ a b
  | _, _ => 0

/-- The §5.2 length of a path: the arc from stage `s - 1` into stage `s` (0-based; the paper's
stage `p = s + 1`) has distance `(n - p + 1) δ_i(j) = (n - s) δ_i(j)`; source and sink arcs have
distance `0`. -/
def pathLength (I : Instance n) (v : ℕ → List (Fin n)) : ℝ :=
  ∑ s ∈ Finset.Ico 1 n, ((n : ℝ) - (s : ℝ)) * nodeDelta I (v (s - 1)) (v s)

/-- The values of `θ_j(p) = t_1 + ⋯ + t_{p-1} + (n - p + 1) t_p` (§5.2) over all partial
schedules ending at the node `j` of `G` at stage `s` (0-based, `p = s + 1`): a path `v` in `G`
from the source to `j`, and landing times `t q ≥ 0` (`q ≤ s`) for the final aircraft of its
nodes, separated pairwise as required. In the paper's notation the value is
`∑_{q < s} t q + (n - s) t s`. -/
def thetaSet (I : Instance n) (s : ℕ) (j : List (Fin n)) : Set ℝ :=
  {θ | ∃ (v : ℕ → List (Fin n)) (t : ℕ → ℝ), IsPathToIn I s j v ∧
    (∀ q : ℕ, q ≤ s → 0 ≤ t q) ∧
    (∀ q r : ℕ, q < r → r ≤ s → nodeDelta I (v q) (v r) ≤ t r - t q) ∧
    θ = ∑ q ∈ Finset.range s, t q + ((n : ℝ) - (s : ℝ)) * t s}

end RunwayCPS.TotalDelay


