-- Prove2me | Definitions.Def_CanadaCTP_Model
-- name    : CanadaCTP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:10.586901+00:00
-- url     : https://prove2.me/theorems/65c4bf71-53be-4d8a-8515-12ba2ab1381c
-- title:
--   §2, p.5 — the Stochastic Canadian Traveller Problem on disjoint-path graphs: instances, randomized adaptive policies, runs, $\mathbb E[\pi]$ and $\mathbb E[\mathrm{Opt}]$
-- statement:
--   An **instance** consists of $k$ paths from $s$ to $t$ that share only $s$ and $t$. Path $i$ has $m_i$ edges; edge $j$ of path $i$ joins vertex $j$ and vertex $j+1$ of the path, vertex $0$ is $s$ and vertex $m_i$ is $t$. The weight $X^i_j$ of each edge is an independent, non-negative, finitely supported random variable, given explicitly as a list of value–probability pairs. A **CTP instance** has $k\ge1$ and every $m_i\ge1$.
--
--   A traveller starts at $s$. The weight of an edge is drawn once, when one of its endpoints is reached for the first time, and persists; at the start every edge at $s$ is revealed. Every traversal of an edge costs its weight, every time. A **policy** observes its position and the weights revealed so far (never the unrevealed ones) and chooses, possibly at random and depending on an internal memory of any type, one of: enter a path at $s$, move one vertex towards $t$ or towards $s$, wait, or stop. Reaching $t$ ends the run.
--
--   For a policy $\pi$, $\mathbb E[\pi]$ is its expected total cost and $P_\pi[t]$ its probability of reaching $t$. A policy is **feasible** if it reaches $t$ almost surely, and
--   $$
--   \mathbb E[\mathrm{Opt}] \;=\; \inf\{\mathbb E[\pi] : \pi \text{ feasible}\}.
--   $$
--   The instance also defines $|E|=\sum_i m_i$, $d_i=\sum_j|\operatorname{supp}X^i_j|$, the rescaling factor $\mu$ (the least non-zero realization, $1$ if all are $0$) and $M$ = largest realization$/\mu$ ($1$ if all are $0$).
--
--   This model underlies every statement of the mission.
--
--   **Formalization Note** Edges and paths are 0-indexed (`Fin`). The joint law of the weights is the finite product over realization indices. A run is the law `lawN` of the configuration after $N$ steps; expected cost and arrival probability are suprema over $N$ in $[0,\infty]$. Randomized stateful policies contain the paper's deterministic history-dependent ones (memory = history, point-mass steps). A move that does not exist at the current position leaves the traveller in place at cost $0$.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), §2, p.5; footnote 1, p.2; Algorithm 1 (rescaling), p.7; Theorem 3 (M, d_i), p.6

import Mathlib

namespace CanadaCTP

open scoped ENNReal

/-! # The Stochastic Canadian Traveller Problem on disjoint-path graphs

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
§2, p.5, footnote 1 p.2, and the disjoint-path class of p.5.

**Formalization Note.** A disjoint-path graph is given by `k` internally vertex-disjoint
`s`–`t` paths; path `i` has `m i` edges `j : Fin (m i)` (0-indexed: the paper's edge `j + 1`),
edge `j` joining vertex `j` and vertex `j + 1` of the path, where vertex `0` of every path is `s`
and vertex `m i` is `t`. Parallel one-edge paths are allowed (a multigraph). Edge weights are
independent explicit finite distributions, so the joint law is the finite product over the
realization index `Realz I`; no measure on `ℝ` is built. Costs live in `ℝ≥0∞`. -/

/-- An explicit finitely supported non-negative distribution: a list of (value, probability)
pairs with distinct values, non-negative values, positive probabilities summing to `1`
(p.5: "independent non-negative discrete random variables, which are finitely supported and
given explicitly"). Positive probabilities make the list exactly the support, so
`|supp X| = pts.length`. -/
structure EdgeDist where
  pts : List (ℝ × ℝ)
  nodup : (pts.map Prod.fst).Nodup
  val_nonneg : ∀ p ∈ pts, 0 ≤ p.1
  prob_pos : ∀ p ∈ pts, 0 < p.2
  sum_one : (pts.map Prod.snd).sum = 1

/-- A disjoint-path instance: `k` paths, path `i` has `m i` edges with weight distributions
`X i j`. -/
structure Inst where
  k : ℕ
  m : Fin k → ℕ
  X : (i : Fin k) → Fin (m i) → EdgeDist

/-- The CTP instances of the paper: at least one path and every path has at least one edge
(a connected graph with `s ≠ t`). -/
def Inst.IsCTP (I : Inst) : Prop := 0 < I.k ∧ ∀ i, 0 < I.m i

/-- A joint realization of all edge weights: for every edge, the index of the support point
drawn. -/
abbrev Realz (I : Inst) := (i : Fin I.k) → (j : Fin (I.m i)) → Fin (I.X i j).pts.length

/-- The realized weight of edge `j` of path `i`. -/
def Inst.w (I : Inst) (ι : Realz I) (i : Fin I.k) (j : Fin (I.m i)) : ℝ :=
  ((I.X i j).pts.get (ι i j)).1

/-- The probability of a joint realization (independence of the edge weights). -/
noncomputable def Inst.P (I : Inst) (ι : Realz I) : ℝ≥0∞ :=
  ∏ i, ∏ j, ENNReal.ofReal ((I.X i j).pts.get (ι i j)).2

/-- `|E| = Σᵢ mᵢ`. -/
def nE (I : Inst) : ℕ := ∑ i, I.m i

/-- `dᵢ = Σⱼ |supp(X^i_j)|`. -/
def dsz (I : Inst) (i : Fin I.k) : ℕ := ∑ j, (I.X i j).pts.length

/-- All values in all supports. -/
noncomputable def allVals (I : Inst) : Finset ℝ :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => ((I.X i j).pts.map Prod.fst).toFinset

/-- The rescaling factor of Algorithm 1: the least non-zero realization on any edge, and `1`
if every realization is `0`. -/
noncomputable def mu (I : Inst) : ℝ :=
  if h : ((allVals I).filter (· ≠ 0)).Nonempty then ((allVals I).filter (· ≠ 0)).min' h else 1

/-- The largest realization on any edge (`0` if there are none; all values are `≥ 0`). -/
noncomputable def maxVal (I : Inst) : ℝ := (allVals I).fold max 0 id

/-- Theorem 3's `M`: the largest realization after rescaling the least non-zero one to `1`.
If every realization is `0` the paper's `M` would be `0`; the `max 1` makes it `1` then and
changes nothing otherwise (the largest value is then `≥ μ`). -/
noncomputable def Mbig (I : Inst) : ℝ := max 1 (maxVal I / mu I)

/-- Positions of the traveller. `mid i v` is the interior vertex `v` of path `i`
(`0 < v < m i`, maintained by the dynamics). -/
inductive Pos (I : Inst) where
  | s
  | t
  | mid (i : Fin I.k) (v : ℕ)
  deriving DecidableEq

/-- Moves. `fwd i`: at `s`, enter path `i`; at an interior vertex of path `i`, go one vertex
towards `t`. `bwd`: at an interior vertex, go one vertex towards `s`. `wait`: stay. `stop`: give
up (absorbing). A move that does not exist at the current position leaves the traveller in
place at cost `0`. -/
inductive Move (I : Inst) where
  | fwd (i : Fin I.k)
  | bwd
  | wait
  | stop

/-- What a policy observes: its position and the weights revealed so far (`none` = not yet
revealed). It never sees the realization itself. -/
structure Obs (I : Inst) where
  pos : Pos I
  rev : (i : Fin I.k) → Fin (I.m i) → Option ℝ

/-- A randomized stateful adaptive policy with memory type `Mem`: an initial memory and, from
the memory and the current observation, a distribution over (move, new memory). Deterministic
history-dependent policies (p.5) are the case where `Mem` stores the history and every step is a
point mass. -/
structure Policy (I : Inst) (Mem : Type) where
  init : Mem
  step : Mem → Obs I → PMF (Move I × Mem)

/-- A configuration of a run: memory, position, which edges are revealed, accumulated cost,
and whether the policy has stopped. -/
structure Config (I : Inst) (Mem : Type) where
  mem : Mem
  pos : Pos I
  rev : (i : Fin I.k) → Fin (I.m i) → Bool
  cost : ℝ≥0∞
  stopped : Bool

/-- The start: `s`, unless some path has no edge, in which case `s = t` (only possible for the
one-path PathOpt instance with `m = 0`, Definition 1). -/
noncomputable def startPos (I : Inst) : Pos I := by
  classical
  exact if ∃ i, I.m i = 0 then Pos.t else Pos.s

/-- The initial configuration: `s` is visited, so every first edge is revealed. -/
noncomputable def initCfg (I : Inst) {Mem : Type} (π : Policy I Mem) : Config I Mem :=
  { mem := π.init, pos := startPos I, rev := fun _ j => decide (j.val = 0), cost := 0,
    stopped := false }

/-- The observation of a configuration under realization `ι`. -/
def obsOf (I : Inst) {Mem : Type} (ι : Realz I) (c : Config I Mem) : Obs I :=
  { pos := c.pos, rev := fun i j => if c.rev i j then some (I.w ι i j) else none }

/-- Vertex `v` of path `i` as a position. -/
def vtx (I : Inst) (i : Fin I.k) (v : ℕ) : Pos I :=
  if v = 0 then Pos.s else if I.m i ≤ v then Pos.t else Pos.mid i v

/-- Arrive at vertex `v` of path `i` by traversing edge `e` (paying its realized weight). The
edges of path `i` incident to `v` become revealed (first visit of an endpoint, p.5); `s` is
visited from the start and `t` is absorbing, so their other incident edges never matter. -/
noncomputable def arrive (I : Inst) {Mem : Type} (ι : Realz I) (c : Config I Mem) (mem : Mem)
    (i : Fin I.k) (e : Fin (I.m i)) (v : ℕ) : Config I Mem :=
  { mem := mem, pos := vtx I i v,
    rev := fun i' j => c.rev i' j || decide (i' = i ∧ (j.val = v ∨ j.val + 1 = v)),
    cost := c.cost + ENNReal.ofReal (I.w ι i e), stopped := false }

/-- Apply a move. Every traversal is paid, every time (weights persist, footnote 1, p.2). -/
noncomputable def applyMove (I : Inst) {Mem : Type} (ι : Realz I) (c : Config I Mem)
    (mv : Move I) (mem : Mem) : Config I Mem :=
  let stay : Config I Mem := { c with mem := mem }
  match c.pos, mv with
  | Pos.s, Move.fwd i =>
      if h : 0 < I.m i then arrive I ι c mem i ⟨0, h⟩ 1 else stay
  | Pos.mid i v, Move.fwd i' =>
      if h : i' = i ∧ v < I.m i then arrive I ι c mem i ⟨v, h.2⟩ (v + 1) else stay
  | Pos.mid i v, Move.bwd =>
      if h : 0 < v ∧ v - 1 < I.m i then arrive I ι c mem i ⟨v - 1, h.2⟩ (v - 1) else stay
  | _, Move.stop => { stay with stopped := true }
  | _, _ => stay

/-- One step of a run: absorbing at `t` and after `stop`; otherwise the policy draws a move
from its step distribution and the move is applied. -/
noncomputable def stepCfg (I : Inst) {Mem : Type} (π : Policy I Mem) (ι : Realz I)
    (c : Config I Mem) : PMF (Config I Mem) :=
  if c.pos = Pos.t ∨ c.stopped = true then PMF.pure c
  else (π.step c.mem (obsOf I ι c)).map fun mm => applyMove I ι c mm.1 mm.2

/-- The law of the configuration after `N` steps, for a fixed realization `ι`. -/
noncomputable def lawN (I : Inst) {Mem : Type} (π : Policy I Mem) (ι : Realz I) :
    ℕ → PMF (Config I Mem)
  | 0 => PMF.pure (initCfg I π)
  | N + 1 => (lawN I π ι N).bind (stepCfg I π ι)

/-- Expected total cost `E[π]`: the supremum over the horizon of the expected cost accumulated
in `N` steps (non-decreasing in `N`), averaged over the edge weights. -/
noncomputable def expCost (I : Inst) {Mem : Type} (π : Policy I Mem) : ℝ≥0∞ :=
  ⨆ N : ℕ, ∑ ι : Realz I, I.P ι * ∑' c : Config I Mem, lawN I π ι N c * c.cost

/-- Probability of reaching `t` (non-decreasing in `N` since `t` is absorbing). -/
noncomputable def arrProb (I : Inst) {Mem : Type} (π : Policy I Mem) : ℝ≥0∞ :=
  ⨆ N : ℕ, ∑ ι : Realz I, I.P ι * (lawN I π ι N).toOuterMeasure {c | c.pos = Pos.t}

/-- A feasible policy reaches `t` almost surely. -/
def Feasible (I : Inst) {Mem : Type} (π : Policy I Mem) : Prop := arrProb I π = 1

/-- `E[Opt]`: the infimum of the expected cost over every memory type and every feasible
randomized stateful policy. -/
noncomputable def optCost (I : Inst) : ℝ≥0∞ :=
  ⨅ (Mem : Type) (π : Policy I Mem) (_ : Feasible I π), expCost I π

/-- A biased coin: `true` with probability `p` clamped to `[0,1]`. Used by the coin strategies
(Definition 6) and the ParallelTraveller policy. -/
noncomputable def coinFlip (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal (max 0 (min 1 p))
      else ENNReal.ofReal (1 - max 0 (min 1 p))) (by
    have h0 : 0 ≤ max 0 (min 1 p) := le_max_left _ _
    have h1 : max 0 (min 1 p) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp)

end CanadaCTP


