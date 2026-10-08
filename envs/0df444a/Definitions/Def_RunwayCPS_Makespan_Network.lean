-- Prove2me | Definitions.Def_RunwayCPS_Makespan_Network
-- name    : RunwayCPS_Makespan_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:59.957926+00:00
-- url     : https://prove2.me/theorems/1b8fef99-4d55-478f-add3-c310cd95d9a9
-- title:
--   §§2–3.1: runway instance, k-CPS sequences, feasible schedules, the CPS network and its precedence pruning
-- statement:
--   This file fixes the single-runway scheduling model under **constrained position shifting** (CPS) and the network on which the algorithms run.
--
--   **Instance.** There are $n$ aircraft, labelled $0,1,\dots,n-1$ in first-come-first-served (FCFS) order (label $a$ is the paper's aircraft $a+1$). The data are a maximum position shift $k\in\mathbb N$, a minimum separation $\delta_{ab}\in\mathbb R$ required between a leading aircraft $a$ and a trailing aircraft $b$, a time window $[e(a),l(a)]$ for each aircraft $a$, and a finite set of precedence pairs, where $(x,y)$ means that $x$ must land before $y$.
--
--   **Sequences and schedules.** Positions in the landing sequence are also numbered $0,\dots,n-1$. A **$k$-CPS sequence** is a bijection $\sigma$ from positions to aircraft such that
--
--   $$|\sigma(p)-p|\le k\quad\text{for every position } p,$$
--
--   that is, every aircraft lands at most $k$ positions away from its FCFS position. A **feasible schedule** is a $k$-CPS sequence $\sigma$ together with landing times $t_0,\dots,t_{n-1}$ (by position) such that
--
--   1. $e(\sigma(p))\le t_p\le l(\sigma(p))$ for every position $p$;
--   2. $\delta_{\sigma(p)\sigma(q)}\le t_q-t_p$ for **every** pair of positions $p<q$ (pairwise, not only consecutive, separations);
--   3. for every precedence pair $(x,y)$, the position of $x$ is strictly smaller than the position of $y$.
--
--   **The CPS network.** Stages are numbered $p=1,\dots,n$ (stage $p$ is the paper's position $p$). A **node of stage $p$** is a list of $L=\min\{2k+1,p\}$ pairwise distinct aircraft that occupy the positions $p-L,\dots,p-1$ (0-based) in that order, each within $k$ of its FCFS position at the position it occupies. Its last entry, sitting at position $p-1$, is its **final aircraft**. There is an **arc** from a stage-$p$ node $i$ to a stage-$(p+1)$ node $j$ when the first $\min\{2k,p\}$ aircraft of $j$ are the last $\min\{2k,p\}$ aircraft of $i$. A **source-sink path** chooses one node $v_p$ in every stage $p=1,\dots,n$ with an arc from $v_p$ to $v_{p+1}$ for $p<n$; its **sequence** places at position $q$ the final aircraft of $v_{q+1}$.
--
--   **Precedence pruning.** A stage-$p$ node $w$ **violates** the pair $(x,y)$ if $y$ appears before $x$ in $w$, or $w$ has $y$ at a position less than $x-k$, or $x$ at a position greater than $y+k$ (the position constraint of Case II, which only bites when $x>y$). The **pruned network** $G$ keeps the nodes that violate no precedence pair, with the same arcs.
--
--   This is the combinatorial substrate of every algorithm in the paper: schedules are searched as paths of $G$ instead of as permutations.
--
--   **Formalization Note** Aircraft, positions and list entries are 0-based; stages are 1-based. The final aircraft of a node is its last list entry (`getLastD`, whose default is never reached on a node, which is nonempty); this needs `[NeZero n]`. A path is a function from $\mathbb N$ to lists whose values outside the stages $1,\dots,n$ are irrelevant. Source and sink nodes are implicit: their arcs exist to every stage-1 node and from every stage-$n$ node. The removal of nodes unreachable from the source or the sink is not modelled, since it does not change the set of source-sink paths. The Case II position filter uses the paper's printed "i.e." clause ($<x-k$, $>y+k$).
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1651–1654, §2 items 1–4, §3, §3.1 (Cases I and II, position-constrained network)

import Mathlib

namespace RunwayCPS.Makespan

/-- A runway scheduling instance with `n` aircraft (§2). Aircraft are labelled `0, …, n-1`
in FCFS order (label `a` is the paper's aircraft `a + 1`). `k` is the maximum position shift,
`δ a b` the minimum separation between leading aircraft `a` and trailing aircraft `b`,
`[e a, l a]` the time window of aircraft `a`, and `(x, y) ∈ prec` means that `x` must land
before `y`. -/
structure Instance (n : ℕ) where
  k : ℕ
  δ : Fin n → Fin n → ℝ
  e : Fin n → ℝ
  l : Fin n → ℝ
  prec : Finset (Fin n × Fin n)

variable {n : ℕ}

/-- A `k`-CPS sequence (§1, §2 item 1): a bijection `σ` from positions to aircraft (both
0-based) such that every aircraft is at most `k` positions away from its FCFS position. -/
def IsCPS (k : ℕ) (σ : Fin n → Fin n) : Prop :=
  Function.Bijective σ ∧ ∀ p : Fin n, |((σ p : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (k : ℤ)

/-- The sequence `σ` respects every precedence pair: if `(x, y) ∈ prec`, then the position of
`x` is strictly before the position of `y`. -/
def RespectsPrec (prec : Finset (Fin n × Fin n)) (σ : Fin n → Fin n) : Prop :=
  ∀ xy ∈ prec, ∀ p q : Fin n, σ p = xy.1 → σ q = xy.2 → p < q

/-- A feasible schedule (§2): a `k`-CPS sequence `σ` (position ↦ aircraft) with landing
times by position `t`, satisfying the time windows, the **pairwise** minimum separations
between every leading and every trailing aircraft, and the precedence constraints. -/
def IsFeasible (I : Instance n) (σ : Fin n → Fin n) (t : Fin n → ℝ) : Prop :=
  IsCPS I.k σ ∧
  (∀ p : Fin n, I.e (σ p) ≤ t p ∧ t p ≤ I.l (σ p)) ∧
  (∀ p q : Fin n, p < q → I.δ (σ p) (σ q) ≤ t q - t p) ∧
  RespectsPrec I.prec σ

/-- In a node `w` of stage `p` (stages are 1-based, `1 ≤ p ≤ n`), the entry with list index
`m` occupies the 0-based sequence position `p - length w + m`; in particular the last entry
(the final aircraft) occupies position `p - 1`, i.e. the paper's position `p`. -/
def entryPos (p : ℕ) (w : List (Fin n)) (m : ℕ) : ℤ :=
  (p : ℤ) - (w.length : ℤ) + (m : ℤ)

/-- `w` is a node of stage `p` of the CPS network (§3): a list of `min (2k+1) p` pairwise
distinct aircraft, each of which is admissible (within `k` of its FCFS position) at the
position it occupies. -/
def IsStageNode (k p : ℕ) (w : List (Fin n)) : Prop :=
  w.length = min (2 * k + 1) p ∧ w.Nodup ∧
  ∀ m : Fin w.length, |((w[m] : Fin n) : ℤ) - entryPos p w m| ≤ (k : ℤ)

instance (k p : ℕ) : DecidablePred (IsStageNode (n := n) k p) := by
  intro w; unfold IsStageNode; infer_instance

/-- The (finite) set of stage-`p` nodes of the CPS network. -/
def stageNodes (n k p : ℕ) : Finset (List (Fin n)) :=
  ((Finset.univ : Finset (Fin (min (2 * k + 1) p) → Fin n)).image List.ofFn).filter
    (IsStageNode k p)

/-- An arc from the stage-`p` node `i` to the stage-`(p+1)` node `j` (§3): the first
`min (2k) p` aircraft of `j` are the last `min (2k) p` aircraft of `i`. -/
def IsArc (k p : ℕ) (i j : List (Fin n)) : Prop :=
  j.take (min (2 * k) p) = i.drop (i.length - min (2 * k) p)

instance (k p : ℕ) (i j : List (Fin n)) : Decidable (IsArc k p i j) := by
  unfold IsArc; infer_instance

/-- `x` appears strictly before `y` in the list `w`. -/
def BeforeIn (w : List (Fin n)) (x y : Fin n) : Prop :=
  ∃ i j : Fin w.length, i < j ∧ w[i] = x ∧ w[j] = y

instance (w : List (Fin n)) (x y : Fin n) : Decidable (BeforeIn w x y) := by
  unfold BeforeIn; infer_instance

/-- The position-constraint violation of §3.1, Case II, for the pair `(x, y)` (`x` must land
before `y`): the stage-`p` node `w` has `y` at a position less than `x - k`, or `x` at a
position greater than `y + k` (the printed rule; positions and labels both shifted to
0-based). -/
def PosViolates (k p : ℕ) (x y : Fin n) (w : List (Fin n)) : Prop :=
  ∃ m : Fin w.length,
    (w[m] = y ∧ entryPos p w m < ((x : ℕ) : ℤ) - k) ∨
    (w[m] = x ∧ entryPos p w m > ((y : ℕ) : ℤ) + k)

instance (k p : ℕ) (x y : Fin n) (w : List (Fin n)) : Decidable (PosViolates k p x y w) := by
  unfold PosViolates; infer_instance

/-- The stage-`p` node `w` violates the precedence pair `(x, y)` (§3.1): `y` appears before
`x` in `w`, or `w` violates the position constraint of Case II. -/
def Violates (k p : ℕ) (x y : Fin n) (w : List (Fin n)) : Prop :=
  BeforeIn w y x ∨ PosViolates k p x y w

instance (k p : ℕ) (x y : Fin n) (w : List (Fin n)) : Decidable (Violates k p x y w) := by
  unfold Violates; infer_instance

/-- `w` is a node of stage `p` of the precedence-pruned network `G` (§3.1): a stage-`p` node
that violates no precedence pair of the instance. -/
def IsGNode (I : Instance n) (p : ℕ) (w : List (Fin n)) : Prop :=
  IsStageNode I.k p w ∧ ∀ xy ∈ I.prec, ¬ Violates I.k p xy.1 xy.2 w

instance (I : Instance n) (p : ℕ) : DecidablePred (IsGNode I p) := by
  intro w; unfold IsGNode; infer_instance

/-- The (finite) set of stage-`p` nodes of the pruned network `G`. -/
def GNodes (I : Instance n) (p : ℕ) : Finset (List (Fin n)) :=
  (stageNodes n I.k p).filter (IsGNode I p)

/-- A source-sink path in the network whose stage-`p` nodes are those satisfying `N p`:
an assignment `v p` of a node to every stage `p = 1, …, n` with an arc between consecutive
stages (values of `v` outside `1, …, n` are irrelevant). -/
def IsPathIn (n : ℕ) (N : ℕ → List (Fin n) → Prop) (k : ℕ) (v : ℕ → List (Fin n)) : Prop :=
  (∀ p, 1 ≤ p → p ≤ n → N p (v p)) ∧
  ∀ p, 1 ≤ p → p < n → IsArc k p (v p) (v (p + 1))

/-- The final aircraft of a node: its last entry (every node of stage `p ≥ 1` is nonempty;
the default is never used on a node). -/
def final [NeZero n] (w : List (Fin n)) : Fin n :=
  w.getLastD default

/-- The aircraft sequence read off a path: the 0-based position `q` receives the final
aircraft of the node at stage `q + 1`. -/
def pathSeq [NeZero n] (v : ℕ → List (Fin n)) : Fin n → Fin n :=
  fun q => final (v ((q : ℕ) + 1))

end RunwayCPS.Makespan


