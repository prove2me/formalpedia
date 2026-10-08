-- Prove2me | Definitions.Def_ProjSchedMinCut_Transform_Setting
-- name    : ProjSchedMinCut_Transform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:19.517265+00:00
-- url     : https://prove2.me/theorems/848537e2-ae85-40f9-b7ec-e358f2605c45
-- title:
--   §2–§2.2, pp. 3–7 — instance, feasible schedules, e(j), ℓ(j), IP (1)–(5), digraph D, a-b-cuts, capacity, n-cuts (Definition 1), map (7)
-- statement:
--   This file fixes the model of §2 of Möhring, Schulz, Stork and Uetz and the minimum cut digraph of §2.2.
--
--   **Instance.** Jobs form the set $J = \{0, \dots, n\}$. Job $j$ has an integral processing time $p_j \ge 0$. A set $L \subseteq J \times J$ of **time lags** is given, and each lag $(i,j) \in L$ has an integral length $d_{ij}$ (possibly negative). There is a time horizon $T \in \mathbb{N}$, and starting job $j$ at time $t$ costs $w_{jt} \in \mathbb{R}$.
--
--   **Feasible schedules, $e(j)$ and $\ell(j)$.** A schedule is a vector $S = (S_0, \dots, S_n)$ of integral start times. It is **feasible** if it is time-feasible and lies within the horizon:
--   $$S_i + d_{ij} \le S_j \quad ((i,j) \in L), \qquad 0 \le S_j,\ \ S_j + p_j \le T \quad (j \in J).$$
--   The **earliest** and **latest feasible start times** of job $j$ are
--   $$e(j) = \min\{S_j : S \text{ feasible}\}, \qquad \ell(j) = \max\{S_j : S \text{ feasible}\}.$$
--
--   **The integer program (1)–(5).** For $x = (x_{jt})$ with integer entries, $j \in J$, $t \in \mathbb{N}$,
--   $$\begin{aligned} &\text{minimize } w(x) = \sum_j \sum_{t=0}^{T} w_{jt} x_{jt} && (1)\\ &\sum_{t=0}^{T} x_{jt} = 1, && j \in J, \quad (2)\\ &\sum_{s=t}^{T} x_{is} + \sum_{s=0}^{t+d_{ij}-1} x_{js} \le 1, && (i,j)\in L,\ t = 0,\dots,T, \quad (3)\\ &x_{jt} \ge 0, && j \in J,\ t = 0, \dots, T, \quad (4)\end{aligned}$$
--   with integrality (5), and with the paper's convention that all variables with time indices outside $[e(j), \ell(j)]$ are $0$. A **feasible solution** satisfies (2)–(5) and that convention; an **optimal solution** is a feasible solution of least cost $w(x)$ among all feasible solutions.
--
--   **The digraph $D = (V, A)$.** Its nodes are a source $a$, a sink $b$ and one node $v_{jt}$ for every job $j$ and $t = e(j), \dots, \ell(j) + 1$. Its arcs are
--   1. **assignment arcs** $(v_{jt}, v_{j,t+1})$ for $t = e(j), \dots, \ell(j)$, of capacity $w_{jt}$;
--   2. **temporal arcs** $(v_{it}, v_{j,t+d_{ij}})$ for every $(i,j) \in L$ and every $t$ with $e(i)+1 \le t \le \ell(i)$ and $e(j)+1 \le t+d_{ij} \le \ell(j)$, of infinite capacity;
--   3. **auxiliary arcs** $(a, v_{j,e(j)})$ and $(v_{j,\ell(j)+1}, b)$ for every $j$, of infinite capacity.
--
--   **Cuts.** An **$a$-$b$-cut** $(X, \bar X)$ is a partition of $V$ with $a \in X$ and $b \in \bar X = V \setminus X$. An arc $(u, v)$ is **in the cut** if $u \in X$ and $v \in \bar X$, and the **capacity** $c(X, \bar X)$ is the sum of the capacities of the arcs in the cut (infinite as soon as one infinite arc is in the cut). A **minimum $a$-$b$-cut** has least capacity among all $a$-$b$-cuts. An **$n$-cut** (Definition 1) is an $a$-$b$-cut in which, for every job $j$, exactly one assignment arc $(v_{jt}, v_{j,t+1})$ is in the cut.
--
--   **The mapping (7).** An $a$-$b$-cut $(X, \bar X)$ is mapped to $x$ with $x_{jt} = 1$ if the assignment arc $(v_{jt}, v_{j,t+1})$ is in the cut, and $x_{jt} = 0$ otherwise.
--
--   These objects are the vocabulary of Theorem 1 and Lemmas 1–4: the scheduling problem with start-time dependent costs is solved by a minimum cut in $D$.
--
--   **Formalization Note** An instance is a structure with fields `p`, `L`, `d`, `T`, `w`; $J$ is `Fin (n + 1)`. The paper never writes the horizon condition as a formula: $0 \le S_j$ and $S_j + p_j \le T$ is read from "$t = 0, 1, 2, \dots, T$", "$e(j) \ge 0$" and "$\ell(j) \le T - p_j$" (p. 5). $e(j)$ and $\ell(j)$ are `sInf`/`sSup` in $\mathbb{Z}$ of the set of feasible start times; they have the intended value only when a feasible schedule exists (on the empty set both are $0$), so every theorem assumes one. The variables are $x : J \to \mathbb{N} \to \mathbb{Z}$; the window convention ("all variables with time indices outside these boundaries are 0", p. 4) is part of feasibility. The second sum of (3) runs over $s = 0, \dots, t + d_{ij} - 1$ and is empty when $t + d_{ij} \le 0$. Arcs are a tagged type (assignment, temporal per lag in $L$, source, sink), so parallel arcs stay distinct; capacities lie in $[0, \infty]$ (`ℝ≥0∞`), with the assignment capacity `ENNReal.ofReal w_jt`, which equals $w_{jt}$ for the non-negative weights the paper assumes. A cut is represented by $X \subseteq V$ with $a \in X$, $b \notin X$.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), pp. 3–7, §2, §2.1 (1)–(5), §2.2, Definition 1, (7)

import Mathlib

namespace ProjSchedMinCut.Transform

open scoped ENNReal

/-- An instance of the project scheduling problem with start-time dependent costs (§2, p. 3):
jobs `J = {0, …, n}` (the type `Fin (n + 1)`), integral non-negative processing times `p`,
the set `L ⊆ J × J` of time lags with integral lengths `d i j`, the time horizon `T`, and the
cost `w j t` of starting job `j` at time `t`. -/
structure Instance (n : ℕ) where
  /-- processing times `p_j` -/
  p : Fin (n + 1) → ℕ
  /-- the set `L` of time lags -/
  L : Finset (Fin (n + 1) × Fin (n + 1))
  /-- the lengths `d_ij` of the time lags -/
  d : Fin (n + 1) → Fin (n + 1) → ℤ
  /-- the time horizon `T` -/
  T : ℕ
  /-- the start-time dependent costs `w_jt` -/
  w : Fin (n + 1) → ℕ → ℝ

variable {n : ℕ}

namespace Instance

/-- A schedule `S` (integral start times) is time-feasible, `S_j ≥ S_i + d_ij` for all
`(i, j) ∈ L`, and lies within the horizon, `0 ≤ S_j` and `S_j + p_j ≤ T` for every job. -/
def Feasible (I : Instance n) (S : Fin (n + 1) → ℤ) : Prop :=
  (∀ ij ∈ I.L, S ij.1 + I.d ij.1 ij.2 ≤ S ij.2) ∧ ∀ j, 0 ≤ S j ∧ S j + (I.p j : ℤ) ≤ I.T

/-- The feasible start times of job `j`: the values `S_j` over feasible schedules `S`. -/
def startTimes (I : Instance n) (j : Fin (n + 1)) : Set ℤ :=
  {t | ∃ S, I.Feasible S ∧ S j = t}

/-- `e(j)`, the earliest feasible start time of job `j` (p. 5). It is the intended value only
when a feasible schedule exists (otherwise `sInf ∅ = 0` in `ℤ`). -/
noncomputable def earliest (I : Instance n) (j : Fin (n + 1)) : ℤ :=
  sInf (I.startTimes j)

/-- `ℓ(j)`, the latest feasible start time of job `j` (p. 5). It is the intended value only
when a feasible schedule exists (otherwise `sSup ∅ = 0` in `ℤ`). -/
noncomputable def latest (I : Instance n) (j : Fin (n + 1)) : ℤ :=
  sSup (I.startTimes j)

/-- Feasibility for the integer program (2)–(5) of §2.1 (p. 4), with integrality (5) built into
the type `ℤ`, together with the window convention of p. 4: variables with time indices before
the earliest or after the latest start time of the job are `0`. -/
def IPFeasible (I : Instance n) (x : Fin (n + 1) → ℕ → ℤ) : Prop :=
  -- (2)
  (∀ j, ∑ t ∈ Finset.range (I.T + 1), x j t = 1) ∧
  -- (3): for `(i, j) ∈ L` and `t = 0, …, T`,
  --      `∑_{s=t}^{T} x_is + ∑_{s=0}^{t+d_ij-1} x_js ≤ 1`
  (∀ ij ∈ I.L, ∀ t ∈ Finset.range (I.T + 1),
      ∑ s ∈ Finset.Icc t I.T, x ij.1 s
        + ∑ s ∈ Finset.range ((t : ℤ) + I.d ij.1 ij.2).toNat, x ij.2 s ≤ 1) ∧
  -- (4)
  (∀ j, ∀ t ∈ Finset.range (I.T + 1), 0 ≤ x j t) ∧
  -- window convention
  (∀ j (t : ℕ), ((t : ℤ) < I.earliest j ∨ I.latest j < (t : ℤ)) → x j t = 0)

/-- The objective (1), `w(x) = ∑_j ∑_t w_jt x_jt`, with `t = 0, …, T`. -/
def cost (I : Instance n) (x : Fin (n + 1) → ℕ → ℤ) : ℝ :=
  ∑ j, ∑ t ∈ Finset.range (I.T + 1), I.w j t * (x j t : ℝ)

/-- An optimal solution of (1)–(5): feasible, and of least cost among feasible solutions. -/
def IsOptimal (I : Instance n) (x : Fin (n + 1) → ℕ → ℤ) : Prop :=
  I.IPFeasible x ∧ ∀ y, I.IPFeasible y → I.cost x ≤ I.cost y

end Instance

/-- Nodes of the minimum cut digraph `D` (p. 5): the source `a`, the sink `b`, and `v_jt`. -/
inductive Node (n : ℕ) where
  | a : Node n
  | b : Node n
  | v (j : Fin (n + 1)) (t : ℤ) : Node n
  deriving DecidableEq

/-- Arc labels of `D` (p. 5). Arcs are tagged by their kind and index, so that parallel arcs
(for instance two time lags between the same jobs) remain distinct arcs:
* `assign j t` is the assignment arc `(v_jt, v_j,t+1)`;
* `temporal ij t` is the temporal arc `(v_it, v_j,t+d_ij)` of the time lag `ij = (i, j) ∈ L`;
* `src j` is the auxiliary arc `(a, v_j,e(j))`;
* `snk j` is the auxiliary arc `(v_j,ℓ(j)+1, b)`. -/
inductive Arc (n : ℕ) where
  | assign (j : Fin (n + 1)) (t : ℤ) : Arc n
  | temporal (ij : Fin (n + 1) × Fin (n + 1)) (t : ℤ) : Arc n
  | src (j : Fin (n + 1)) : Arc n
  | snk (j : Fin (n + 1)) : Arc n
  deriving DecidableEq

namespace Instance

/-- The node set `V := {v_jt | j ∈ J, t = e(j), …, ℓ(j) + 1} ∪ {a, b}` of `D` (p. 5). -/
def V (I : Instance n) : Set (Node n) :=
  {Node.a, Node.b} ∪
    {u | ∃ j t, u = Node.v j t ∧ I.earliest j ≤ t ∧ t ≤ I.latest j + 1}

/-- The tail of an arc. -/
noncomputable def tail (I : Instance n) : Arc n → Node n
  | .assign j t => .v j t
  | .temporal ij t => .v ij.1 t
  | .src _ => .a
  | .snk j => .v j (I.latest j + 1)

/-- The head of an arc. -/
noncomputable def head (I : Instance n) : Arc n → Node n
  | .assign j t => .v j (t + 1)
  | .temporal ij t => .v ij.2 (t + I.d ij.1 ij.2)
  | .src j => .v j (I.earliest j)
  | .snk _ => .b

/-- Arc capacities (p. 5): `c(v_jt, v_j,t+1) := w_jt` on assignment arcs, `∞` on temporal and
auxiliary arcs. -/
noncomputable def cap (I : Instance n) : Arc n → ℝ≥0∞
  | .assign j t => ENNReal.ofReal (I.w j t.toNat)
  | .temporal _ _ => ⊤
  | .src _ => ⊤
  | .snk _ => ⊤

/-- The arc set `A` of `D` (p. 5):
* assignment arcs `(v_jt, v_j,t+1)` for every job `j` and `t = e(j), …, ℓ(j)`;
* temporal arcs `(v_it, v_j,t+d_ij)` for every `(i, j) ∈ L` and every `t` with
  `e(i) + 1 ≤ t ≤ ℓ(i)` and `e(j) + 1 ≤ t + d_ij ≤ ℓ(j)`;
* auxiliary arcs `(a, v_j,e(j))` and `(v_j,ℓ(j)+1, b)` for every job `j`. -/
noncomputable def A (I : Instance n) : Finset (Arc n) :=
  (Finset.univ.biUnion fun j =>
      (Finset.Icc (I.earliest j) (I.latest j)).image (Arc.assign j)) ∪
    (I.L.biUnion fun ij =>
      ((Finset.Icc (I.earliest ij.1 + 1) (I.latest ij.1)).filter fun t =>
          I.earliest ij.2 + 1 ≤ t + I.d ij.1 ij.2 ∧ t + I.d ij.1 ij.2 ≤ I.latest ij.2).image
        (Arc.temporal ij)) ∪
    Finset.univ.image Arc.src ∪
    Finset.univ.image Arc.snk

/-- An `a`-`b`-cut `(X, X̄)` of `D` (p. 6), given by `X`: `X ⊆ V`, `a ∈ X`, `b ∉ X`; then
`X̄ = V \ X`. -/
def IsCut (I : Instance n) (X : Set (Node n)) : Prop :=
  X ⊆ I.V ∧ Node.a ∈ X ∧ Node.b ∉ X

/-- An arc `(u, v)` is in the cut `(X, X̄)` if `u ∈ X` and `v ∈ X̄ = V \ X` (p. 6). -/
def InCut (I : Instance n) (X : Set (Node n)) (α : Arc n) : Prop :=
  I.tail α ∈ X ∧ I.head α ∈ I.V \ X

open Classical in
/-- The capacity `c(X, X̄)` of the cut: the sum of the capacities of the arcs of `A` in the cut
(p. 6), with value `∞` as soon as an infinite-capacity arc is in the cut. -/
noncomputable def cutCap (I : Instance n) (X : Set (Node n)) : ℝ≥0∞ :=
  ∑ α ∈ I.A.filter (fun α => I.InCut X α), I.cap α

/-- A minimum `a`-`b`-cut: an `a`-`b`-cut whose capacity is at most that of every
`a`-`b`-cut (p. 6). -/
def IsMinCut (I : Instance n) (X : Set (Node n)) : Prop :=
  I.IsCut X ∧ ∀ Y, I.IsCut Y → I.cutCap X ≤ I.cutCap Y

/-- Definition 1 (p. 6): an `n`-cut is an `a`-`b`-cut such that for every job `j` exactly one
assignment arc `(v_jt, v_j,t+1)` is in the cut. -/
def IsNCut (I : Instance n) (X : Set (Node n)) : Prop :=
  I.IsCut X ∧ ∀ j, ∃! t : ℤ, Arc.assign j t ∈ I.A ∧ I.InCut X (Arc.assign j t)

open Classical in
/-- The mapping (7) (p. 7): `x_jt = 1` if the assignment arc `(v_jt, v_j,t+1)` is (an arc of `D`
and) in the cut `(X, X̄)`, and `x_jt = 0` otherwise. -/
noncomputable def xOfCut (I : Instance n) (X : Set (Node n)) : Fin (n + 1) → ℕ → ℤ :=
  fun j t => if Arc.assign j (t : ℤ) ∈ I.A ∧ I.InCut X (Arc.assign j (t : ℤ)) then 1 else 0

end Instance

end ProjSchedMinCut.Transform


