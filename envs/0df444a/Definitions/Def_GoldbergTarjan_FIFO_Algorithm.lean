-- Prove2me | Definitions.Def_GoldbergTarjan_FIFO_Algorithm
-- name    : GoldbergTarjan_FIFO_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:32:48.270808+00:00
-- url     : https://prove2.me/theorems/2478ef3b-e868-446b-b565-0e4cb913da0e
-- title:
--   Edge lists, the push/relabel operation (Fig. 3), the discharge operation (Fig. 4) and runs of the first-in, first-out algorithm
-- statement:
--   This file defines the first-in, first-out (FIFO) push–relabel algorithm of §4 of Goldberg and Tarjan.
--
--   **Edge lists.** Each vertex $v$ has a list $L(v)$ of the vertices $w$ such that $(v,w) \in E$ or $(w,v) \in E$, each exactly once, in a fixed but arbitrary order. Each vertex has a **current edge**, a position in its list; initially the first.
--
--   **Push/relabel$(v)$** (Fig. 3) is applicable when $v$ is active. Let $\{v,w\}$ be the current edge of $v$. If push$(v,w)$ is applicable, it is performed. Otherwise, if $\{v,w\}$ is not the last edge on $L(v)$, the next edge becomes current; if it is the last, the first edge becomes current and $v$ is relabeled.
--
--   **Discharge** (Fig. 4) acts on the queue $Q$ of active vertices. It removes the vertex $v$ at the front of $Q$ and repeats push/relabel$(v)$, adding to the rear of $Q$ each vertex $w$ that becomes active during one of these operations, until $e(v) = 0$ or $d(v)$ has increased. Finally, $v$ is added to the rear of $Q$ if it is still active.
--
--   **Passes.** Each queue entry carries the number of the pass over the queue in which it is discharged. The vertices placed in the queue at initialization belong to pass $1$. A vertex added during a discharge of pass $i$ belongs to pass $i+1$.
--
--   **Runs.** A run of $K$ discharges starts from the initial preflow and the simple labeling, with every current edge at the first position. The initial queue contains each vertex of $$\{ v \in V - \{s,t\} : c(s,v) > 0 \}$$ once, in any order, all in pass $1$. Each subsequent state arises from the previous one by one discharge.
--
--   These definitions carry the statements of Lemmas 3.7, 3.8, 4.1, 4.3 and Corollary 4.4 about the FIFO algorithm.
--
--   **Formalization Note** The configuration is `(f, d, cur)`, and `cur v` is a 0-based index into `L v`. Push/relabel is the total function `pushRelabel`. Its applicability `PRApplicable` also requires that the current edge exists, which excludes vertices with an empty edge list. The $j$-th configuration inside a discharge is `prIter … j`, the $j$-fold iterate. `DischargeStep S J S'` makes the number `J ≥ 1` of push/relabel operations explicit, and the loop guard is checked after each of them against the label at the start of the discharge. `IsFIFORun N L K S J` lists the states `S 0, …, S K` and the numbers `J k`. The printed variant of Fig. 4, which stops as soon as $v$ is relabeled, is formalized.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, pp. 929–930, §4: edge lists and current edges p. 929, initial Q p. 929, Fig. 3 and Fig. 4 p. 930, the first-in first-out algorithm and passes p. 930

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel

open Classical

namespace GoldbergTarjan.FIFO

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Edge lists (§4, p. 929). `L v` is the list of the vertices `w` such that `{v, w}` is an
undirected edge of `G`, i.e. `(v, w) ∈ E` or `(w, v) ∈ E` (`c(v, w) > 0` or `c(w, v) > 0`), each
exactly once, "in fixed but arbitrary order". -/
def IsEdgeList (N : Network V) (L : V → List V) : Prop :=
  ∀ v, (L v).Nodup ∧ ∀ w, w ∈ L v ↔ (0 < N.c v w ∨ 0 < N.c w v)

/-- The algorithm's data apart from the queue: the preflow `f`, the labeling `d`, and the current
edge of each vertex, `cur v` being the (0-based) position of the current edge of `v` in `L v`. -/
structure Config (V : Type) where
  f : V → V → ℝ
  d : V → ℕ∞
  cur : V → ℕ

/-- Applicability of `push/relabel(v)` (Fig. 3, p. 930): `v` is active. We also require that the
current edge of `v` exists (`cur v` is a valid position in `L v`); for an active vertex this holds
in every run of the algorithm, and it makes the operation undefined on an empty edge list. -/
def PRApplicable (N : Network V) (L : V → List V) (v : V) (σ : Config V) : Prop :=
  IsActive N σ.f σ.d v ∧ σ.cur v < (L v).length

/-- The action of `push/relabel(v)` (Fig. 3, p. 930). Let `{v, w}` be the current edge of `v`.
If `push(v, w)` is applicable then `push(v, w)`; else if `{v, w}` is not the last edge on the edge
list of `v`, the next edge becomes the current edge; else the first edge becomes the current edge
and `relabel(v)` is performed (the action of Fig. 1: `d(v) ← min{d(w) + 1 | (v, w) ∈ E_f}`).
When `v` has no current edge the configuration is returned unchanged (this case is excluded by
`PRApplicable`). -/
noncomputable def pushRelabel (N : Network V) (L : V → List V) (v : V) (σ : Config V) :
    Config V :=
  match (L v)[σ.cur v]? with
  | none => σ
  | some w =>
    if PushApplicable N σ.f σ.d v w then
      { σ with f := pushFlow N σ.f v w }
    else if σ.cur v + 1 < (L v).length then
      { σ with cur := Function.update σ.cur v (σ.cur v + 1) }
    else
      { σ with d := Function.update σ.d v (relabelLabel N σ.f σ.d v),
               cur := Function.update σ.cur v 0 }

/-- The configuration after `j` consecutive `push/relabel(v)` operations starting from `σ`. -/
noncomputable def prIter (N : Network V) (L : V → List V) (v : V) (σ : Config V) (j : ℕ) :
    Config V :=
  (pushRelabel N L v)^[j] σ

/-- The vertex added to the rear of `Q` by one `push/relabel(v)` operation from `σ` (Fig. 4):
`[w]` if `{v, w}` is the current edge and `w` "becomes active during this push/relabel operation",
i.e. `w` is not active before the operation and is active after it; `[]` otherwise. -/
noncomputable def activated (N : Network V) (L : V → List V) (v : V) (σ : Config V) : List V :=
  match (L v)[σ.cur v]? with
  | none => []
  | some w =>
    if ¬ IsActive N σ.f σ.d w ∧ IsActive N (pushRelabel N L v σ).f (pushRelabel N L v σ).d w
    then [w] else []

/-- The loop guard of the discharge operation (Fig. 4): `e(v) = 0` or `d(v)` has increased,
comparing the current configuration `σ` with the configuration `σ₀` at the start of the discharge. -/
def DischargeStop (v : V) (σ₀ σ : Config V) : Prop :=
  excess σ.f v = 0 ∨ σ₀.d v < σ.d v

/-- A state of the first-in, first-out algorithm: the configuration and the queue `Q`. Each queue
entry `(v, i)` records the vertex and the number `i` of the pass over the queue in which it will be
discharged: `1` for the vertices added during the initialization, and `i + 1` for vertices added
during a discharge of pass `i` (p. 930). -/
structure State (V : Type) where
  cfg : Config V
  Q : List (V × ℕ)

/-- The discharge operation (Fig. 4, p. 930), with `J` the number of `push/relabel` operations it
performs. It applies to a state whose queue has front entry `(v, i)`: `v` is removed from the front
of `Q`; `push/relabel(v)` is repeated (it must be applicable each time) until, for the first time,
`e(v) = 0` or `d(v)` has increased (Repeat … until: at least one operation); every `w` that becomes
active during one of these operations is added to the rear of `Q`, in order; finally `v` is added
to the rear of `Q` if it is still active. Every added vertex is tagged with pass number `i + 1`. -/
def DischargeStep (N : Network V) (L : V → List V) (S : State V) (J : ℕ) (S' : State V) : Prop :=
  ∃ v i rest, S.Q = (v, i) :: rest ∧
    0 < J ∧
    (∀ j < J, PRApplicable N L v (prIter N L v S.cfg j)) ∧
    (∀ j, 1 ≤ j → j < J → ¬ DischargeStop v S.cfg (prIter N L v S.cfg j)) ∧
    DischargeStop v S.cfg (prIter N L v S.cfg J) ∧
    S'.cfg = prIter N L v S.cfg J ∧
    S'.Q = rest
      ++ (List.range J).flatMap
          (fun j => (activated N L v (prIter N L v S.cfg j)).map (fun w => (w, i + 1)))
      ++ (if IsActive N (prIter N L v S.cfg J).f (prIter N L v S.cfg J).d v
          then [(v, i + 1)] else [])

/-- The initial configuration (Fig. 2 with the simple labeling, and §4): the initial preflow, the
labels `d(s) = n`, `d(v) = 0` otherwise, and the first edge of every edge list as current edge. -/
def initConfig (N : Network V) : Config V where
  f := initFlow N
  d := initLabel N
  cur := fun _ => 0

/-- The initial queue (p. 929): `Q = {v ∈ V − {s, t} | c(s, v) > 0}`, each such vertex exactly
once, in an arbitrary order, every entry tagged with pass number `1`. -/
def IsInitialQueue (N : Network V) (Q : List (V × ℕ)) : Prop :=
  (Q.map Prod.fst).Nodup ∧
    (∀ x, x ∈ Q.map Prod.fst ↔ (x ≠ N.s ∧ x ≠ N.t ∧ 0 < N.c N.s x)) ∧
    ∀ p ∈ Q, p.2 = 1

/-- A run of the first-in, first-out algorithm (p. 930) consisting of `K` discharge operations:
`L` is an edge list, `S 0` is the initial state (initial configuration and initial queue), and for
every `k < K`, `S (k + 1)` is obtained from `S k` by one discharge operation performing
`J k` push/relabel operations. States `S k` with `k > K` are irrelevant. -/
def IsFIFORun (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ) : Prop :=
  IsEdgeList N L ∧ (S 0).cfg = initConfig N ∧ IsInitialQueue N (S 0).Q ∧
    ∀ k < K, DischargeStep N L (S k) (J k) (S (k + 1))

/-- The vertex at the front of the queue of `S` (the vertex discharged next); `s` if the queue is
empty (this default is never used for the discharges of a run, whose queues are nonempty). -/
def frontVertex (N : Network V) (S : State V) : V :=
  match S.Q with
  | [] => N.s
  | p :: _ => p.1

/-- The pass number of the front entry of the queue of `S`; `0` if the queue is empty. -/
def frontPass (S : State V) : ℕ :=
  match S.Q with
  | [] => 0
  | p :: _ => p.2

end GoldbergTarjan.FIFO


