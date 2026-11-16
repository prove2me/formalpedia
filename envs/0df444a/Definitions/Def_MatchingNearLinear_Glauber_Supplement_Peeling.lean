-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Supplement_Peeling
-- name    : MatchingNearLinear_Glauber_Supplement_Peeling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:30.07776+00:00
-- url     : https://prove2.me/theorems/afdc79b6-84c5-441f-ba43-0a65cb189183
-- title:
--   Single-edge GD trajectories and the occupation-interval peeling algorithm
-- statement:
--   Let $G$ be a labeled simple graph with vertices $[n]$ and edges $[m]$, and let $\nu(G)$ be its **maximum matching size**. For activities $\lambda_e>0$ put $p_e=\lambda_e/(1+\lambda_e)$ and $p^*=\max_e p_e$.
--
--   An **update tape** of length $T$ is a sequence of pairs $(e_s,B_s)$, $s=1,\dots,T$, with $e_s$ an edge and $B_s\in\{0,1\}$ a mark. Starting from a matching $M_0$, **single-edge GD** performs update $s$ by deleting $e_s$ if present and then inserting it when $B_s=1$ and both endpoints of $e_s$ are unmatched; $M_t$ is the state after $t$ updates, $t\in\{0,\dots,T\}$.
--
--   The **occupation-interval algorithm** of §5.1 builds **records**: each positive-marked update $s$ gives a record $(e_s,[s,d))$, where $d$ is the next update time of $e_s$ or $T+1$; each edge $e\in M_0$ gives an initial record $(e,[0,d))$ ending at its first update or at $T+1$. Two distinct records **conflict** if their edges share an endpoint and their intervals overlap. First all initial records are accepted and the noninitial records conflicting with them are rejected. Among the remaining active records, a record is **ready** if no active record with an earlier start conflicts with it; one **peeling round** accepts every ready record, rejects every other active record conflicting with a ready one, and removes the decided records. $R$ is the number of peeling rounds until no active record remains. The batch's state at time $t$ is the set of edges of accepted records whose intervals contain $t$; its **output** is the state at time $T$.
--
--   The **batch algorithm** on $N$ updates splits the tape into $\lceil N/m\rceil$ consecutive batches of at most $m$ updates and passes the output of each batch to the next.
--
--   **Formalization Note** Record intervals use the update numbering $s=1,\dots,T$ (tape index $s-1$). The number of rounds is counted over the first $|\text{records}|+1$ iterates, which suffices because each round with active records decides the earliest of them.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §5, printed p. 22 (PDF p. 24); §5.1, printed pp. 22–23 (PDF pp. 24–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_MatchingModel

set_option autoImplicit false

/-!
# Single-edge GD trajectories and the occupation-interval peeling algorithm

Miao–Yin, *Sampling Matchings in Near-linear Time*, STOC 2027 submission #444, §5 and §5.1
(printed pp. 22–23, PDF pp. 24–25). An update tape of length `T` is a sequence of pairs
`(e_s, B_s)`; update `s` (numbered `1,…,T`) deletes `e_s` if present and then inserts it when
`B_s = 1` and both endpoints are unmatched. Times `t ∈ {0,…,T}` index the state after `t` updates.
-/

namespace MatchingNearLinear.Glauber.Supplement

open scoped BigOperators
noncomputable section
open Classical

open MatchingNearLinear.Glauber

/-- The maximum matching size `ν(G)`. -/
def maxMatchingSize {n m : ℕ} (G : Input n m) : ℕ :=
  (Finset.univ.filter fun M : Config m => EdmondsMatching65.Polyhedron.IsMatching G.graph M).sup
    Finset.card

/-- `p_e = λ_e / (1 + λ_e)`. -/
def markProb {m : ℕ} (lam : Fin m → ℝ) (e : Fin m) : ℝ := lam e / (1 + lam e)

/-- `p* = max_e p_e` (used only for `m ≥ 1`). -/
def maxMarkProb {m : ℕ} (lam : Fin m → ℝ) : ℝ := ⨆ e, markProb lam e

/-- Vertex `w` is covered by an edge of `M`. -/
def Covered {n m : ℕ} (G : Input n m) (M : Config m) (w : Fin n) : Prop :=
  ∃ f ∈ M, G.u f = w ∨ G.v f = w

/-- Two edges share an endpoint (every edge shares an endpoint with itself). -/
def ShareEndpoint {n m : ℕ} (G : Input n m) (e f : Fin m) : Prop :=
  G.u e = G.u f ∨ G.u e = G.v f ∨ G.v e = G.u f ∨ G.v e = G.v f

/-- One single-edge GD update with chosen edge `e` and mark `b`. -/
def gdUpdate {n m : ℕ} (G : Input n m) (M : Config m) (x : Fin m × Bool) : Config m :=
  let M' := M.erase x.1
  if x.2 = true ∧ ¬ Covered G M' (G.u x.1) ∧ ¬ Covered G M' (G.v x.1) then insert x.1 M' else M'

/-- The sequential GD state after the first `t` updates of the tape (`t ≤ T`; later updates are
not applied when `t > T`). -/
def gdState {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool) :
    ℕ → Config m
  | 0 => M0
  | t + 1 => if h : t < T then gdUpdate G (gdState G M0 tape t) (tape ⟨t, h⟩)
      else gdState G M0 tape t

/-- Records of one batch: an initial record per edge of the input matching, and one record per
positive-marked update (update `s = i+1` for the tape index `i`). -/
inductive Record (m T : ℕ) where
  | initial (e : Fin m)
  | update (i : Fin T)
  deriving DecidableEq

instance (m T : ℕ) : Fintype (Record m T) :=
  Fintype.ofEquiv (Fin m ⊕ Fin T)
    { toFun := fun x => match x with | .inl e => .initial e | .inr i => .update i
      invFun := fun r => match r with | .initial e => .inl e | .update i => .inr i
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun r => by cases r <;> rfl }

namespace Record

variable {m T : ℕ}

def edge (tape : Fin T → Fin m × Bool) : Record m T → Fin m
  | initial e => e
  | update i => (tape i).1

/-- Start of the interval: `0` for an initial record, `s = i+1` for update `i`. -/
def start : Record m T → ℕ
  | initial _ => 0
  | update i => i.val + 1

/-- End `d` of the interval `[start, d)`: the next update time of the same edge strictly after the
start, or `T + 1` if there is none. -/
def finish (tape : Fin T → Fin m × Bool) (r : Record m T) : ℕ :=
  let later := (Finset.univ.filter fun j : Fin T =>
    (tape j).1 = r.edge tape ∧ r.start < j.val + 1).image fun j => j.val + 1
  if h : later.Nonempty then later.min' h else T + 1

/-- The interval `[start, finish)` contains time `t`. -/
def Live (tape : Fin T → Fin m × Bool) (r : Record m T) (t : ℕ) : Prop :=
  r.start ≤ t ∧ t < r.finish tape

end Record

/-- The records that exist: initial records of edges in `M0`, and positive-marked updates. -/
def records {m T : ℕ} (M0 : Config m) (tape : Fin T → Fin m × Bool) : Finset (Record m T) :=
  Finset.univ.filter fun r => match r with
    | .initial e => e ∈ M0
    | .update i => (tape i).2 = true

/-- Two records conflict: distinct records whose edges share an endpoint and whose intervals
overlap. -/
def Conflict {n m T : ℕ} (G : Input n m) (tape : Fin T → Fin m × Bool)
    (r q : Record m T) : Prop :=
  r ≠ q ∧ ShareEndpoint G (r.edge tape) (q.edge tape) ∧
    r.start < q.finish tape ∧ q.start < r.finish tape

/-- Peeling state: accepted records and still-active records. -/
structure PeelState (m T : ℕ) where
  accepted : Finset (Record m T)
  active : Finset (Record m T)

def IsInitial {m T : ℕ} : Record m T → Prop
  | .initial _ => True
  | .update _ => False

/-- The initial step: accept every initial record and reject the noninitial records that
conflict with one of them. -/
def peelStart {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool) :
    PeelState m T :=
  let init := (records M0 tape).filter fun r => IsInitial r
  ⟨init, ((records M0 tape).filter fun r => ¬ IsInitial r).filter
      fun r => ¬ ∃ q ∈ init, Conflict G tape r q⟩

/-- Ready records: active records with no earlier active conflicting record. -/
def ready {n m T : ℕ} (G : Input n m) (tape : Fin T → Fin m × Bool) (s : PeelState m T) :
    Finset (Record m T) :=
  s.active.filter fun r => ¬ ∃ q ∈ s.active, Conflict G tape q r ∧ q.start < r.start

/-- One peeling round: accept every ready record, reject every other active record conflicting
with a ready one, and remove all records decided in the round. -/
def peelRound {n m T : ℕ} (G : Input n m) (tape : Fin T → Fin m × Bool) (s : PeelState m T) :
    PeelState m T :=
  let rd := ready G tape s
  ⟨s.accepted ∪ rd,
   s.active \ (rd ∪ s.active.filter fun r => ∃ q ∈ rd, Conflict G tape r q)⟩

/-- The state after `k` peeling rounds. -/
def peelAfter {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool)
    (k : ℕ) : PeelState m T :=
  (peelRound G tape)^[k] (peelStart G M0 tape)

/-- The number `R` of peeling rounds after the initial step: the number of `k` at which records
are still active. Every round with active records decides the earliest one, so at most
`|records|` rounds occur and the count over `k ≤ |records|` is exact. -/
def peelRounds {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool) : ℕ :=
  ((Finset.range ((records M0 tape).card + 1)).filter
    fun k => (peelAfter G M0 tape k).active.Nonempty).card

/-- The accepted records once peeling has terminated. -/
def finalAccepted {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool) :
    Finset (Record m T) :=
  (peelAfter G M0 tape ((records M0 tape).card + 1)).accepted

/-- Edges of accepted records whose intervals contain `t`. -/
def peelState {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool)
    (t : ℕ) : Config m :=
  ((finalAccepted G M0 tape).filter fun r => r.Live tape t).image (Record.edge tape)

/-- The output of one batch: the accepted edges live at time `T`. -/
def peelOutput {n m T : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin T → Fin m × Bool) :
    Config m :=
  peelState G M0 tape T

/-- The batch algorithm on `N` updates: consecutive batches of at most `m` updates, each passing
its output matching to the next. -/
def batchOutput {n m N : ℕ} (G : Input n m) (M0 : Config m) (tape : Fin N → Fin m × Bool) :
    Config m :=
  (List.toChunks m (List.ofFn tape)).foldl (fun M c => peelOutput G M c.get) M0

end

end MatchingNearLinear.Glauber.Supplement


