-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_model
-- name    : NonuniformCompetitive_Snoopy_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:46:59.892229+00:00
-- url     : https://prove2.me/theorems/39965a34-25bf-4439-97d0-63a77ef85e06
-- title:
--   The single-block snoopy-caching task system, on-line algorithms and the off-line optimum
-- statement:
--   Fix $n$ processors, each with a cache, and one memory block $B$ whose transfer over the bus costs $p$ bus cycles (the block holds $p-1$ variables).
--
--   **States.** The block is either *shared* between all caches, or *private* to the cache of one processor $i \in \{0,\dots,n-1\}$.
--
--   **Requests.** A request is a read $\mathrm{R}_i$ or a write $\mathrm{W}_i$ from processor $i$.
--
--   **Costs.** Moving from a private state to any other state costs $p$; moving from the shared state to any state is free, and staying put is free. A read $\mathrm{R}_i$ served in state $s$ costs $0$ if $s$ is shared or private to $i$, and $+\infty$ otherwise. A write $\mathrm{W}_i$ costs $0$ in $i$'s private state, $1$ in the shared state, and $+\infty$ otherwise.
--
--   **Serving a request.** Before request $j$ the system is in state $s_{j-1}$ (its state after request $j-1$; $s_0$ is the initial state). At the moment of the request it is in a state $m_j$, performs the task there, and immediately after the request moves to $s_j$. The cost of the request is
--   $$d(s_{j-1}, m_j) + \mathrm{task}(r_j, m_j) + d(m_j, s_j).$$
--   Reads are look-ahead-one requests: $m_j$ may differ from $s_{j-1}$. Writes are look-ahead-zero requests: no state change is allowed at the moment of a write, so $m_j = s_{j-1}$.
--
--   **Admissible sequences.** Every write is preceded by a read to the same block: a write $\mathrm{W}_i$ is never the first request, and the request just before it is $\mathrm{R}_i$ or $\mathrm{W}_i$.
--
--   **Off-line optimum.** $C_{opt}(s_0, \sigma)$ is the infimum, over all schedules $(m_j, s_j)$ starting in $s_0$ that obey the look-ahead-zero rule, of the total cost on $\sigma$, taken in $[0, +\infty]$.
--
--   **On-line algorithms.** A deterministic on-line algorithm is given by two functions of the request prefix seen so far: the state at the moment of the last request of the prefix, and the state after it (the state after the empty prefix is the initial state). At a write, the state at the moment of the request must equal the state after the previous prefix. Its cost $C_A(\sigma)$ on $\sigma$ is the sum of the request costs above.
--
--   This is the task system of §3.1 (p. 550), with the move conventions of §2 (p. 545). A multi-block system decomposes into independent single-block problems (p. 551).
--
--   **Formalization Note** States are `Option (Fin n)` (`none` = shared). Costs are in `ℝ≥0∞`, where $+\infty$ is a genuine infeasible outcome. Moves "immediately before" a request are made without knowledge of it, so they are recorded as moves immediately after the previous request. The paper states admissibility as "every write is preceded by a read to the same block"; the form here (the request just before a write of $i$ is a read or write of $i$) is the one used by the proof of Theorem 4 (write runs, p. 551; phases, p. 552). On admissible sequences the off-line optimum is finite: the schedule that moves to the shared state at the first request (a read) and stays there costs at most $p$ plus the number of writes.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 545 (§2, moves before/at/after a request, look-ahead-zero requests) and p. 550 (§3.1, the snoopy-caching task system)

import Mathlib

namespace NonuniformCompetitive.Snoopy

open scoped ENNReal

/-- A state of the single-block snoopy-caching task system (Karlin et al. 1994, §3.1, p. 550)
with `n` processors: `none` means the block `B` is shared between all caches, `some i` means
`B` is private to processor `i`'s cache. -/
abbrev State (n : ℕ) : Type := Option (Fin n)

/-- A request for the block `B`: a read or a write from processor `i`. -/
inductive Req (n : ℕ) : Type where
  | read (i : Fin n)
  | write (i : Fin n)
  deriving DecidableEq

/-- `true` exactly on write requests (the look-ahead-zero requests of §2, p. 545). -/
def Req.isWrite {n : ℕ} : Req n → Bool
  | .read _ => false
  | .write _ => true

/-- State-transition cost (p. 550): `p` for going from a private state to any other state,
`0` from the shared state to any state, and `0` for staying put. -/
noncomputable def transCost {n : ℕ} (p : ℕ) (s s' : State n) : ℝ≥0∞ :=
  if s' = s then 0 else
    match s with
    | none => 0
    | some _ => (p : ℝ≥0∞)

/-- Task cost of a request served in state `s` (p. 550). A read from `i` costs `0` if `B` is
shared or private to `i`, and `∞` otherwise. A write from `i` costs `0` in `i`'s private state,
`1` in the shared state, and `∞` otherwise. -/
noncomputable def taskCost {n : ℕ} : Req n → State n → ℝ≥0∞
  | .read i, s => if s = none ∨ s = some i then 0 else ⊤
  | .write i, s => if s = some i then 0 else if s = none then 1 else ⊤

/-- Cost of serving one request `r` (§2, p. 545): the system is in `prev` (its state after the
previous request, including all moves made immediately after it), moves to `mom` at the moment
of the request, performs the task in `mom`, and moves to `aft` immediately after the request. -/
noncomputable def stepCost {n : ℕ} (p : ℕ) (r : Req n) (prev mom aft : State n) : ℝ≥0∞ :=
  transCost p prev mom + taskCost r mom + transCost p mom aft

/-- Admissible request sequences: "every write is preceded by a read to the same block"
(p. 550), in the form the proof of Theorem 4 uses (write runs, p. 551; phases "consist of a
read followed by up to `p` writes", p. 552): a write from processor `i` is never the first
request, and the request immediately before it is a read or a write from the same processor
`i`. (`j - 1` is only evaluated for `0 < j`.) -/
def Admissible {n : ℕ} (σ : List (Req n)) : Prop :=
  ∀ (j : ℕ) (i : Fin n), σ[j]? = some (Req.write i) →
    0 < j ∧ (σ[j - 1]? = some (Req.read i) ∨ σ[j - 1]? = some (Req.write i))

/-- The cost of the schedule `(m, s)` on the request sequence `σ`: `s 0` is the initial state,
and for the request `σ[j]` (0-based) the system is in `s j`, is in `m (j + 1)` at the moment of
the request and in `s (j + 1)` after it. -/
noncomputable def scheduleCost {n : ℕ} (p : ℕ) (σ : List (Req n)) (m s : ℕ → State n) : ℝ≥0∞ :=
  ∑ j : Fin σ.length, stepCost p σ[j] (s j) (m (j + 1)) (s (j + 1))

/-- The look-ahead-zero rule (p. 545): no state change at the moment of a write, so the state
at the moment of a write is the state after the previous request. -/
def RespectsWrites {n : ℕ} (σ : List (Req n)) (m s : ℕ → State n) : Prop :=
  ∀ j : Fin σ.length, σ[j].isWrite = true → m (j + 1) = s j

/-- The optimal off-line cost from the initial state `s₀` (the algorithm `opt` of §2): the
infimum of `scheduleCost` over all schedules starting in `s₀` that respect the look-ahead-zero
rule. The infimum is taken in `ℝ≥0∞`. On admissible sequences it is finite: the schedule that
moves to the shared state at the first request (a read) and stays there costs at most
`p + σ.length`. -/
noncomputable def offlineCost {n : ℕ} (p : ℕ) (s₀ : State n) (σ : List (Req n)) : ℝ≥0∞ :=
  ⨅ (m : ℕ → State n) (s : ℕ → State n) (_ : s 0 = s₀) (_ : RespectsWrites σ m s),
    scheduleCost p σ m s

/-- A deterministic on-line snoopy-caching algorithm. It sees only the requests so far:
`moment l` is the state at the moment of the last request of the nonempty prefix `l`, and
`after l` the state after all moves following the last request of `l`; `after []` is the initial
state (the value `moment []` is never used). Moves "immediately before" a request are made
without knowledge of it, so they are part of `after` of the previous prefix. At a write
(look-ahead-zero) no move is permitted at the moment of the request. -/
structure OnlineAlgorithm (n : ℕ) : Type where
  moment : List (Req n) → State n
  after : List (Req n) → State n
  lookaheadZero : ∀ (l : List (Req n)) (i : Fin n), moment (l ++ [Req.write i]) = after l

/-- The cost of the on-line algorithm `A` on `σ`: the sum over the requests of `stepCost`, with
the state before request `j` equal to `after (σ.take j)`, the state at its moment
`moment (σ.take (j+1))` and the state after it `after (σ.take (j+1))`. -/
noncomputable def OnlineAlgorithm.cost {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ)
    (σ : List (Req n)) : ℝ≥0∞ :=
  ∑ j : Fin σ.length,
    stepCost p σ[j] (A.after (σ.take j)) (A.moment (σ.take (j + 1))) (A.after (σ.take (j + 1)))

end NonuniformCompetitive.Snoopy


