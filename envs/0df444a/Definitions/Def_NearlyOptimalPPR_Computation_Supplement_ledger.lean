-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_Supplement_ledger
-- name    : NearlyOptimalPPR_Computation_Supplement_ledger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:46:44.431543+00:00
-- url     : https://prove2.me/theorems/debf26b4-5a20-46b9-adba-ebdba4753080
-- title:
--   Operational query trace and finite-prefix accounts
-- statement:
--   For the same input and block, the decorated run iterates the published transition while recording the operations that it executes. A degree lookup queries only an unanswered degree. The first exterior access to a row asks its indexed neighbor queries, stores the returned list, and queries degrees at newly touched endpoints; repeated exterior scans and all joint solves read stored lists. The trace contains the actual queries and their answers in execution order, rather than inferring queries from a set of stored vertices.
--
--   The ledger records exterior scan lengths, $S=\sum d_vt$, incremental charges to open episode budgets, entered-episode snapshots, and cache solves with or without a new admission. Its work is
--   $$\mathcal W_t=\mathcal W_t^{\rm core}+|\mathcal Q_t|.$$
--   Every oracle call has its own unit charge, in addition to the core's arithmetic, heap, assembly, propagation, solver, completion and sparse-output charges. Traces, snapshots and analytical counters are erased ghost data. The structural erasure lemma proves that they never change a core transition.
--
--   Total work is $+\infty$ for a nonterminating run and otherwise the extended nonnegative supremum of prefix work. Expected work is the nonnegative integral over the published coin-tape probability measure of this deterministic work. This interface supports finite-prefix analysis without assuming termination or the desired bounds.
--
--   Differences from the source:
--   - encoding: Algorithm 5 with idealized exact FullSolve and CacheSolve operations → finite iteration of the published depth-zero recursive transition with threshold epsilon/96 and fixed schedule [b], plus the isolated-source wrapper and an erasing ledger; reason: root_threshold and coreRun_nonisolated prove the threshold and routine identities, run_core proves ledger erasure, and the theorem establishes that a legal block is not clamped
--   - encoding: valid finite execution prefixes and episodes → prefixes obtained only by iterating the operational transition, with recorded episode-entry and post-operation snapshots; reason: no residual, cache-size, termination or cost invariant is assumed; crossing updates and the current partial episode are retained
--   - encoding: exact idealized SDDM work charged in expectation → nonnegative extended work is infinity on nontermination, with a measurable constant tape-work function and its nonnegative integral equal to total charged work; reason: the published exact primitive uses deterministic charges, so their expectation is the same charge; every oracle call is additionally charged and core arithmetic, heaps, solves, completion and explicit output are retained
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Algorithms 2–5 and §3.4, p. 9–11 (printed = PDF); canonical source.pdf, sha256 17a68253bbd187a44704374a465f62c34c8d7628c44b48c160e903ed3300bdb4

import Definitions.Def_NearlyOptimalPPR_Computation_Supplement_adapter

set_option autoImplicit false

open Finset Matrix
open scoped ENNReal

noncomputable section

namespace NearlyOptimalPPR.Computation.Supplement

attribute [local instance] Classical.propDecidable

inductive Query (n : ℕ) where
  | degree (v : Fin n)
  | neighbor (v : Fin n) (index : ℕ)

inductive Answer (n : ℕ) where
  | degree (value : ℕ)
  | neighbor (value : Option (Fin n))

/-- Memoized oracle answers. trace is a ghost log of executed queries, not a
set of vertices from which a query count is inferred. -/
structure Access (n : ℕ) where
  degrees : Fin n → Option ℕ
  rows : Fin n → Option (List (Fin n))
  trace : List (Query n × Answer n)

def emptyAccess (n : ℕ) : Access n := ⟨fun _ => none, fun _ => none, []⟩

/-- First degree lookup executes an oracle call; subsequent lookups read memory. -/
def readDegree {n : ℕ} (g : InputGraph n) (v : Fin n) (a : Access n) : Access n :=
  match a.degrees v with
  | some _ => a
  | none =>
      let d := (g.neighbors v).length
      { a with
        degrees := Function.update a.degrees v (some d)
        trace := a.trace ++ [(.degree v, .degree d)] }

/-- Only an exterior push invokes this acquisition. Each list entry is obtained
by a neighbor query indexed below the previously queried degree. -/
def acquireRow {n : ℕ} (g : InputGraph n) (v : Fin n) (a : Access n) : Access n :=
  match a.rows v with
  | some _ => a
  | none =>
      let a := readDegree g v a
      let indices := List.range ((a.degrees v).getD 0)
      let row := indices.filterMap (fun i => (g.neighbors v)[i]?)
      { a with
        rows := Function.update a.rows v (some row)
        trace := a.trace ++ indices.map (fun i =>
          (.neighbor v i, .neighbor ((g.neighbors v)[i]?))) }

def touchDegrees {n : ℕ} (g : InputGraph n) (vertices : List (Fin n))
    (a : Access n) : Access n :=
  vertices.foldl (fun a v => readDegree g v a) a

/-- Joint solves inspect stored lists, never acquire new ones. Missing rows are
not silently fetched: reachability must prove that the required lists exist. -/
def scanStored {n : ℕ} (g : InputGraph n) (T : Finset (Fin n)) (a : Access n) : Access n :=
  T.toList.foldl (fun a v => touchDegrees g (v :: (a.rows v).getD []) a) a

def accessEvent {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (a : Access n) : Access n :=
  match event g st with
  | .push v =>
      let a := acquireRow g v a
      touchDegrees g (v :: (a.rows v).getD []) a
  | .fullSolve | .completion => scanStored g (st.frames 0).active a
  | .cacheSolve C => scanStored g C a
  | _ => a

/-- This ledger decorates, but never chooses or changes, a published transition.
Snapshots, traces and analytical counters are ghost data; their storage is not
part of the algorithm. The degree and row memo tables describe actual memory. -/
structure Ledger (n : ℕ) where
  core : RecursiveState n
  access : Access n
  scans : ℕ
  pushMass : ℝ
  episodeCharges : ℝ
  cacheCalls : ℕ
  admittingCalls : ℕ
  repeatCalls : ℕ
  snapshot : Option (RecursiveState n)
  endpoints : List (EpisodeEndpoint n)

def init {n : ℕ} (g : InputGraph n) (s : Fin n) (ε : ℝ) (b : ℕ) : Ledger n :=
  ⟨initialCore g s ε b, readDegree g s (emptyAccess n), 0, 0, 0, 0, 0, 0, none, []⟩

def step {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (b : ℕ) (l : Ledger n) : Ledger n :=
  let st := l.core
  let f := st.frames 0
  let ev := event g st
  let next := recursiveStep m g s α 0 [b] st
  let a := accessEvent g st l.access
  let snap := if ev = .openEpisode then some st else l.snapshot
  let endpoints :=
    if f.openBudget = true ∨ ev = .openEpisode then
      match snap with
      | some entry => l.endpoints ++ [⟨entry, next⟩]
      | none => l.endpoints
    else l.endpoints
  let (scan, mass) := match ev with
    | .push v =>
        let d := ((a.degrees v).getD 0 : ℝ)
        let h := min (f.residual v / (5 * d)) (3 * f.q / 8 - st.x v)
        (((a.rows v).getD []).length, d * h)
    | _ => (0, 0)
  let charge := if f.openBudget = true then (next.frames 0).W - f.W else 0
  let (calls, admits, repeats) := match ev with
    | .cacheSolve C =>
        if C = f.cache then (1, 0, 1) else (1, 1, 0)
    | _ => (0, 0, 0)
  { core := next
    access := a
    scans := l.scans + scan
    pushMass := l.pushMass + mass
    episodeCharges := l.episodeCharges + charge
    cacheCalls := l.cacheCalls + calls
    admittingCalls := l.admittingCalls + admits
    repeatCalls := l.repeatCalls + repeats
    snapshot := snap
    endpoints := endpoints }

/-- Finite iteration is the sole reachability condition. -/
def run {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b t : ℕ) : Ledger n :=
  (step m g s α b)^[t] (init g s ε b)

/-- Erasure commutes with iteration; the ledger never alters an algorithm step. -/
theorem run_core {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b t : ℕ) :
    (run m g s α ε b t).core = coreRun m g s α ε b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [run, coreRun, Function.iterate_succ_apply'] at *
      change recursiveStep m g s α 0 [b] (((step m g s α b)^[t] (init g s ε b)).core) = _
      rw [ih]

/-- Every query is additionally charged one unit. All arithmetic, heap, scan,
assembly, exact-solve, completion and output charges of the core are retained. -/
def chargedWork {n : ℕ} (l : Ledger n) : ℝ≥0∞ :=
  l.core.work + (l.access.trace.length : ℝ≥0∞)

/-- No nontermination is converted into a zero integral or a finite cost. -/
def totalWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b : ℕ) : ℝ≥0∞ :=
  if ∃ t, (run m g s α ε b t).core.done = true then
    ⨆ t, chargedWork (run m g s α ε b t)
  else ⊤

/-- In the stipulated exact primitive model the charges are deterministic.
The random tape is unused, so this really is their expectation. -/
def tapeWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b : ℕ) (_ω : ℕ → Bool) : ℝ≥0∞ := totalWork m g s α ε b

def expectedWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, tapeWork m g s α ε b ω ∂LocalPush.coinTape

end NearlyOptimalPPR.Computation.Supplement


