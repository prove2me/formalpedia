-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_Supplement_adapter
-- name    : NearlyOptimalPPR_Computation_Supplement_adapter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:45:28.422001+00:00
-- url     : https://prove2.me/theorems/92f069ad-1ad2-4c9f-a8ac-50712648339a
-- title:
--   Algorithm 5 adapter, operation tags, and episode snapshots
-- statement:
--   Let $G$ be the published finite simple undirected adjacency-list input, $s$ a seed, $\varepsilon$ the real accuracy parameter, and $b$ an integer block. Put
--   $$q=\varepsilon/96,\qquad N=96/\varepsilon,\qquad \mu(x,H,r)=\sum_{v\in H}r_v.$$
--   The nonisolated execution is exactly the published recursive transition at depth zero with schedule $[b]$. The isolated branch emits the single entry $(s,1)$ and halts with constant work. Operation tags identify an actual exterior push, episode opening, full or cache solve, ordinary pruned return, component completion, or a control transition by the transition's own guards. Episode endpoints record the actual drained starting state and an actual post-operation state; they do not contain assumed invariants.
--
--   These adapters expose Section 3's existing algorithm for the supplemental results without introducing another graph or solver model. The file includes only structural proofs of the threshold identity and the nonisolated adapter identity.
--
--   Differences from the source:
--   - encoding: Algorithm 5 with idealized exact FullSolve and CacheSolve operations → finite iteration of the published depth-zero recursive transition with threshold epsilon/96 and fixed schedule [b], plus the isolated-source wrapper and an erasing ledger; reason: root_threshold and coreRun_nonisolated prove the threshold and routine identities, run_core proves ledger erasure, and the theorem establishes that a legal block is not clamped
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Algorithms 2–5, p. 10–11 (printed = PDF); canonical source.pdf, sha256 17a68253bbd187a44704374a465f62c34c8d7628c44b48c160e903ed3300bdb4; parameter conventions pp.5–6; episode budget p.9; published Algorithms 6–9 at depth zero

import Definitions.Def_NearlyOptimalPPR_Computation_recursive

set_option autoImplicit false

open Finset Matrix

noncomputable section

namespace NearlyOptimalPPR.Computation.Supplement

attribute [local instance] Classical.propDecidable

/-- Section 3, pp.5--6. These are real parameters, not integer accuracy scales. -/
def threshold (ε : ℝ) : ℝ := ε / 96

def scale (ε : ℝ) : ℝ := 96 / ε

def activeMass {n : ℕ} (st : RecursiveState n) : ℝ :=
  ∑ v ∈ (st.frames 0).active, (st.frames 0).residual v

/-- Algorithm 5 line 1 precedes the nonisolated routine. The isolated branch
emits one explicit entry and is charged constant work. -/
def initialCore {n : ℕ} (g : InputGraph n) (s : Fin n) (ε : ℝ) (b : ℕ) :
    RecursiveState n :=
  let st := recursiveInit g s (threshold ε) 0 [b]
  if g.graph.degree s = 0 then
    { st with
      done := true
      output := [((s.val : ℤ), 1)]
      work := 3
      charged := fun id => if id = 0 then 3 else 0 }
  else st

/-- Algorithm 5 uses the published depth-zero transition, including prioritized
component completion. Fixed scheduling covers every legal block, not just the
balanced schedule. Control-only transitions refine the pseudocode into steps. -/
def coreRun {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b t : ℕ) : RecursiveState n :=
  (recursiveStep m g s α 0 [b])^[t] (initialCore g s ε b)

/-- Structural adapter identity: erasing the isolated-source wrapper gives the
existing routine. No equivalence assumption is imposed on a theorem. -/
theorem coreRun_nonisolated {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b t : ℕ) (hs : g.graph.degree s ≠ 0) :
    coreRun m g s α ε b t = recursiveRun m g s α (threshold ε) 0 [b] t := by
  simp [coreRun, initialCore, recursiveRun, hs]

theorem root_threshold (ε : ℝ) : rootThreshold ε 0 = threshold ε := by
  norm_num [rootThreshold, kappa, threshold]

/-- Tags for operations actually selected by recursiveStep at depth zero.
These tags carry no correctness, termination, or work invariant. -/
inductive Event (n : ℕ) where
  | control
  | openEpisode
  | push (v : Fin n)
  | fullSolve
  | cacheSolve (C : Finset (Fin n))
  | ordinaryReturn
  | completion
  deriving DecidableEq

def queuedPush {n : ℕ} (st : RecursiveState n) : Event n :=
  if anyExhausted st then .control else
    match pendingPush st with
    | some (_, v) => .push v
    | none => .control

/-- The guards are the published transition's guards. A singular or unavailable
solve is a charged control step, never a successful solve event. -/
def event {n : ℕ} (g : InputGraph n) (st : RecursiveState n) : Event n :=
  if st.done then .control else
  if componentComplete st then .completion else
  let f := st.frames st.top
  match f.pc with
  | .initialDrain =>
      if ancestorExhausted st then .control else
      if (pendingPush st).isSome then queuedPush st else .control
  | .beginEpisode => .openEpisode
  | .fullSolve =>
      if anyExhausted st then .control else
      if f.active ⊆ st.stored ∧ ∀ v ∈ f.active, 0 < g.graph.degree v then
        .fullSolve else .control
  | .leafDrain =>
      if anyExhausted st then .control else
      if (pendingPush st).isSome then queuedPush st else
      if f.high = ∅ then .control else
      let C := f.cache ∪ f.high
      if C ⊆ st.stored ∧ ∀ v ∈ C, 0 < g.graph.degree v then
        .cacheSolve C else .control
  | .afterChild =>
      if ancestorExhausted st ∨ exhausted st st.top then .control else queuedPush st
  | .restartDrain =>
      if ancestorExhausted st then .control else
      if (pendingPush st).isSome then queuedPush st else .control
  | .normal => .ordinaryReturn
  | _ => .control

/-- Actual pre/post records of operations during an episode, including its
opening, closing, and any update crossing Q. This is a proof-only snapshot. -/
structure EpisodeEndpoint (n : ℕ) where
  start : RecursiveState n
  stop : RecursiveState n

/-- An ordinary pruned return excludes isolated and component-completion returns. -/
def ordinary {n : ℕ} (g : InputGraph n) (st : RecursiveState n) : Prop :=
  event g st = .ordinaryReturn

end NearlyOptimalPPR.Computation.Supplement


