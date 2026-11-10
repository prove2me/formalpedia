-- Prove2me | Definitions.Def_AdaptiveRefresh_Main_RefreshProcess
-- name    : AdaptiveRefresh_Main_RefreshProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:02:42.179824+00:00
-- url     : https://prove2.me/theorems/d2d60f5d-52b4-4ee4-836c-22f740372abc
-- title:
--   Algorithms 1–4 and their analytical microsteps
-- statement:
--   For an initial unweighted identified multigraph with $m$ edges and initial maximum degree $\Delta$, the sampling rate is
--
--   $$p=\min\{1,10^4\Delta^{-1}\eta^{-2}\log^2m\}.$$
--
--   The analytical context is the source's connected nontrivial component, $0<\eta<1/2$, and $0<p<1$. The algorithm starts with an empty transient graph and empty sample, samples each initial identity, and immediately performs repairs. Counters initially vanish. Maximum estimated counters at least $8\Delta$ have priority over degree errors exceeding $\eta\Delta/2$. Ties use the first eligible vertex in the labelled order. A contraction resets the refreshed counter, draws one uniform incident identity to increase the estimated counter at its other endpoint by the current degree, removes sampled incident identities, and queues all live incident identities for fresh independent sampling with weight $1/p$. True counters reset at the refreshed vertex and increase by parallel multiplicities elsewhere. They are analysis variables. Setting the comparison switch to exact instead uses these true counters to trigger Algorithm 4.
--
--   A deletion removes one live identity, mandatorily refreshes its first recorded endpoint, then repairs. A measurable strategy selects deletions from completed-output histories and all past draws. Illegal messages stop the input game. Each analytical transition samples one edge or contracts one vertex, with stationary padding after the input game ends. The analytical adjacency error is against the transient graph, not the complete input graph during a partial refresh. Variance adds $1/p$ at both endpoints of a sample and resets its refreshed diagonal entry at a contraction. The counter error is
--
--   $$E'=\operatorname{diag}(a'-\widehat a).$$
--
--   Refresh counts increase at the contraction that starts a refresh; the pending queue records when it finishes. The stopped horizon is the first crossing of $44\Delta\log m$, completion of the first $2m+3$ refreshes, or termination. No bounds on counters, variance, refresh count or termination are assumed. Analytical steps are not implementation costs; the separate RAM specifies charged execution. The all-size algorithm theorems remain unrestricted by this analysis context, including the exact-storage branch when clipping gives $p=1$ or the graph is empty.
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Algorithms 1–4, printed pp. 6–10 (PDF pp. 7–11); §4.3.3 and stopping argument, printed pp. 11–12 (PDF pp. 12–13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_OnlineMachine

set_option autoImplicit false

namespace AdaptiveRefresh.Main

/-- The source's exact rate, including clipping. Analytical lemmas use its nontrivial branch. -/
noncomputable def samplingRate (η Δ : ℝ) (m : ℕ) : ℝ :=
  min 1 (10 ^ 4 * Δ⁻¹ * η⁻¹ ^ 2 * Real.log m ^ 2)

/-- Connected, nontrivial, unweighted initial graph in the unclipped sampling analysis. -/
noncomputable def SamplingContext (n : ℕ) (G : Graph) (η : ℝ) : Prop :=
  ValidGraph n G ∧ (∀ e ∈ G, e.weight = 1) ∧ 2 ≤ n ∧
  (∀ u v : Fin n, Relation.ReflTransGen (fun a b => 0 < pairWeights n G a b) u v) ∧
  0 < η ∧ η < 1 / 2 ∧ 0 < initialMaxDegree n G ∧
  0 < samplingRate η (initialMaxDegree n G) G.length ∧
  samplingRate η (initialMaxDegree n G) G.length < 1

/-- Incident edge identities, not distinct neighbours. -/
def incident (G : Graph) (u : ℕ) : Graph := G.filter (fun e => e.u = u ∨ e.v = u)

def removeIncident (G : Graph) (u : ℕ) : Graph :=
  G.filter (fun e => e.u ≠ u ∧ e.v ≠ u)

def multiplicity (G : Graph) (u v : ℕ) : ℕ :=
  (G.filter (fun e => (e.u = u ∧ e.v = v) ∨ (e.u = v ∧ e.v = u))).length

/-- Each analytical state distinguishes the delivered graph from the transient graph.
True counters and diagonal variance are analysis variables, never assumed bounded. -/
structure RefreshState (n : ℕ) where
  live : Graph
  transient : Graph := []
  H : Graph := []
  pending : Graph
  estimated : Fin n → ℝ := fun _ => 0
  trueCounter : Fin n → ℝ := fun _ => 0
  variance : Fin n → ℝ := fun _ => 0
  refreshes : ℕ := 0
  counterRepairs : ℕ := 0
  deletions : ℕ := 0
  stopped : Bool := false
  history : History := ([], [], [])

/-- A deterministic tie break: first vertex of maximum counter above the threshold. -/
noncomputable def counterChoice {n : ℕ} (Δ : ℝ) (exact : Bool)
    (s : RefreshState n) : Option (Fin n) := by
  classical
  let a := if exact then s.trueCounter else s.estimated
  exact ((List.finRange n).filter (fun u => 8 * Δ ≤ a u ∧ ∀ v, a v ≤ a u)).head?

noncomputable def degreeChoice {n : ℕ} (η Δ : ℝ) (s : RefreshState n) : Option (Fin n) := by
  classical
  exact ((List.finRange n).filter
    (fun u => η * Δ / 2 < |degree n s.H u - degree n s.live u|)).head?

/-- Completed initialization/deletion states occur precisely when the sampling queue and
both repair queues are empty. -/
noncomputable def Completed {n : ℕ} (η Δ : ℝ) (exact : Bool)
    (s : RefreshState n) : Prop :=
  s.pending = [] ∧ counterChoice Δ exact s = none ∧ degreeChoice η Δ s = none

/-- Uniform incident identity via the half-open partition of [0,1); the endpoint 1 is
sent to the last interval and has probability zero under the uniform law. -/
noncomputable def incidentDraw (E : Graph) (x : ℝ) : Option Edge :=
  E[min (Nat.floor (x * E.length)) (E.length - 1)]?

/-- One contraction. The true counter and variance at u reset; estimated mass goes to
one uniform incident identity's other endpoint. Counter repairs have strict priority. -/
noncomputable def contract {n : ℕ} (u : Fin n) (isCounter exact : Bool)
    (x : ℝ) (s : RefreshState n) : RefreshState n := by
  classical
  let E := incident s.live u.val
  let tc := fun v : Fin n => if v = u then 0 else
    s.trueCounter v + multiplicity s.live u.val v.val
  let ac := Function.update s.estimated u 0
  let ac' := match incidentDraw E x with
    | none => ac
    | some e =>
      let v := if e.u = u.val then e.v else e.u
      fun w : Fin n => ac w + if w.val = v then (E.length : ℝ) else 0
  exact {s with transient := removeIncident s.live u.val, H := removeIncident s.H u.val, pending := E, estimated := (if exact then tc else ac'), trueCounter := tc, variance := Function.update s.variance u 0, refreshes := s.refreshes + 1, counterRepairs := s.counterRepairs + if isCounter then 1 else 0, history := (s.history.1 ++ [u.val], s.history.2.1, s.history.2.2 ++ [x])}

/-- The fast process uses exact=false. exact=true is only the Algorithm 4 comparison.
Every non-padding transition is an edge sample or a contraction. -/
noncomputable def refreshStep (n : ℕ) (G₀ : Graph) (η : ℝ) (t : ℕ)
    (exact : Bool) (S : Strategy) (ω : ℕ → ℝ) (i : ℕ)
    (s : RefreshState n) : RefreshState n := by
  classical
  let Δ := initialMaxDegree n G₀
  let p := samplingRate η Δ G₀.length
  let x := ω i
  exact if s.stopped then s else match s.pending with
  | e :: es =>
    let H := if x < p then s.H ++ [{e with weight := p⁻¹}] else s.H
    {s with transient := s.transient ++ [e], H := H, pending := es, variance := fun v => s.variance v + if v.val = e.u ∨ v.val = e.v then p⁻¹ else 0, history := (s.history.1, s.history.2.1, s.history.2.2 ++ [x])}
  | [] =>
    match counterChoice Δ exact s with
    | some u => contract u true exact x s
    | none => match degreeChoice η Δ s with
      | some u => contract u false exact x s
      | none =>
        if t ≤ s.deletions then {s with stopped := true} else
          let hist : History :=
            (s.history.1 ++ [s.H.length] ++ s.H.flatMap (fun e => [e.id, e.u, e.v]), s.history.2.1 ++ s.H.map Edge.weight, s.history.2.2)
          match S hist with
          | (1 :: id :: [], []) =>
            match s.live.find? (fun e => e.id = id) with
            | none => {s with stopped := true}
            | some e =>
              if hu : e.u < n then
                let s' := {s with live := s.live.filter (fun e => e.id ≠ id), deletions := s.deletions + 1, history := (hist.1 ++ [1, id], hist.2.1, hist.2.2)}
                contract ⟨e.u, hu⟩ false exact x s'
              else {s with stopped := true}
          | _ => {s with stopped := true}

noncomputable def refreshRun (n : ℕ) (G₀ : Graph) (η : ℝ) (t : ℕ)
    (exact : Bool) (S : Strategy) (ω : ℕ → ℝ) : ℕ → RefreshState n
  | 0 => {live := G₀, pending := G₀}
  | i + 1 => refreshStep n G₀ η t exact S ω i (refreshRun n G₀ η t exact S ω i)

/-- Diagonal counter-estimation error and adjacency error against the transient graph. -/
noncomputable def counterError {n : ℕ} (s : RefreshState n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun v => s.trueCounter v - s.estimated v)

noncomputable def adjacencyError {n : ℕ} (s : RefreshState n) : Matrix (Fin n) (Fin n) ℝ :=
  adjacency n s.H - adjacency n s.transient

/-- Before completion of the first 2m+3 refreshes, including its final sampling steps.
The next state after finishing that refresh is excluded. -/
def BeforeRefreshHorizon {n : ℕ} (m : ℕ) (s : RefreshState n) : Prop :=
  s.refreshes < 2 * m + 3 ∨ (s.refreshes = 2 * m + 3 ∧ s.pending ≠ [])

/-- Source stopping index: first true-counter crossing or first completion of
2m+3 refreshes (or algorithm termination). It is not a success assumption. -/
noncomputable def counterStop (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (S : Strategy) (ω : ℕ → ℝ) : ℕ := by
  classical
  exact Nat.findGreatest (fun i =>
    ∀ j < i, let s := refreshRun n G η t false S ω j
      (∀ v, s.trueCounter v ≤ 44 * initialMaxDegree n G * Real.log G.length) ∧
      BeforeRefreshHorizon G.length s ∧ s.stopped = false) (8 * G.length ^ 2)

end AdaptiveRefresh.Main


