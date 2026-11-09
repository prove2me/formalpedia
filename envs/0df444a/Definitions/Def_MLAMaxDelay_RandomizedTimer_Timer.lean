-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer
-- name    : MLAMaxDelay_RandomizedTimer_Timer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:59.408217+00:00
-- url     : https://prove2.me/theorems/b125630e-096b-4d0d-a58e-92750bc2df49
-- title:
--   The event-driven OPT-Timer execution and causal histories
-- statement:
--   Requests with zero root-path cost are served at arrival and removed from the timer input. Fix one real parameter $\theta$ for the whole execution. An arriving complete epoch starts an idle busy block or joins its active block $B$ precisely when its arrival is no later than
--   $$\tau_\theta(B)=\alpha(B)+F(B)-(1-\theta)\kappa(B),$$
--   where $F(B)$ is computed by Algorithm 1 on the revealed block. Otherwise the armed timer first emits the rooted service of $B$ and the arriving epoch starts the next block. After the final observed arrival the already armed timer still fires; no end-of-input signal is used. The finite evaluator records timed batches, converts them to actual rooted services, and merges the zero-path services chronologically, before timer services at ties.
--
--   Revealed histories retain occurrence labels, arrival times and locations. An algorithm is causal when inputs with identical revealed histories through any real time $t$ yield identical service histories through $t$. This property is a conclusion required of OPT-Timer, not an assumption about its traces.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 8, Algorithm 2 and equations (3)–(4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Offline

namespace MLAMaxDelay.RandomizedTimer

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Zero paths are served immediately, not excluded from the input theorem. -/
noncomputable def positiveInput (T : WeightedTree V) (I : Input V) : Input V := by
  classical
  exact restrictInput I (I.requests.filter (fun r => 0 < kappa T I {r}))

noncomputable def zeroServices (T : WeightedTree V) (I : Input V) : Schedule V := by
  classical
  exact (epochs I).map (fun a => (a, footprint T I
    (I.requests.filter (fun r => I.arrival r = a ∧ kappa T I {r} = 0))))

/-- The online implementation calls Algorithm 1 on the revealed busy block.
It does not use the true offline value as an oracle. -/
noncomputable def deadline (T : WeightedTree V) (I : Input V) (θ : ℝ) (B : Finset ℕ) : ℝ :=
  firstArrival I B + (offlineAlgorithm T (restrictInput I B)).value - (1-θ) * kappa T I B

structure TimedBatch where
  batch : Finset ℕ
  time : ℝ

structure TimerState where
  active : Option (Finset ℕ)
  completed : List TimedBatch

/-- One arrival transition. At equality the complete epoch is accepted first. -/
noncomputable def timerStep (T : WeightedTree V) (I : Input V) (θ : ℝ)
    (st : TimerState) (a : ℝ) : TimerState := by
  classical
  let R := I.requests.filter (fun r => I.arrival r = a)
  exact match st.active with
  | none => ⟨some R, st.completed⟩
  | some B =>
    if a ≤ deadline T I θ B then ⟨some (B ∪ R), st.completed⟩
    else ⟨some R, st.completed ++ [⟨B, deadline T I θ B⟩]⟩

/-- Finite evaluation of the arrival/timer process. Finishing emits the already
armed timer even on a continuation with no more arrivals; it sends no termination
message to the algorithm. Causality is asserted, rather than assumed, in the goal. -/
noncomputable def timerBlocks (T : WeightedTree V) (I : Input V) (θ : ℝ) : List TimedBatch :=
  let st := (epochs I).foldl (timerStep T I θ) ⟨none, []⟩
  match st.active with
  | none => st.completed
  | some B => st.completed ++ [⟨B, deadline T I θ B⟩]

noncomputable def timerServices (T : WeightedTree V) (I : Input V) (θ : ℝ) : Schedule V :=
  (timerBlocks T I θ).map (fun b => (b.time, footprint T I b.batch))

/-- Zero services go first at a coincident time (stable mergeSort). Zero epochs
with no zero request are omitted, so idle preprocessing adds no spurious service. -/
noncomputable def optTimer (T : WeightedTree V) (I : Input V) (θ : ℝ) : Schedule V := by
  classical
  let Z := (zeroServices T I).filter (fun s => ∃ r ∈ I.requests,
    I.arrival r = s.1 ∧ kappa T I {r} = 0)
  exact (Z ++ timerServices T (positiveInput T I) θ).mergeSort (fun s t => s.1 ≤ t.1)

/-- Revealed arrival history. Labels preserve simultaneous multiplicities. -/
noncomputable def observed (I : Input V) (t : ℝ) : Finset (ℕ × ℝ × V) := by
  classical
  exact (I.requests.filter (fun r => I.arrival r ≤ t)).image
    (fun r => (r, I.arrival r, I.location r))

noncomputable def serviceHistory (S : Schedule V) (t : ℝ) : Schedule V := by
  classical
  exact S.filter (fun s => s.1 ≤ t)

/-- Prefix agreement for every real time: no future requests, final count, or
end-of-input information can affect the services already performed. -/
def Causal (A : Input V → Schedule V) : Prop :=
  ∀ I J t, observed I t = observed J t →
    serviceHistory (A I) t = serviceHistory (A J) t

end MLAMaxDelay.RandomizedTimer


