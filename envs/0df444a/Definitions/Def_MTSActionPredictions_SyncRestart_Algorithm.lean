-- Prove2me | Definitions.Def_MTSActionPredictions_SyncRestart_Algorithm
-- name    : MTSActionPredictions_SyncRestart_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:57:50.790644+00:00
-- url     : https://prove2.me/theorems/2b41acb5-4825-424b-bcbe-b001e2e175d2
-- title:
--   Algorithm 1: operational synchronization and independent restart law
-- statement:
--   Algorithm 1 starts at $x$, draws one uniform offset $s\in\{0,\ldots,H-1\}$, and runs the supplied causal rule. On request $t$ it serves at $A_t$, pays movement from its previous post-step state and service there, and, when $t\bmod H=s$, moves to $P_t$ and restarts. The boundary move pays distance only. The state stores its restart origin, local task history, seed index, service state, post-step state, and the actual accumulated running and synchronization charges.
--
--   $$C_{\rm total}=C_{\rm Alg}+C_{\rm sync},\qquad E_s=\sum_{1\le t\le T,\ t\bmod H=s}d(P_t,O_t).$$
--
--   For each finite horizon, independent seeds with the arbitrary base law supply all restarts; the offset is independent of these seeds. A separate product factor allows independently random predictions. Offline trajectories may depend on the entire outcome. There is no synchronization at time zero, and terminal boundaries are charged even when their predictions have infinite service cost. These operational definitions are reusable independently of the promised competitive bound.
--
--   Differences from the source:
--   - encoding: nonnegative extended service costs, movement distances, and expectations → ENNReal tasks, metric edist, and nonnegative extended integrals; reason: the same costs and infinities are retained, without conversion to real numbers
--   - encoding: requests indexed from 1 through T and trajectories starting at time 0 → a finite task list with entry i at time i+1 and trajectories on natural times; reason: only the first T+1 states are used, so every finite horizon including zero is represented
--   - encoding: a positive block length and uniform random offset, with the base algorithm restarted → H at least 1, a uniform law on Fin H, and an independent finite product of arbitrary base-seed laws; reason: H=0 has no uniform offset; at horizon T at most T+1 seeds suffice, and the seed law need not have finite support
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Algorithm 1, PDF p. 7 / printed p. 6; §3 (4)–(5), PDF p. 8 / printed p. 7; Remark 7, PDF pp. 8–9 / printed pp. 7–8

import Definitions.Def_MTSActionPredictions_SyncRestart_Model

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart

/-- The operational state of Algorithm 1, not a package of cost guarantees. -/
structure RunState (M : Type*) where
  anchor : M
  history : List (Task M)
  seedIndex : ℕ
  service : M
  post : M
  costAlg : ℝ≥0∞
  costSync : ℝ≥0∞

/-- Serve first; the optional move to P serves no request. There is no time-zero
synchronization. Index n+1 is charged even when it is the terminal time. -/
noncomputable def run {Ω M : Type*} [MetricSpace M] (A : Rule Ω M)
    (tape : ℕ → Ω) (x : M) (q : List (Task M)) (P : ℕ → M) (H s : ℕ) :
    ℕ → RunState M
  | 0 => ⟨x, [], 0, x, x, 0, 0⟩
  | n + 1 =>
    let st := run A tape x q P H s n
    let c := q.getD n (fun _ => 0)
    let hist := st.history ++ [c]
    let a := A (tape st.seedIndex) st.anchor hist
    let running := st.costAlg + edist st.post a + c a
    if (n + 1) % H = s then
      ⟨P (n + 1), [], n + 1, a, P (n + 1), running,
        st.costSync + edist a (P (n + 1))⟩
    else
      ⟨st.anchor, hist, st.seedIndex, a, a, running, st.costSync⟩

noncomputable def syncError {M : Type*} [MetricSpace M]
    (T H s : ℕ) (P O : ℕ → M) : ℝ≥0∞ :=
  ∑ i : Fin T, if (i.val + 1) % H = s then
    edist (P (i.val + 1)) (O (i.val + 1)) else 0

/-- At horizon T at most T+1 fresh seeds are needed. Unused coordinates do not
restrict the randomness. The extension agrees with coordinate n for n ≤ T. -/
abbrev Tape (Ω : Type*) (T : ℕ) := Fin (T + 1) → Ω

def expandTape {Ω : Type*} (T : ℕ) (ω : Tape Ω T) (n : ℕ) : Ω :=
  ω ⟨n % (T + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def tapeLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) : Measure (Tape Ω T) :=
  Measure.pi (fun _ => μ)

/-- The same independent base law is used at each restart. -/
noncomputable def runningCost {Ω M : Type*} [MetricSpace M] (A : Rule Ω M)
    (x : M) (q : List (Task M)) (P : ℕ → M) (H s : ℕ)
    (ω : Tape Ω q.length) : ℝ≥0∞ :=
  (run A (expandTape q.length ω) x q P H s q.length).costAlg

noncomputable def totalCost {Ω M : Type*} [MetricSpace M] (A : Rule Ω M)
    (x : M) (q : List (Task M)) (P : ℕ → M) (H s : ℕ)
    (ω : Tape Ω q.length) : ℝ≥0∞ :=
  let st := run A (expandTape q.length ω) x q P H s q.length
  st.costAlg + st.costSync

/-- Exactly uniform on Fin H for H≥1; independent of the fresh seed tape. -/
noncomputable def offsetLaw (H : ℕ) : Measure (Fin H) :=
  (H : ℝ≥0∞)⁻¹ • Measure.count

noncomputable def privateLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℕ) :
    Measure (Fin H × Tape Ω T) :=
  (offsetLaw H).prod (tapeLaw μ T)

/-- An independent prediction seed may have any probability law. OFF is allowed
to see this seed AND the entire private outcome (offset and base seeds). -/
noncomputable def jointLaw {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ν : Measure Z) (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℕ) :
    Measure (Z × (Fin H × Tape Ω T)) :=
  ν.prod (privateLaw μ H T)

end MTSActionPredictions.SyncRestart


