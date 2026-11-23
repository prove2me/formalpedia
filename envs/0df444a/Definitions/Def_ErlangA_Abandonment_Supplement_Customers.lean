-- Prove2me | Definitions.Def_ErlangA_Abandonment_Supplement_Customers
-- name    : ErlangA_Abandonment_Supplement_Customers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:50:59.675016+00:00
-- url     : https://prove2.me/theorems/ea692b16-97c1-4159-a044-f3700352d643
-- title:
--   FCFS customer realization and the virtual-wait process
-- statement:
--   Consider an unlimited first-come-first-served queue with $N\ge1$ identical exponential servers and exponential customer patience. External interarrival gaps $E_i$, potential service times $S_i$ and patience times $X_i$ are mutually independent, with respective rates $\lambda,\mu,\theta$, and are independent of the arbitrary finite initial count $K$. Initial callers are represented as an ordered batch at time zero; the first $\min(K,N)$ service marks are residual services and waiting callers' patience marks are residual patience. This uses the exponential model's memorylessness, without imposing stationarity or moments on $K$.
--
--   The published FCFS recursion processes these customers in arrival order, accepting a customer for service exactly when its patience reaches its offered wait. At time $t$, insert a hypothetical infinitely patient customer immediately after all real arrivals at or before $t$. Its offered wait is
--
--   $$\upsilon_N(t)=\text{the time until this hypothetical customer can begin service}.$$
--
--   The same marks are used for all $t$, retaining the joint law of the entire process. Later arrivals cannot advance this customer. The marked realization is linked to the published Erlang-A count process by equality of its arrival count and its total number in service or waiting. It contains no diffusion or stationary convergence assumption.
--
--   **Formalization Note** Only the deterministic FCFS recursion, counting and sorting functions of `DelayDep.Equiv.Model` are reused. Its stochastic `Inputs`/`ExoSystem` predicates are not used: they assume an empty initial queue. The time-zero batch permits every finite initial queue here. Positive, nonexplosive versions hold almost surely under the stated independent exponential inputs. The unused $N=0$ virtual wait and count are set to zero. At an actual arrival the virtual customer is placed just after that arrival, giving the right-continuous version; ties of patience and service are null events.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, pp. 209–210, 216, §1 and §4 (virtual waiting); p. 222, Appendix B

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model
import Definitions.Def_ErlangA_Diffusion_Queue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

namespace ErlangA.Abandonment.Supplement

/-- Initial callers are a batch at time zero, in FCFS order; subsequent gaps are `e`.
For initial busy callers, `s` below means residual service and `p` means residual patience.
Memorylessness allows arbitrary initial counts with these independent exponential residuals. -/
def customerGaps (k : ℕ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < k then 0 else e (i - k)

/-- Insert an infinitely patient hypothetical arrival at time `t`, after every real arrival
at or before `t`. Only the gaps up to its index enter the published FCFS recursion. -/
noncomputable def insertedGaps (a : ℕ → ℝ) (t : ℝ) : ℕ → ℝ :=
  let m := DelayDep.Equiv.nextArr a t
  Function.update a m (t - if m = 0 then 0 else DelayDep.Equiv.kappa a (m - 1))

/-- The actual FCFS virtual wait, computed from the same service and patience marks at every
time, rather than freshly sampling a marginal waiting kernel. The artificial customer's own
marks are never inspected. Zero servers is an unused totalization; the theorem uses `N ≥ 1`. -/
noncomputable def virtualWait (N k : ℕ) (e s p : ℕ → ℝ) (t : ℝ) : ℝ :=
  if h : N = 0 then 0 else
    letI : NeZero N := ⟨h⟩
    let a := customerGaps k e
    DelayDep.Equiv.wait (insertedGaps a t) (fun _ : Fin N => 0) p
      (fun i _ => s i) (DelayDep.Equiv.nextArr a t)

/-- Number in the FCFS system from the same marked customer realization. -/
noncomputable def customerCount (N k : ℕ) (e s p : ℕ → ℝ) (t : ℝ) : ℕ :=
  if h : N = 0 then 0 else
    letI : NeZero N := ⟨h⟩
    let z := DelayDep.Equiv.pathX (customerGaps k e) (fun _ : Fin N => 0) p
      (fun i _ => s i) t.toNNReal
    z.1 + z.2.1

/-- One family expressing mutual independence of the initial count and all arrival, service
and patience marks. The three rows are interarrival times, services, and patience. -/
def primitiveFamily {Ω : Type*} (k : Ω → ℕ) (e s p : ℕ → Ω → ℝ) :
    Option (Fin 3 × ℕ) → Ω → ℝ
  | none => fun ω => (k ω : ℝ)
  | some (j, i) => if j = 0 then e i else if j = 1 then s i else p i

/-- A marked FCFS refinement of the published Erlang-A count process. No invariant law,
moment bound, diffusion convergence or queue/wait approximation is part of this predicate.
`e` lists positive external interarrival gaps. Initial callers enter as an ordered time-zero
batch. The first `min(k,N)` services are residual services. Independence and exponential
memorylessness give exactly the source's initial count model. The a.s. nonexplosion and
positivity clauses specify harmless versions of the independent exponential primitives. -/
structure IsFCFSRealization {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℕ) (lam μ θ : ℝ) (A : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (e s p : ℕ → Ω → ℝ) : Prop where
  measurable_e : ∀ i, Measurable (e i)
  measurable_s : ∀ i, Measurable (s i)
  measurable_p : ∀ i, Measurable (p i)
  exponential_e : ∀ i, P.map (e i) = expMeasure lam
  exponential_s : ∀ i, P.map (s i) = expMeasure μ
  exponential_p : ∀ i, P.map (p i) = expMeasure θ
  independent : iIndepFun (primitiveFamily (fun ω => Q ω 0) e s p) P
  regular : ∀ᵐ ω ∂P,
    (∀ i, 0 < e i ω ∧ 0 < s i ω ∧ 0 < p i ω) ∧
    Tendsto (fun i => DelayDep.Equiv.kappa (fun j => e j ω) i) atTop atTop
  arrivals : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (DelayDep.Equiv.nextArr (customerGaps (Q ω 0) (fun i => e i ω)) t : ℝ) =
      (Q ω 0 : ℝ) + A ω (lam * t)
  count : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    Q ω t = customerCount N (Q ω 0) (fun i => e i ω) (fun i => s i ω)
      (fun i => p i ω) t

/-- The process υ_N on the original probability space, without rescaling. -/
noncomputable def waitProcess {Ω : Type*} (N : ℕ) (Q : Ω → ℝ → ℕ)
    (e s p : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  virtualWait N (Q ω 0) (fun i => e i ω) (fun i => s i ω) (fun i => p i ω) t

end ErlangA.Abandonment.Supplement


