-- Prove2me | Definitions.Def_BramsonQueueing_Instability_LuKumarRun
-- name    : BramsonQueueing_Instability_LuKumarRun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:40.230952+00:00
-- url     : https://prove2.me/theorems/90f271b2-69bd-4d4b-a636-c98039683df1
-- title:
--   Queueing trajectories, immediate workload, hitting time, and instability
-- statement:
--   For any finite initial vector $z_0\in\mathbb N^4$, let $Z_k(t)$ be the queue length and $C_k(t)$ the number of completed class-$k$ visits during $(0,t]$. Class arrivals $B$ are $B_1=A$, $B_2=C_1$, $B_3=C_2$, $B_4=C_3$. Cumulative allocated service $T_k$ is the time integral of the preemptive service rule. A run satisfies queue conservation and the renewal-clock equations on one almost-sure event:
--   $$Z_k(t)+C_k(t)=z_{0,k}+B_k(t),\qquad S_k(C_k(t))\le T_k(t)<S_k(C_k(t)+1),$$
--   where $S_k(n)=\sum_{i<n}V_{k,i}$. Counts start at zero, completion counts are nondecreasing, and the jointly measurable integer-valued paths are right-continuous. Queue capacity is unbounded and time is real.
--
--   The immediate station workload sums $S_k(z_{0,k}+B_k(t))-T_k(t)$ over its classes, exactly the convention of (4.44). In particular, a class-2 completion adds the next class-3 requirement even though both classes use station 2. Network departures are $D=C_4$. The hitting time is $\tau_0=\inf\{t\ge0:Z_2(t)=0\text{ or }Z_4(t)=0\}$, with an empty infimum equal to infinity. Instability means positive probability that the total queue length tends to infinity from some finite initial state. No separation, rate bound, finite hitting time, or escape property is included in the run's defining assumptions.
--
--   **Formalization Note** The service-clock representation enumerates successive class visits, including initially present jobs, with independent exponential requirements. The scalar busy-time integrands take values zero or one and are measurable on every bounded interval, hence integrable. Counts use natural numbers; conservation uses addition to avoid truncated subtraction. Hitting times use nonnegative extended reals. Negative-time queue values play no role.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Section 3.1, printed 53–58 / PDF 61–66; immediate workload equation (4.44), printed 102 / PDF 110

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarPrimitives

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Unbounded integer-valued queues and class-completion counts on continuous time. -/
structure QueueingPaths (Ω : Type*) where
  Z : ℝ → Ω → Fin 4 → ℕ
  C : Fin 4 → ℝ → Ω → ℕ

/-- Cumulative class arrivals along the deterministic route, excluding initial jobs. -/
def classArrivals {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    (p : LuKumarPrimitives Ω d) (r : QueueingPaths Ω) (k : Fin 4) (t : ℝ) (ω : Ω) : ℕ :=
  if k = 0 then p.A t ω else if k = 1 then r.C 0 t ω
  else if k = 2 then r.C 1 t ω else r.C 2 t ω

/-- Cumulative allocated service. Preemption retains the accumulated service. -/
noncomputable def allocatedTime {Ω : Type*} (r : QueueingPaths Ω)
    (k : Fin 4) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, serviceRate (r.Z s ω) k

/-- Queue conservation and renewal service clocks define the run, independently of
any instability, separation, hitting-time or departure-rate assertion. -/
structure LuKumarRun {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    (p : LuKumarPrimitives Ω d) (z₀ : Fin 4 → ℕ) extends QueueingPaths Ω where
  queue_measurable : Measurable (fun x : ℝ × Ω => Z x.1 x.2)
  completion_measurable : ∀ k, Measurable (fun x : ℝ × Ω => C k x.1 x.2)
  dynamics : ∀ᵐ ω, (∀ k, C k 0 ω = 0) ∧
    (∀ k, MonotoneOn (fun t => C k t ω) (Set.Ici 0)) ∧
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t) ∧
    (∀ (k : Fin 4) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => C k s ω) (Set.Ici t) t) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ k,
      Z t ω k + C k t ω = z₀ k + classArrivals p toQueueingPaths k t ω) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ k,
      serviceSum p k (C k t ω) ω ≤ allocatedTime toQueueingPaths k t ω ∧
      allocatedTime toQueueingPaths k t ω < serviceSum p k (C k t ω + 1) ω)

/-- Immediate workload: current class requirements minus work already performed,
as in (4.44). A class-2 completion creates a new class-3 requirement. -/
noncomputable def workload {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    {p : LuKumarPrimitives Ω d} {z₀ : Fin 4 → ℕ}
    (r : LuKumarRun p z₀) (j : Fin 2) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin 4, if d.p k = j then
    serviceSum p k (z₀ k + classArrivals p r.toQueueingPaths k t ω) ω -
      allocatedTime r.toQueueingPaths k t ω else 0

/-- First time either high-priority queue is empty; the empty infimum is infinity. -/
noncomputable def tauZero {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    {p : LuKumarPrimitives Ω d} {z₀ : Fin 4 → ℕ}
    (r : LuKumarRun p z₀) (ω : Ω) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ t : ℝ, 0 ≤ t ∧ s = ENNReal.ofReal t ∧
    (r.Z t ω 1 = 0 ∨ r.Z t ω 3 = 0)}

/-- Departures from the network are class-4 completions over (0,t]. -/
def departures {Ω : Type*} (r : QueueingPaths Ω) (t : ℝ) (ω : Ω) : ℕ :=
  r.C 3 t ω

/-- The source's instability notion: escape with positive probability from some
finite queue-length initial state, for the process family on a fixed probability space. -/
def IsUnstable {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    {p : LuKumarPrimitives Ω d} (runs : ∀ z₀ : Fin 4 → ℕ, LuKumarRun p z₀) : Prop :=
  ∃ z₀ : Fin 4 → ℕ, 0 < ℙ {ω | Tendsto
    (fun t : ℝ => ∑ k : Fin 4, ((runs z₀).Z t ω k : ℝ)) atTop atTop}

end BramsonQueueing.Instability


