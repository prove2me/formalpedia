-- Prove2me | Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Online
-- name    : AvgCompletionSched_BestAlpha_Supplement_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:51:25.414936+00:00
-- url     : https://prove2.me/theorems/142ee3e2-5e64-434b-be83-fa2b1e3a5ce3
-- title:
--   Causal policies, exponential seed law, and insertion-time FIFO
-- statement:
--   One policy $A$ maps every finite input $I$, one shared seed $a$, and a job label to its start time. Two inputs have the same revealed history at time $t$ when they have the same labels, sizes, and release dates for all jobs released by $t$. Causality means that equal histories and the same seed give identical labeled starts through $t$, even if the inputs have different numbers of unrevealed jobs. An entire nonpreemptive execution is fixed by these starts and the revealed processing times.
--
--   The input-independent seed measure has density
--
--   $$f(a)=\frac{e^a}{e-1},\qquad 0<a\le1.$$
--
--   The online total cost is $\sum_j(S_j+p_j)$. The theorem, rather than a premise, asserts that the seed measure is a probability measure, the returned schedule is feasible, and its cost is measurable and integrable. For a simulated preemptive schedule $P$ and its α-order $\pi$, the insertion-time queue has recursion
--
--   $$F_0=0,\qquad F_{k+1}=\max\{F_k,C^P_{\pi(k)}(a)\}+p_{\pi(k)}.$$
--
--   The queue-realization predicate requires the actual event trace, one reservation per job without duplicate labels, equality of enqueue times with simulated α-points, and this exact recursion. These conditions have to be established by the online existence theorem. They do not assume the competitive inequality or efficiency. The published offline α-schedule instead uses $r_{\pi(k)}$ in its recursion, so it is a distinct observable.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, DOI 10.1137/S0097539797327180, pp. 147–148, §1 (online information and oblivious adversary); p. 155, proof of Theorem 2.8

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Events
import Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Objectives

set_option autoImplicit false

namespace AvgCompletionSched.BestAlpha.Supplement

open MeasureTheory

/-- A single policy handles all finite inputs. Its only random seed is one shared alpha. -/
def Policy := (n : ℕ) → Instance n → ℝ → Fin n → ℝ

/-- The processing times and labels of precisely those jobs revealed by time t. -/
def revealed {n : ℕ} (I : Instance n) (t : ℝ) : Set (ℕ × ℝ × ℝ) :=
  {q | ∃ j, q = (j.val, I.p j, I.r j) ∧ I.r j ≤ t}

/-- All starts already committed on or before time t, including their natural job labels. -/
def startsThrough (A : Policy) {n : ℕ} (I : Instance n) (a t : ℝ) : Set (ℕ × ℝ) :=
  {q | ∃ j, q = (j.val, A n I a j) ∧ A n I a j ≤ t}

/-- Causality compares arbitrary different finite future extensions, including different
numbers of unrevealed jobs. Equal histories and equal seeds give equal actions up to t. -/
def Causal (A : Policy) : Prop :=
  ∀ (n m : ℕ) (I : Instance n) (J : Instance m) (a t : ℝ),
    a ∈ Set.Ioc (0 : ℝ) 1 → revealed I t = revealed J t →
      startsThrough A I a t = startsThrough A J a t

/-- The same exponential density is used before every input (oblivious adversary). -/
noncomputable def alphaLaw : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
    (fun a => ENNReal.ofReal (Real.exp a / (Real.exp 1 - 1)))

/-- Unweighted total completion of the policy's returned starts. Feasibility is asserted
in the theorem, not baked into the numeric observable. -/
noncomputable def onlineCost (A : Policy) {n : ℕ} (I : Instance n) (a : ℝ) : ℝ :=
  ∑ j, (A n I a j + I.p j)

/-- Explicit insertion-time FIFO recursion, in the published alpha-order. This is distinct
from the published offline `listFinish`, whose eligibility time is the original release. -/
noncomputable def fifoFinish {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (a : ℝ) (π : Fin n ≃ Fin n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if h : k < n then
      max (P.CPα (π ⟨k, h⟩) a) (fifoFinish P a π k) + I.p (π ⟨k, h⟩)
    else fifoFinish P a π k

/-- The event output is a causal FIFO realization of the actual simulated SRPT schedule.
Uniqueness/existence, alpha-point identity and feasibility are conclusions, not premises. -/
def RealizesQueue (A : Policy) {n : ℕ} (I : Instance n) (a : ℝ)
    (P : PreemptiveSchedule I) : Prop :=
  P.σ = eventService I a ∧
  ((eventRun I a).reservations.map Reservation.job).Nodup ∧
  (∀ j, ∃! z : Reservation n, z ∈ (eventRun I a).reservations ∧ z.job = j) ∧
  (∀ z ∈ (eventRun I a).reservations, z.enqueue = P.CPα z.job a) ∧
  ∀ j, A n I a j + I.p j =
    fifoFinish P a (alphaOrder P a) (((alphaOrder P a).symm j : ℕ) + 1)

end AvgCompletionSched.BestAlpha.Supplement


