-- Prove2me | Definitions.Def_WhittEfficiency_IS_Model
-- name    : WhittEfficiency_IS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:07.699597+00:00
-- url     : https://prove2.me/theorems/3cb7b39b-7b69-4d32-95f6-ecbc4574e87f
-- title:
--   §2.3–2.5, pp. 711–713 — infinite-server model: busy count N(t), Poisson arrivals with i.i.d. class labels, class counts
-- statement:
--   This file sets up the **infinite-server (IS) model** of Whitt (1992, §2.3–§2.5): every customer begins service immediately upon arrival, so the only state is which customers are still in service.
--
--   **Arrivals.** Let $T_0, T_1, T_2, \dots$ be the interarrival times and let $\tau_n = T_0 + \cdots + T_{n-1}$ be the $n$-th arrival epoch (the published definition `QueueingFundamentals.Foundations.ArrivalProcess`). Customers are numbered $k = 0, 1, 2, \dots$; customer $k$ arrives at $\tau_{k+1}$.
--
--   **Busy servers.** If customer $k$ has service time $D_k$, it occupies a server at time $t$ exactly when
--   $$\tau_{k+1} \le t < \tau_{k+1} + D_k,$$
--   i.e. an arrival at time $t$ is counted and a departure at time $t$ is not (the convention of the proof of Proposition 2.3, p. 712). The number of busy servers is
--   $$N(t) = \#\{k \ge 0 : \tau_{k+1} \le t < \tau_{k+1} + D_k\}.$$
--
--   **Poisson arrivals with a finite service-time law.** Fix $m \ge 1$ classes, probabilities $p_1,\dots,p_m$ and service times $d_1,\dots,d_m$. The model `IsMarkedPoisson` asserts:
--   1. the interarrival times are i.i.d. exponential with rate $\lambda$ (a Poisson arrival process of rate $\lambda$);
--   2. each customer $k$ carries a class label $J_k \in \{1,\dots,m\}$; the labels are measurable, mutually independent, and $P(J_k = i) = p_i$ for every $k$ and $i$;
--   3. the label sequence $(J_k)$ is independent of the interarrival sequence $(T_k)$.
--
--   A class-$i$ customer has service time $d_i$, so service times are i.i.d., independent of the arrival process, and equal $d_i$ with probability $p_i$ — the paper's "each service time assumes the values $d_i$ with probability $p_i$" (§2.5, p. 713). Using labels rather than raw values keeps classes with equal $d_i$ distinct.
--
--   **Class counts.** The class-$i$ busy count is $N_i(t) = \#\{k : J_k = i,\ \tau_{k+1} \le t < \tau_{k+1} + d_i\}$, and the class-$i$ arrivals in a window $(a, b]$ are counted by $A_i(a,b] = \#\{k : J_k = i,\ a < \tau_{k+1} \le b\}$.
--
--   These objects carry the M/D/∞ and M/G/∞ results of §2.4–§2.5.
--
--   **Formalization Note** Classes are indexed by `Fin m` (the paper's $1 \le i \le n$). Counts use `Set.ncard`, which returns $0$ on an infinite set; under exponential interarrival times infinitely many arrivals in a bounded window is a null event. The independence of labels and arrivals (item 3) is the standard meaning of "service times i.i.d. and independent of the arrival process" in an IS model, which the page presupposes rather than states.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), pp. 711–713, §2.3 (IS model), §2.4 (proof of Prop. 2.3, window convention), §2.5 (service-time law)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- The number of busy servers `N(t)` at time `t` in an infinite-server (IS) model
(Whitt 1992, §2.3, p. 711). Customers are numbered `k = 0, 1, 2, …`; customer `k` arrives at the
`(k+1)`-st arrival epoch `arrivalTime T (k+1) = T 0 + ⋯ + T k`, enters service at once (there are
infinitely many servers) and has service time `D k ω`. It is present at `t` iff
`arrivalTime T (k+1) ω ≤ t < arrivalTime T (k+1) ω + D k ω`: an arrival at time `t` is counted, a
departure at time `t` is not (proof of Proposition 2.3, p. 712). If infinitely many customers are
present, `Set.ncard` returns `0`; under exponential interarrival times this is a null event. -/
noncomputable def busyCount {Ω : Type*} (T : ℕ → Ω → ℝ) (D : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | arrivalTime T (k + 1) ω ≤ t ∧ t < arrivalTime T (k + 1) ω + D k ω}.ncard

/-- Poisson arrivals with i.i.d. class labels (§2.5, p. 713). The interarrival times `T` are
i.i.d. exponential with rate `lam` (a Poisson arrival process of rate `lam`). Customer `k`
carries a class label `J k ∈ Fin m`; the labels are measurable, mutually independent, each equal
to `i` with probability `p i`, and the whole label sequence is independent of the whole
interarrival sequence. A customer of class `i` has service time `d i`, so the service times are
i.i.d., independent of the arrivals, and take the value `d i` with probability `p i`. -/
structure IsMarkedPoisson {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (lam : ℝ)
    (T : ℕ → Ω → ℝ) {m : ℕ} (p : Fin m → ℝ) (J : ℕ → Ω → Fin m) : Prop where
  arrivals : IsExpInterarrivals μ lam T
  label_measurable : ∀ k, Measurable (J k)
  label_indep : iIndepFun J μ
  label_law : ∀ k i, μ.real {ω | J k ω = i} = p i
  indep : IndepFun (fun ω k => T k ω) (fun ω k => J k ω) μ

/-- The number of busy servers of class `i` at time `t`: customers `k` with label `J k ω = i`
that are present at `t`, i.e. `arrivalTime T (k+1) ω ≤ t < arrivalTime T (k+1) ω + d i`. -/
noncomputable def classBusyCount {Ω : Type*} {m : ℕ} (T : ℕ → Ω → ℝ) (J : ℕ → Ω → Fin m)
    (d : Fin m → ℝ) (i : Fin m) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | J k ω = i ∧ arrivalTime T (k + 1) ω ≤ t ∧ t < arrivalTime T (k + 1) ω + d i}.ncard

/-- The number of class-`i` arrivals in the window `(a, b]`: customers `k` with label
`J k ω = i` and `a < arrivalTime T (k+1) ω ≤ b`. -/
noncomputable def classWindowCount {Ω : Type*} {m : ℕ} (T : ℕ → Ω → ℝ) (J : ℕ → Ω → Fin m)
    (i : Fin m) (a b : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | J k ω = i ∧ a < arrivalTime T (k + 1) ω ∧ arrivalTime T (k + 1) ω ≤ b}.ncard

end WhittEfficiency.IS


