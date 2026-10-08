-- Prove2me | Definitions.Def_MartingaleHT_FiniteWaiting_Model
-- name    : MartingaleHT_FiniteWaiting_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:14.905259+00:00
-- url     : https://prove2.me/theorems/e8efd624-9eae-43d5-bf27-7bf1143a3aa3
-- title:
--   The $M/M/n/m_n+M$ queue via Poisson time changes with lost arrivals, its scaled martingales (102), the scaled loss process (117) and the filtration (118)
-- statement:
--   This module defines the $n$-th queue of the many-server sequence of Pang, Talreja and Whitt (2007), §1.2 and §7.2, together with the processes its martingale representation is written in.
--
--   **The model** (§1.2, p. 197). There are $n$ servers and a waiting room of size $m_n \in \{0,1,2,\dots\}$, so at most $n+m_n$ customers are in the system. Customers arrive as a Poisson process of rate $\lambda_n>0$; an arrival that finds the system full is lost (blocked). Service times are exponential with rate $\mu>0$, service is first come, first served, and each waiting customer abandons at rate $\theta\ge 0$.
--
--   **Construction** ((113)–(114), pp. 251–252). On a probability space $(\Omega,\mathcal F,P)$ let $A$, $S$, $R$ be rate-1 Poisson processes, and let $Q_n(0)$ be a random variable, with $A$, $S$, $R$, $Q_n(0)$ mutually independent. The number in system $Q_n$ is a process with values in $\{0,1,\dots\}$ such that
--
--   1. every path of $Q_n$ is right-continuous with left limits on $[0,\infty)$ and every $Q_n(t)$ is a random variable;
--   2. $Q_n(t)\le n+m_n$ for every $t\ge 0$;
--   3. almost surely, for every $t\ge 0$,
--   $$
--   Q_n(t)=Q_n(0)+A(\lambda_n t)-S\Big(\mu\int_0^t (Q_n(s)\wedge n)\,ds\Big)-R\Big(\theta\int_0^t (Q_n(s)-n)^+\,ds\Big)-U_n(t),
--   $$
--   where $U_n(t)$ is the number of arrivals in $(0,t]$ that find the system full:
--   $$
--   U_n(t)=\int_{(0,t]} \mathbf 1\{Q_n(s-)=n+m_n\}\,dA(\lambda_n s).
--   $$
--
--   **Scaled processes** ((102), (117), pp. 247–248, 252). With $X_n(t)=(Q_n(t)-n)/\sqrt n$,
--   $$
--   M_{n,1}(t)=\frac{A(\lambda_n t)-\lambda_n t}{\sqrt n},\quad
--   M_{n,2}(t)=\frac{S(\mu B_n(t))-\mu B_n(t)}{\sqrt n},\quad
--   M_{n,3}(t)=\frac{R(\theta W_n(t))-\theta W_n(t)}{\sqrt n},\quad
--   V_n(t)=\frac{U_n(t)}{\sqrt n},
--   $$
--   with busy-server time $B_n(t)=\int_0^t (Q_n(s)\wedge n)\,ds$ and waiting time $W_n(t)=\int_0^t (Q_n(s)-n)^+\,ds$.
--
--   **Filtration** ((118)). $\mathcal F_{n,t}=\sigma\big(Q_n(0),\,A(\lambda_n s),\,S(\mu B_n(s)),\,R(\theta W_n(s)) : 0\le s\le t\big)$.
--
--   **Predictable quadratic variation.** A process $M$ is a square-integrable martingale with predictable quadratic variation $V$ with respect to a filtration $\mathbb F$ if $M$ is an $\mathbb F$-martingale with $E[M(t)^2]<\infty$, $V$ is $\mathbb F$-adapted with continuous, nondecreasing, nonnegative paths, and $M^2-V$ is an $\mathbb F$-martingale.
--
--   These objects are the prelimit side of Theorem 1.2 and of the martingale representation in Theorem 7.4.
--
--   **Formalization Note** (114) as printed integrates $\mathbf 1\{Q_n(s)=n+m_n\}$; with right-continuous paths that would also count the arrival that takes the last free place. The definition uses the left limit $Q_n(s-)$, the paper's own convention for such integrals (p. 204, after (13)). $U_n$ is the Lebesgue–Stieltjes measure, for the arrival clock $s\mapsto A(\lambda_n s)$, of the set $\{s\in(0,t]: Q_n(s-)=n+m_n\}$; if the clock is not monotone (impossible for a Poisson process) the value is $0$. The rates' positivity is part of the structure. The σ-algebras of (118) are augmented, as on the page, by the measurable $P$-null sets (the space is not assumed complete, so only measurable null sets can be added); without the augmentation the time-changed clocks need not be adapted, because (113) holds only almost surely. The paper's "predictable" means left-continuous (p. 208); for the quadratic variations here this is continuity. Martingales are indexed by $\mathbb R_{\ge 0}$; time of the paths is real and every condition is imposed for $t\ge 0$. The Poisson processes are `ManyServerQED.Scheduling.IsPoissonProcess`, and path regularity is `BellWilliams2001.ThresholdPolicy.IsCadlag`.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 197, §1.2 (model); pp. 247–248, (102); pp. 251–252, (113)–(114), (117)–(119)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_Queue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MartingaleHT.FiniteWaiting

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling

/-!
Pang, Talreja & Whitt (2007), §1.2 (p. 197) and §7.2 (pp. 251–252): the `n`-th
`M/M/n/mₙ + M` queue (`n` servers, a waiting room of size `mₙ`, Poisson arrivals, exponential
service and patience), built from three unit-rate Poisson processes by the random time changes
(113)–(114); the scaled martingales (102), the scaled blocking process (117), the filtration
(118), and the predictable-quadratic-variation property used in (119).

Conventions. Time is real and every condition quantifies over `t ≥ 0` (as in
`BellWilliams2001.ThresholdPolicy.Paths`). Martingales are indexed by `ℝ≥0`, as Mathlib's
`Martingale` requires; a process `M : Ω → ℝ → ℝ` enters as `fun (t : ℝ≥0) ω => M ω t`.
-/

/-- The arrival clock `s ↦ A(λ s)` of (113), frozen at its value `A(0)` for `s < 0`. For a
Poisson process `A` (so `A(0) = 0`) and `λ ≥ 0` it is nondecreasing and right-continuous on
all of `ℝ`, and its Lebesgue–Stieltjes measure has no atom at `0`. -/
noncomputable def arrivalClock {Ω : Type*} (lam : ℝ) (A : Ω → ℝ → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun s => A ω (lam * max s 0)

/-- **The number of blocked arrivals** `Uₙ(t)` of (113)–(114): the number of arrivals in
`(0, t]` that find the system full, i.e. the Lebesgue–Stieltjes integral
`Uₙ(t) = ∫_{(0,t]} 1{Qₙ(s−) = n + mₙ} dA(λₙ s)`. The left limit `Qₙ(s−)` is the state an
arrival at time `s` sees (the paper's convention for thinning integrals, p. 204, after (13));
(114) as printed has `Qₙ(s)`, which would also count the arrival that takes the last free place.
When the arrival clock is not monotone (never the case for a Poisson process and `λ ≥ 0`) the
value is `0`. -/
noncomputable def blocked {Ω : Type*} (n m : ℕ) (lam : ℝ) (A : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (ω : Ω) (t : ℝ) : ℝ :=
  open Classical in
  if h : Monotone (arrivalClock lam A ω) then
    (h.stieltjesFunction.measure
      {s | s ∈ Set.Ioc (0 : ℝ) t ∧
        Function.leftLim (fun r => (Q ω r : ℝ)) s = ((n + m : ℕ) : ℝ)}).toReal
  else 0

/-- Cumulative busy-server time `∫₀ᵗ (Qₙ(s) ∧ n) ds`. -/
noncomputable def busyTime {Ω : Type*} (n : ℕ) (Q : Ω → ℝ → ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, min (Q ω s : ℝ) (n : ℝ)

/-- Cumulative waiting-customer time `∫₀ᵗ (Qₙ(s) − n)⁺ ds`. -/
noncomputable def waitTime {Ω : Type*} (n : ℕ) (Q : Ω → ℝ → ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, max ((Q ω s : ℝ) - n) 0

/-- **The `n`-th `M/M/n/mₙ + M` system** (§1.2, p. 197; (113)–(114), pp. 251–252). On
`(Ω, P)`, `Q : Ω → ℝ → ℕ` is the number of customers in a queue with `n` servers, a waiting
room of size `m` (capacity `n + m`), arrival rate `λ > 0`, service rate `µ > 0` per server and
abandonment rate `θ ≥ 0` per waiting customer, built from three unit-rate Poisson processes
`A` (arrivals), `S` (services) and `R` (abandonments):
* `P` is a probability measure; `A`, `S`, `R` are Poisson processes of rate `1`;
* `A`, `S`, `R` (their paths on `t ≥ 0`) and the initial value `Q(0)` are mutually independent;
* every path of `Q` is right-continuous with left limits on `[0, ∞)`, every `Q(t)` is a random
  variable, and the integrands below are integrable on every `[0, t]`;
* the state never exceeds the capacity: `Q(t) ≤ n + m` for all `t ≥ 0` (including `t = 0`);
* almost surely, for every `t ≥ 0`, (113) holds:
  `Q(t) = Q(0) + A(λt) − S(µ ∫₀ᵗ (Q(s) ∧ n) ds) − R(θ ∫₀ᵗ (Q(s) − n)⁺ ds) − U(t)`,
  with `U = blocked n m λ A Q` the arrivals that find the system full. -/
structure IsFiniteWaitingSystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n m : ℕ)
    (lam μ θ : ℝ) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ) : Prop where
  lam_pos : 0 < lam
  mu_pos : 0 < μ
  theta_nonneg : 0 ≤ θ
  isProb : IsProbabilityMeasure P
  poisson_A : IsPoissonProcess P A 1
  poisson_S : IsPoissonProcess P S 1
  poisson_R : IsPoissonProcess P R 1
  indep : iIndepFun (![fun ω (t : ℝ≥0) => A ω t, fun ω (t : ℝ≥0) => S ω t,
    fun ω (t : ℝ≥0) => R ω t, fun ω (_ : ℝ≥0) => (Q ω 0 : ℝ)] : Fin 4 → Ω → ℝ≥0 → ℝ) P
  cadlag : ∀ ω, IsCadlag (fun t => (Q ω t : ℝ))
  meas : ∀ t, Measurable (fun ω => Q ω t)
  integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntervalIntegrable (fun s => min ((Q ω s : ℝ)) (n : ℝ)) volume 0 t ∧
    IntervalIntegrable (fun s => max ((Q ω s : ℝ) - n) 0) volume 0 t
  capacity : ∀ ω (t : ℝ), 0 ≤ t → Q ω t ≤ n + m
  eqn : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (Q ω t : ℝ) = (Q ω 0 : ℝ) + A ω (lam * t)
      - S ω (μ * busyTime n Q ω t)
      - R ω (θ * waitTime n Q ω t)
      - blocked n m lam A Q ω t

/-- The scaled arrival martingale `Mₙ,₁(t) = n^{−1/2}[A(λₙ t) − λₙ t]` of (102). -/
noncomputable def scaledMart1 {Ω : Type*} (n : ℕ) (lam : ℝ) (A : Ω → ℝ → ℝ) (ω : Ω)
    (t : ℝ) : ℝ :=
  (A ω (lam * t) - lam * t) / Real.sqrt n

/-- The scaled service martingale
`Mₙ,₂(t) = n^{−1/2}[S(µ ∫₀ᵗ (Qₙ(s) ∧ n) ds) − µ ∫₀ᵗ (Qₙ(s) ∧ n) ds]` of (102). -/
noncomputable def scaledMart2 {Ω : Type*} (n : ℕ) (μ : ℝ) (S : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (ω : Ω) (t : ℝ) : ℝ :=
  (S ω (μ * busyTime n Q ω t) - μ * busyTime n Q ω t) / Real.sqrt n

/-- The scaled abandonment martingale
`Mₙ,₃(t) = n^{−1/2}[R(θ ∫₀ᵗ (Qₙ(s) − n)⁺ ds) − θ ∫₀ᵗ (Qₙ(s) − n)⁺ ds]` of (102). -/
noncomputable def scaledMart3 {Ω : Type*} (n : ℕ) (θ : ℝ) (R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (ω : Ω) (t : ℝ) : ℝ :=
  (R ω (θ * waitTime n Q ω t) - θ * waitTime n Q ω t) / Real.sqrt n

/-- The scaled blocking process `Vₙ(t) = Uₙ(t)/√n` of (117). -/
noncomputable def scaledBlocked {Ω : Type*} (n m : ℕ) (lam : ℝ) (A : Ω → ℝ → ℝ)
    (Q : Ω → ℝ → ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  blocked n m lam A Q ω t / Real.sqrt n

/-- The σ-algebra `ℱₙ,ₜ` of (118), augmented by the `P`-null sets:
`σ(Qₙ(0), A(λₙ s), S(µ ∫₀ˢ (Qₙ(u) ∧ n) du), R(θ ∫₀ˢ (Qₙ(u) − n)⁺ du) : 0 ≤ s ≤ t)` joined with
the σ-algebra generated by the measurable sets of `P`-measure `0`. The augmentation matters:
(113) holds only almost surely, so `Qₙ(s)`, `s ≤ t`, is a function of the generators only off a
null set. -/
noncomputable def genSigma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (lam μ θ : ℝ) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (Q ω 0 : ℝ)) inferInstance ⊔
  MeasurableSpace.comap (fun ω (s : Set.Iic t) => A ω (lam * (s : ℝ))) inferInstance ⊔
  MeasurableSpace.comap (fun ω (s : Set.Iic t) => S ω (μ * busyTime n Q ω s)) inferInstance ⊔
  MeasurableSpace.comap (fun ω (s : Set.Iic t) => R ω (θ * waitTime n Q ω s)) inferInstance ⊔
  MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ P N = 0}

/-- `M` is a **square-integrable martingale with predictable quadratic variation `V`** with
respect to the filtration `ℱ` (the paper's `⟨M⟩ = V`, p. 208 and (119)): `M` is an
`ℱ`-martingale with `E[M(t)²] < ∞` for every `t`; `V` is `ℱ`-adapted with continuous (hence,
in the paper's sense, predictable), nondecreasing, nonnegative paths; and `M² − V` is an
`ℱ`-martingale. Continuity of `V` together with the martingale property of `M² − V` identifies
`V` as the compensator of `M²` (Doob–Meyer uniqueness). -/
def HasPQV {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (M V : ℝ≥0 → Ω → ℝ) : Prop :=
  Martingale M ℱ P ∧ (∀ t, MemLp (M t) 2 P) ∧
  Adapted ℱ V ∧ (∀ ω, Continuous (fun t => V t ω)) ∧ (∀ ω, Monotone (fun t => V t ω)) ∧
  (∀ t ω, 0 ≤ V t ω) ∧
  Martingale (fun t ω => M t ω ^ 2 - V t ω) ℱ P

end MartingaleHT.FiniteWaiting


