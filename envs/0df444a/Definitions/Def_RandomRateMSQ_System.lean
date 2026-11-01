-- Prove2me | Definitions.Def_RandomRateMSQ_System
-- name    : RandomRateMSQ_System
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:36.267854+00:00
-- url     : https://prove2.me/theorems/b5d70d76-3f43-4833-9bd9-358b183b55c0
-- title:
--   The $n$-th many-server system with random service rates: primitives and system equations
-- statement:
--   The sample-path description of the $n$-th system, which has $n$ servers.
--
--   The primitives are: interarrival times $u_i$ ($i\ge1$), with arrivals $A^n(t)=\sup\{k:\sum_{i\le k}u_i/\lambda_n\le t\}$; the service rates $\tilde\mu^n_k$ of the servers $k=1,\dots,n$, fixed through time; a unit-rate Poisson process $S^n$ (given by its exponential gaps) whose time change $S^n_P(t)=S^n\big((\sum_j\tilde\mu^n_j)t\big)$ produces potential service completions at epochs $\theta^n_i$; uniform marks $U^n_i$ with $\kappa^n_i=\min\{k:(\sum_{j}\tilde\mu^n_j)U^n_i\le\sum_{j\le k}\tilde\mu^n_j\}$; and a unit-rate Poisson process $N^n$ for abandonments. The system processes are the number in system $X^n(t)$, the idleness indicators $I^n_k(t)$ and the routing counts $R^n_k(t)$.
--
--   Completions are $D^n_k(t)=\sum_{i=1}^{S^n_P(t)}(1-I^n_k(\theta^n_i-))\,\mathbf 1\{\kappa^n_i=k\}$ (non-preemptive service). The **system equations** on a path are:
--
--   1. $X^n$, $I^n_k$, $R^n_k$ are càdlàg, and $I^n_k(t)\in\{0,1\}$;
--   2. $I^n_k(t)=I^n_k(0)-R^n_k(t)+D^n_k(t)$;
--   3. $R^n_k$ is a counting process with $R^n_k(0)=0$ and unit jumps, and $(1-I^n_k(t-))\,dR^n_k(t)=0$;
--   4. non-idling (3.1): $(X^n(t)-n)^-=\sum_k I^n_k(t)$;
--   5. $X^n(t)=X^n(0)+A^n(t)-\sum_kD^n_k(t)-N^n\big(\gamma\int_0^t(X^n(s)-n)^+ds\big)$.
--
--   This is the pathwise construction on which every result of the mission rests.
--
--   **Formalization Note** Time is $[0,\infty)$; servers are `Fin n`; families are indexed by $\mathbb N$ and used from $1$. Counts are computed with the public `BellWilliams2001.ThresholdPolicy.renewalCount` in $\mathbb N\cup\{\infty\}$ and converted to $\mathbb N$ (they are finite almost surely). $I(\theta-)$ is the left limit.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, §3, pp.5–6 (system equations, (3.1), construction of D, abandonment process) and p.8 (paths in D)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Definitions.Def_RandomRateMSQ_StandingData

open MeasureTheory ProbabilityTheory Filter Topology
open BellWilliams2001.ThresholdPolicy
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- The **sample-path data of the `n`-th system** (Büke–Qin, arXiv:1905.04198v1, §3, pp.5–6), on a
sample space `Ω`:
1. `u i` (`i ≥ 1`): the interarrival times `uⁿᵢ` (mean `1`); arrivals are at `Σ_{j≤i} u j / λₙ`;
2. `rate k` (`k : Fin n`): the service rate `µ̃ⁿₖ` of server `k`, fixed through time;
3. `e i` (`i ≥ 1`): the interarrival gaps of the unit-rate Poisson process `Sⁿ`, whose `i`-th
   epoch is `Σ_{j≤i} e j`;
4. `U i` (`i ≥ 1`): the uniform(0,1) marks `Uⁿᵢ` that split the potential completions;
5. `b i` (`i ≥ 1`): the interarrival gaps of the unit-rate Poisson process `Nⁿ` (abandonments);
6. `X ω t`: the number `Xⁿ(t)` of customers in the system;
7. `I k ω t`: the idleness indicator `Iⁿₖ(t)` of server `k`;
8. `R k ω t`: the number `Rⁿₖ(t)` of customers routed to server `k` by time `t`.

**Formalization Note.** Time is `ℝ≥0`. Servers are `Fin n` (the paper's `k = 1, …, n`). The
families `u, e, U, b` are indexed by `ℕ` and used from index `1` on, as in the paper's sums
`Σ_{i=1}^{k}`; the value at index `0` is never used. Unit-rate Poisson processes are given by
their i.i.d. exponential(1) gaps (the laws are imposed in `IsModel`). -/
structure System (Ω : Type*) (n : ℕ) where
  u : ℕ → Ω → ℝ
  rate : Fin n → Ω → ℝ≥0
  e : ℕ → Ω → ℝ
  U : ℕ → Ω → ℝ
  b : ℕ → Ω → ℝ
  X : Ω → ℝ≥0 → ℕ
  I : Fin n → Ω → ℝ≥0 → ℕ
  R : Fin n → Ω → ℝ≥0 → ℕ

namespace System

variable {Ω : Type*} {n : ℕ} (s : System Ω n)

/-- The arrival process `Aⁿ(t) = sup{k : Σ_{i=1}^{k} uⁿᵢ/λₙ ≤ t}` (arXiv:1905.04198v1, p.5), the
renewal count of public `BellWilliams2001.ThresholdPolicy.renewalCount` (computed in `ℕ∞`).

**Formalization Note.** The count is converted to `ℕ` with `ENat.toNat`, which is `0` at `⊤`. The
count is finite for every `t` almost surely (the gaps have mean `1 > 0`), so the conversion only
changes a null set of paths. -/
noncomputable def arrivals (lam : ℝ) (ω : Ω) (t : ℝ≥0) : ℕ :=
  (renewalCount (fun k => partialSum (fun i => s.u i ω) k / lam) (t : ℝ)).toNat

/-- The total service rate `Σ_{j=1}^{n} µ̃ⁿⱼ`. -/
noncomputable def totalRate (ω : Ω) : ℝ := ∑ k, (s.rate k ω : ℝ)

/-- The unit-rate Poisson process `Sⁿ(r) = sup{i : Σ_{j≤i} e j ≤ r}` in its own clock `r`
(arXiv:1905.04198v1, p.6: "{Sⁿ(t), t ≥ 0} to be Poisson processes with rate 1"); `ℕ` via
`ENat.toNat` as in `arrivals`. -/
noncomputable def unitCount (ω : Ω) (r : ℝ) : ℕ :=
  (renewalCount (partialSum (fun i => s.e i ω)) r).toNat

/-- The potential service completion process `Sⁿ_P(t) = Sⁿ((Σⱼ µ̃ⁿⱼ) t)` (arXiv:1905.04198v1,
p.6). -/
noncomputable def potential (ω : Ω) (t : ℝ≥0) : ℕ := s.unitCount ω (s.totalRate ω * t)

/-- The `i`-th epoch `θⁿᵢ` of `Sⁿ_P`: the `i`-th epoch of `Sⁿ` divided by `Σⱼ µ̃ⁿⱼ`
(arXiv:1905.04198v1, p.6). -/
noncomputable def epoch (ω : Ω) (i : ℕ) : ℝ≥0 :=
  Real.toNNReal (partialSum (fun j => s.e j ω) i / s.totalRate ω)

/-- `κⁿᵢ = k`, where `κⁿᵢ := min{k : (Σ_{j=1}^{n} µ̃ⁿⱼ) Uⁿᵢ ≤ Σ_{j=1}^{k} µ̃ⁿⱼ}`
(arXiv:1905.04198v1, p.6): server `k` satisfies the inequality and no server of smaller index
does. -/
def IsMark (ω : Ω) (i : ℕ) (k : Fin n) : Prop :=
  s.totalRate ω * s.U i ω ≤ ∑ j ∈ Finset.univ.filter (· ≤ k), (s.rate j ω : ℝ) ∧
    ∀ j : Fin n, j < k →
      ¬ (s.totalRate ω * s.U i ω ≤ ∑ l ∈ Finset.univ.filter (· ≤ j), (s.rate l ω : ℝ))

/-- The service completion process of server `k` (arXiv:1905.04198v1, p.6):
`Dⁿₖ(t) = Σ_{i=1}^{Sⁿ_P(t)} (1 − Iⁿₖ(θⁿᵢ−)) δₖ(κⁿᵢ)`: a potential completion at `θⁿᵢ` marked `k`
is an actual completion iff server `k` is busy just before it (non-preemptive service).

**Formalization Note.** `Iⁿₖ(θ−)` is `Function.leftLim`; `1 − I` is truncated subtraction in `ℕ`,
exact because `I ≤ 1` in the model. -/
noncomputable def departures (k : Fin n) (ω : Ω) (t : ℝ≥0) : ℕ := by
  classical exact
    ∑ i ∈ Finset.Icc 1 (s.potential ω t),
      if s.IsMark ω i k then 1 - Function.leftLim (s.I k ω) (s.epoch ω i) else 0

/-- The unit-rate Poisson process `Nⁿ(r)` of abandonments in its own clock (arXiv:1905.04198v1,
p.6), from its gaps `b`; `ℕ` via `ENat.toNat` as in `arrivals`. -/
noncomputable def abandonClock (ω : Ω) (r : ℝ) : ℕ :=
  (renewalCount (partialSum (fun i => s.b i ω)) r).toNat

/-- `∫₀ᵗ (Xⁿ(s) − n)⁺ ds`, the cumulative queue length. -/
noncomputable def cumOverflow (ω : Ω) (t : ℝ≥0) : ℝ :=
  cumInt (fun r => max ((s.X ω r : ℝ) - n) 0) t

/-- The abandonment process `Nⁿ(γ ∫₀ᵗ (Xⁿ(s) − n)⁺ ds)` (arXiv:1905.04198v1, p.6). -/
noncomputable def abandonments (γ : ℝ) (ω : Ω) (t : ℝ≥0) : ℕ :=
  s.abandonClock ω (γ * s.cumOverflow ω t)

/-- The **system equations** of the `n`-th system on the path `ω` (arXiv:1905.04198v1,
pp.5–6, 8):
1. the paths of `Xⁿ`, `Iⁿₖ`, `Rⁿₖ` are càdlàg ("The paths of Xⁿ(·) are in D_R[0, ∞)", p.8);
2. `Iⁿₖ(t) ∈ {0, 1}`;
3. `Iⁿₖ(t) = Iⁿₖ(0) − Rⁿₖ(t) + Dⁿₖ(t)` (p.5);
4. `Rⁿₖ` is a counting process (`Rⁿₖ(0) = 0`, nondecreasing, unit jumps) that increases only when
   server `k` is idle just before: `(1 − Iⁿₖ(t−)) dRⁿₖ(t) = 0` (p.5);
5. non-idling (3.1): `(Xⁿ(t) − n)⁻ = Σₖ Iⁿₖ(t)` (p.5);
6. `Xⁿ(t) = Xⁿ(0) + Aⁿ(t) − Σₖ Dⁿₖ(t) − Nⁿ(γ ∫₀ᵗ (Xⁿ(s) − n)⁺ ds)` (p.6): first-come-first-served,
   abandonment from the queue only.

**Formalization Note.** `(Xⁿ(t) − n)⁻` is the truncated subtraction `n - Xⁿ(t)` in `ℕ`.
Non-preemptive service is built into `departures`. -/
def SystemEqs (lam γ : ℝ) (ω : Ω) : Prop :=
  PuhaWardFluid.Limit.IsCadlag (fun t => (s.X ω t : ℝ)) ∧
  (∀ k, PuhaWardFluid.Limit.IsCadlag (fun t => (s.I k ω t : ℝ)) ∧
    PuhaWardFluid.Limit.IsCadlag (fun t => (s.R k ω t : ℝ))) ∧
  (∀ k t, s.I k ω t ≤ 1) ∧
  (∀ k t, (s.I k ω t : ℤ) = s.I k ω 0 - s.R k ω t + s.departures k ω t) ∧
  (∀ k, s.R k ω 0 = 0 ∧ Monotone (s.R k ω) ∧
    ∀ t, s.R k ω t ≤ Function.leftLim (s.R k ω) t + 1 ∧
      (s.R k ω t ≠ Function.leftLim (s.R k ω) t → Function.leftLim (s.I k ω) t = 1)) ∧
  (∀ t, n - s.X ω t = ∑ k, s.I k ω t) ∧
  (∀ t, (s.X ω t : ℝ) = s.X ω 0 + s.arrivals lam ω t - ∑ k, (s.departures k ω t : ℝ) -
    s.abandonments γ ω t)

end System

end RandomRateMSQ


