-- Prove2me | Definitions.Def_OptStopC1_TimeDeriv_Problem
-- name    : OptStopC1_TimeDeriv_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:53.482405+00:00
-- url     : https://prove2.me/theorems/2dd26cec-6ee0-4162-8726-aa10b1b106ad
-- title:
--   (2.2)–(2.3), p. 3 — the finite-horizon optimal stopping problem: value V(t, x), sets C and D, boundary ∂C, well-posedness
-- statement:
--   This file defines the finite-horizon optimal stopping problem (2.2) for the time-space process $X^{t,x}_s=(t+s,X^x_s)$, its value function, the continuation and stopping sets, and the standing premise that the problem is well posed.
--
--   **Data.** A probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_s)_{s\ge0}$, a horizon $T$, a spatial flow $X^x_s$ in $\mathbb R^{d-1}$, and three real functions $\lambda,G,H$ of $(t,x)$. The standing hypotheses are: $P$ is a probability measure; $(\mathcal F_s)$ is right-continuous; $T>0$; $X$ is a càdlàg flow adapted to $(\mathcal F_s)$ with the strong Markov property and left continuity over stopping times; entry and hitting times of open and closed sets are stopping times; $\lambda$, $G$ and $H$ are continuous on $[0,T]\times\mathbb R^{d-1}$ and $\lambda\ge0$ there.
--
--   **Discounting (2.3).** Along the flow started at $(t,x)$,
--   $$\Lambda^{t,x}_s=\int_0^s\lambda(t+u,X^x_u)\,du .$$
--
--   **Value (2.2).** A stopping time $\tau$ is admissible for $(t,x)$ if it is finite valued with $0\le\tau\le T-t$. The value function is
--   $$V(t,x)=\sup_{0\le\tau\le T-t}\mathsf E\Big[e^{-\Lambda^{t,x}_\tau}G(t+\tau,X^x_\tau)+\int_0^\tau e^{-\Lambda^{t,x}_s}H(t+s,X^x_s)\,ds\Big]$$
--   for $(t,x)\in[0,T]\times\mathbb R^{d-1}$.
--
--   **Sets.** The continuation set and the stopping set are
--   $$C=\{(t,x)\in[0,T]\times\mathbb R^{d-1} : V(t,x)>G(t,x)\},\qquad D=\{(t,x)\in[0,T]\times\mathbb R^{d-1} : V(t,x)=G(t,x)\},$$
--   and the optimal stopping boundary is $\partial C=D\cap\overline C$, the points of $D$ at which $C$ accumulates.
--
--   **Well-posedness (p. 4).** The problem is well posed if for every $(t,x)\in[0,T]\times\mathbb R^{d-1}$:
--   1. the payoff of every admissible stopping time is integrable;
--   2. the first entry time $\tau^{t,x}_D$ into $D$ is a stopping time;
--   3. some admissible stopping time equal to $\tau^{t,x}_D$ almost surely attains the supremum in (2.2).
--
--   In other words, $\tau_D$ is optimal, which the paper takes as a standing premise.
--
--   **Formalization Note** Expectations are Bochner integrals and $V$ is a real `sSup`. Under well-posedness, the set of admissible expected payoffs is bounded above and attains its supremum, so $V$ is the paper's value and not a junk value. Admissible stopping times are maps $\Omega\to[0,\infty)$ that are stopping times for the common filtration, the same for every starting point. $\Lambda$ and the running reward are interval integrals along the path $u\mapsto X^x_u$. The paper's "mild integrability conditions" (p. 3) are item 1 of well-posedness. Only the values of $V$ on $[0,T]\times\mathbb R^{d-1}$ are meaningful.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 3–4, (2.2), (2.3), (2.4), well-posedness (p. 4); C and D in the time-space form, pp. 15–16

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow

namespace OptStopC1.TimeDeriv

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- The data of the finite-horizon optimal stopping problem (2.2) for the time-space process
`X^{t,x}_s = (t + s, X^x_s)` (§2.1, p. 3; §4.2, pp. 15–16): a probability space `(Ω, F, P)`, one
filtration `𝔽`, the horizon `T`, the spatial flow `X`, the killing rate `λ`, the gain `G` and the
running reward `H`, all three functions of `(t, x) ∈ ℝ × ℝ^{d−1}`. -/
structure StoppingProblem (m : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  P : Measure Ω
  𝔽 : Filtration ℝ≥0 mΩ
  T : ℝ
  X : Space m → ℝ≥0 → Ω → Space m
  lam : ℝ × Space m → ℝ
  G : ℝ × Space m → ℝ
  H : ℝ × Space m → ℝ

namespace StoppingProblem

variable {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : StoppingProblem m Ω)

/-- The standing hypotheses of §2.1 (pp. 3–4) and §2.4 (p. 6) for the time-space setting: `P` is a
probability measure; `𝔽` is right-continuous; `T > 0`; the spatial part is a càdlàg flow adapted
to `𝔽` with the strong Markov property; first entry and hitting times of open and closed sets are
stopping times (p. 9); `λ`, `G`, `H` are continuous on `[0, T] × ℝ^{d−1}` and `λ ≥ 0` there. -/
structure Standing : Prop where
  prob : IsProbabilityMeasure M.P
  right_cont : M.𝔽.IsRightContinuous
  T_pos : 0 < M.T
  flow : IsCadlagFlow M.𝔽 M.X
  quasi_left_cont : IsQuasiLeftContinuousFlow M.P M.𝔽 M.X
  strong_markov : IsStrongMarkovFlow M.P M.𝔽 M.X
  stopping_times : EntryHittingAreStoppingTimes M.𝔽 M.T M.X
  lam_cont : ContinuousOn M.lam (domain m M.T)
  lam_nonneg : ∀ p ∈ domain m M.T, 0 ≤ M.lam p
  G_cont : ContinuousOn M.G (domain m M.T)
  H_cont : ContinuousOn M.H (domain m M.T)

/-- The discount functional (2.3) along the flow started at `p = (t, x)`:
`Λ^{t,x}_s(ω) = ∫_0^s λ(t + u, X^x_u(ω)) du`. -/
noncomputable def discount (p : ℝ × Space m) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..(s : ℝ), M.lam (p.1 + u, M.X p.2 u.toNNReal ω)

/-- The payoff of stopping at the random time `τ` when the time-space process starts at
`p = (t, x)`: `e^{−Λ^{t,x}_τ} G(t + τ, X^x_τ) + ∫_0^τ e^{−Λ^{t,x}_s} H(t + s, X^x_s) ds`. -/
noncomputable def payoff (p : ℝ × Space m) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-M.discount p (τ ω) ω) * M.G (p.1 + τ ω, M.X p.2 (τ ω) ω) +
    ∫ u in (0 : ℝ)..(τ ω : ℝ),
      Real.exp (-M.discount p u.toNNReal ω) * M.H (p.1 + u, M.X p.2 u.toNNReal ω)

/-- Admissible stopping times for the start `p = (t, x)` in (2.2): finite-valued `𝔽`-stopping
times `τ` with `0 ≤ τ ≤ T − t`. -/
def IsAdmissible (p : ℝ × Space m) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime M.𝔽 (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) ∧ ∀ ω, (τ ω : ℝ) ≤ M.T - p.1

/-- The expected payoff `E[payoff]` of the stopping time `τ` from `p` (a Bochner integral). -/
noncomputable def gain (p : ℝ × Space m) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, M.payoff p τ ω ∂M.P

/-- The value function (2.2): `V(t, x) = sup_{0 ≤ τ ≤ T − t} E[payoff]`, the supremum over the
admissible stopping times for `(t, x)`. -/
noncomputable def value (p : ℝ × Space m) : ℝ :=
  sSup {v | ∃ τ, M.IsAdmissible p τ ∧ v = M.gain p τ}

/-- The stopping set `D = {(t, x) ∈ [0, T] × ℝ^{d−1} | V(t, x) = G(t, x)}` (p. 16). -/
def stoppingSet : Set (ℝ × Space m) :=
  {p | p ∈ domain m M.T ∧ M.value p = M.G p}

/-- The continuation set `C = {(t, x) ∈ [0, T] × ℝ^{d−1} | V(t, x) > G(t, x)}` (p. 15). -/
def contSet : Set (ℝ × Space m) :=
  {p | p ∈ domain m M.T ∧ M.G p < M.value p}

/-- The optimal stopping boundary `∂C`: the points of `D` at which `C` accumulates,
`∂C := D ∩ closure C`. -/
def boundary : Set (ℝ × Space m) :=
  M.stoppingSet ∩ closure M.contSet

/-- **Well-posedness** (p. 4, the standing premise "τ_D is optimal"): for every start
`p ∈ [0, T] × ℝ^{d−1}`,
1. the payoff of every admissible stopping time is integrable (the "mild integrability
   conditions" of p. 3);
2. the entry time `τ^{p}_D` into the stopping set is an `𝔽`-stopping time;
3. some admissible `τ*` equals `τ^{p}_D` almost surely and is optimal:
   `E[payoff(τ)] ≤ E[payoff(τ*)]` for every admissible `τ`. -/
def IsWellPosed : Prop :=
  ∀ p ∈ domain m M.T,
    (∀ τ, M.IsAdmissible p τ → Integrable (M.payoff p τ) M.P) ∧
    IsStoppingTime M.𝔽 (entryTime M.T M.X M.stoppingSet p) ∧
    ∃ τs : Ω → ℝ≥0, M.IsAdmissible p τs ∧
      (∀ᵐ ω ∂M.P, ((τs ω : ℝ≥0) : WithTop ℝ≥0) = entryTime M.T M.X M.stoppingSet p ω) ∧
      ∀ τ, M.IsAdmissible p τ → M.gain p τ ≤ M.gain p τs

end StoppingProblem

end OptStopC1.TimeDeriv


