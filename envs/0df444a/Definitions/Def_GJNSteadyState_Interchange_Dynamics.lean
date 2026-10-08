-- Prove2me | Definitions.Def_GJNSteadyState_Interchange_Dynamics
-- name    : GJNSteadyState_Interchange_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:36.836513+00:00
-- url     : https://prove2.me/theorems/d43bedd3-38f3-41ea-a464-64f10dc5aa75
-- title:
--   §2.1, pp. 7–9 — GJN dynamics (4)–(5), Markov state Q̄ = (Q, â, v̂), realizations, stationary distributions, net input (6)
-- statement:
--   This file builds the stochastic dynamics of a generalized Jackson network and the notions of stationarity and conditional expectation used throughout the paper.
--
--   **Counting processes.** For a sequence of times $x(0),x(1),\dots$ let $N(t)$ be the number of $n\ge 0$ with $x(0)+\dots+x(n)\le t$. The arrival process $A_j(t)$ counts in this way the external arrivals to $j$ in $[0,t]$ (built from the first residual time $a_j(0)$ and $a_j(1),a_j(2),\dots$; $A_j\equiv 0$ for $j\notin\mathcal J$), and $S_j(b)$ counts the service completions at $j$ within cumulative busy time $b$ (built from $v_j(0),v_j(1),\dots$). $R^k_j(m)$ is the number of the first $m$ jobs completing service at $k$ that are routed to $j$.
--
--   **Dynamics.** With $Q_j(t)$ the number of jobs at $j$ and $B_j(t)$ the busy time of $j$ in $[0,t]$, for all $t\ge 0$
--   $$Q_j(t) = Q_j(0) + A_j(t) + \sum_{k} R^k_j\big(S_k(B_k(t))\big) - S_j\big(B_j(t)\big),\qquad B_j(t) = t - \int_0^t \mathbf 1\{Q_j(s)=0\}\,ds. \tag{4–5}$$
--
--   **Markov state.** $\hat a_j(t)$ is the time since the last external arrival to $j$ (or $a_j+t$ if none has occurred since time $0$, where $a_j$ is the initial elapsed time; $0$ for $j\notin\mathcal J$), and $\hat v_j(t)$ is the service already received by the job in service at $j$ ($0$ if $j$ is idle). $\bar Q(t) = (Q(t),\hat a(t),\hat v(t))$, with $\bar Q(0) = (z,a,v)$ the initial state.
--
--   **Realizations.** A realization of the network from an initial law $\mu_0$ on $\mathcal X$ is a probability space carrying $\bar Q(0)\sim\mu_0$, the first residual times, independent given $\bar Q(0)=(z,a,v)$ with $a_j(0)\sim$ the residual life of $F_{A,j}$ at age $a_j$ and $v_j(0)\sim$ the residual life of $F_{S,j}$ at age $v_j$, the independent i.i.d. primitives $a_j(l)\sim F_{A,j}$, $v_j(l)\sim F_{S,j}$, $\psi^j(l)\sim$ row $j$ of $P$ ($l\ge1$), and processes $Q,B$ solving (4)–(5) almost surely.
--
--   **Stationarity and expectations.** A probability law $\pi$ on $\mathcal X$ is **stationary** if the network can be started from $\pi$ and $\bar Q(0)\sim\pi$ implies $\bar Q(t)\sim\pi$ for all $t\ge0$. The expectation $\mathbb E[f(\bar Q(t))\mid\bar Q(0)=x]$ is the expectation under a realization started from the point mass at $x$. The file also defines the net input process (6),
--   $$X_j(t) = Q_j(0) + \Big(\alpha_j+\sum_i\mu_ip_{ij}-\mu_j\Big)t + (A_j(t)-\alpha_jt) + \sum_i p_{ij}\big(S_i(B_i(t))-\mu_iB_i(t)\big) - \big(S_j(B_j(t))-\mu_jB_j(t)\big) + \sum_i\big(R^i_j(S_i(B_i(t))) - p_{ij}S_i(B_i(t))\big),$$
--   its fluid counterpart $x_z(t) = z+(\alpha-(I-P')\mu)t$, the diffusion scaling $Q(0)/\sqrt n$ of a state and the law of $Q(0)/\sqrt n$ under a law $\mu$ on $\mathcal X$.
--
--   **Formalization Note** The page defines $A_j(t)=\sup\{n:\sum_{0\le l\le n}a_j(l)\le t\}$, which is one less than the number of arrivals in $[0,t]$; the count of renewal epochs is used, which is what (4) needs (and what the proof on p. 31 uses: "$A_j(0,t)=1+A_j(\tau',t)$"). The page describes $a_j(0)$ both as a full interarrival time conditioned on exceeding $a_{0,j}$ (p. 6) and as the residual time (p. 31); the residual reading is used, the one that makes $\bar Q$ Markov. Conditioning on $\bar Q(0)=x$ is encoded by realizations from the point mass $\delta_x$, and `expectAt` is the supremum over such realizations (all have the same law). Stationarity is equality of laws of $\bar Q(t)$ on $\mathcal X$, equivalent to the paper's (21) on this Polish space; the conjunct "a realization from $\pi$ exists" prevents the definition from holding vacuously. The dynamics (4) is required for $t>0$, with $Q(0)=z$ separately. `expectOn` is the same expectation operator on the state space $\mathcal X$ (the subtype of `InStateSpace` states), the form in which Definition 2 and (24)–(26) are applied to $\bar Q$. Measurability of every coordinate, of the paths $s\mapsto Q_j(s)$ (so that the integral in (5) is a Lebesgue integral of a measurable function) and of $\bar Q(t)$ is part of the definition of a realization.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, pp. 6–9, Section 2.1 (counting processes, (4)–(7), Markovian representation, stationarity); p. 11 (fluid model); p. 14, (21) and Section 3.1 (E_x); p. 18 (π̂ⁿ)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network

open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-!
Gamarnik–Zeevi (2006), §2.1, pp. 6–9: counting processes, the dynamics (4)–(5), the Markov
state `Q̄ = (Q, â, v̂)`, realizations of the network from an initial law, stationary
distributions, the expectation `E[· | Q̄(0) = x]`, the net input process (6) and its fluid
counterpart (p. 11), and the diffusion scaling `Q/√n`.
-/

/-- Number of renewal epochs in `[0, t]` of the sequence of times `x 0, x 1, …`: the number of
`n ≥ 0` with `x 0 + ⋯ + x n ≤ t` (the paper's `A_j(t)` and `S_j(t)`, p. 7, counted so that one
epoch in `[0, t]` gives `1`). -/
noncomputable def countRenewals (x : ℕ → ℝ) (t : ℝ) : ℕ :=
  Nat.card {n : ℕ // ∑ l ∈ Finset.range (n + 1), x l ≤ t}

/-- `R^k_j(m)`: the number of the routing decisions `ψ^k(1), …, ψ^k(m)` that send a job to
station `j` (p. 7). -/
def routedCount {J : ℕ} (ψk : ℕ → Fin (J + 1)) (j : Fin J) (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter (fun l => ψk l = j.castSucc)).card

/-- Arrival counting process `A_j(t)` of station `j`: the number of external arrivals in
`[0, t]`, built from `a_j(0), a_j(1), …`; identically `0` for `j ∉ 𝒥`. -/
noncomputable def arrCount {J : ℕ} (N : Network J) (a : Fin J → ℕ → ℝ) (j : Fin J) (t : ℝ) :
    ℕ :=
  if j ∈ N.arrSet then countRenewals (a j) t else 0

/-- Elapsed time `â_j(t)` since the last external arrival to `j` (p. 9): `t` minus the epoch
of the last arrival in `[0, t]`, or `a₀ + t` if there has been none yet (`a₀` the initial
elapsed time); `0` for `j ∉ 𝒥`. -/
noncomputable def elapsedArr {J : ℕ} (N : Network J) (a0 : Fin J → ℝ) (a : Fin J → ℕ → ℝ)
    (j : Fin J) (t : ℝ) : ℝ :=
  if j ∈ N.arrSet then
    (if countRenewals (a j) t = 0 then a0 j + t
     else t - ∑ l ∈ Finset.range (countRenewals (a j) t), a j l)
  else 0

/-- Elapsed service time `v̂_j(t)` of the job in service at `j` (p. 9), given the queue length
`q = Q_j(t)` and the busy time `b = B_j(t)`: `0` if the station is idle; otherwise the busy
time since the last service completion, or `v₀ + b` before the first completion (`v₀` the
initial elapsed service time). -/
noncomputable def elapsedSrv {J : ℕ} (v0 : Fin J → ℝ) (v : Fin J → ℕ → ℝ) (j : Fin J)
    (q : ℕ) (b : ℝ) : ℝ :=
  if q = 0 then 0
  else if countRenewals (v j) b = 0 then v0 j + b
  else b - ∑ l ∈ Finset.range (countRenewals (v j) b), v j l

/-- The Markov state `Q̄(t) = (Q(t), â(t), v̂(t))` (p. 9) built from the initial state
`x₀ = (z, a₀, v₀)`, the primitives `a`, `v`, the queue length `Q` and the busy time `B`; by
definition `Q̄(0) = x₀`. -/
noncomputable def stateAt {J : ℕ} (N : Network J) (x0 : State J) (a v : Fin J → ℕ → ℝ)
    (Q : ℝ → Fin J → ℕ) (B : ℝ → Fin J → ℝ) (t : ℝ) : State J :=
  if t = 0 then x0
  else (Q t, fun j => elapsedArr N x0.2.1 a j t, fun j => elapsedSrv x0.2.2 v j (Q t j) (B t j))

/-- The law of the first residual times `(a_j(0))_j, (v_j(0))_j` given the initial state
`x = (z, a, v)`: independent coordinates, `a_j(0)` with the residual law of `F_{A,j}` at `a_j`
and `v_j(0)` with the residual law of `F_{S,j}` at `v_j`. -/
noncomputable def firstTimesLaw {J : ℕ} (N : Network J) (x : State J) :
    Measure ((Fin J → ℝ) × (Fin J → ℝ)) :=
  (Measure.pi fun j => residual (N.FA j) (x.2.1 j)).prod
    (Measure.pi fun j => residual (N.FS j) (x.2.2 j))

/-- The joint law of the primitive sequences `(a_j(l))_{j, l ≥ 1}`, `(v_j(l))_{j, l ≥ 1}`,
`(ψ^j(l))_{j, l ≥ 1}`: all independent, `a_j(l) ∼ F_{A,j}`, `v_j(l) ∼ F_{S,j}`, and `ψ^j(l)`
distributed as row `j` of `P`. The index `(j, l)` of the product stands for `(j, l + 1)`. -/
noncomputable def primLaw {J : ℕ} (N : Network J) :
    Measure ((Fin J × ℕ → ℝ) × (Fin J × ℕ → ℝ) × (Fin J × ℕ → Fin (J + 1))) :=
  (Measure.infinitePi fun p : Fin J × ℕ => N.FA p.1).prod
    ((Measure.infinitePi fun p : Fin J × ℕ => N.FS p.1).prod
      (Measure.infinitePi fun p : Fin J × ℕ => routeLaw N.P p.1))

/-- A realization of the network `N` started from the initial law `μ₀` on `𝒳`: a probability
space carrying
* the initial state `X0 ∼ μ₀`;
* the first residual times `a j 0`, `v j 0` and the i.i.d. primitives `a j l`, `v j l`,
  `ψ j l` (`l ≥ 1`), with joint law: given `X0 = x`, the first times have law
  `firstTimesLaw N x`, and the primitive sequences are independent of all of these with law
  `primLaw N` (stated on measurable rectangles);
* the queue length process `Q` and the busy time process `B`, satisfying `Q(0) = z`, the
  dynamics (4) for `t > 0` and (5) with `B_j(t) = t − I_j(t)`, almost surely.
Every coordinate is measurable, and so is the Markov state `Q̄(t)` for each `t`. -/
structure Realization {J : ℕ} (N : Network J) (μ0 : Measure (State J)) : Type 1 where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  X0 : Ω → State J
  a : Fin J → ℕ → Ω → ℝ
  v : Fin J → ℕ → Ω → ℝ
  ψ : Fin J → ℕ → Ω → Fin (J + 1)
  Q : ℝ → Ω → Fin J → ℕ
  B : ℝ → Ω → Fin J → ℝ
  meas_X0 : Measurable X0
  meas_a : ∀ j l, Measurable (a j l)
  meas_v : ∀ j l, Measurable (v j l)
  meas_ψ : ∀ j l, Measurable (ψ j l)
  meas_Q : ∀ t, Measurable (Q t)
  meas_B : ∀ t, Measurable (B t)
  joint_law : ∀ (A : Set (State J)) (Bs : Set ((Fin J → ℝ) × (Fin J → ℝ)))
      (D : Set ((Fin J × ℕ → ℝ) × (Fin J × ℕ → ℝ) × (Fin J × ℕ → Fin (J + 1)))),
      MeasurableSet A → MeasurableSet Bs → MeasurableSet D →
      P {ω | X0 ω ∈ A ∧ ((fun j => a j 0 ω), (fun j => v j 0 ω)) ∈ Bs ∧
          ((fun p : Fin J × ℕ => a p.1 (p.2 + 1) ω), (fun p : Fin J × ℕ => v p.1 (p.2 + 1) ω),
            (fun p : Fin J × ℕ => ψ p.1 (p.2 + 1) ω)) ∈ D} =
        (∫⁻ x in A, firstTimesLaw N x Bs ∂μ0) * primLaw N D
  init : ∀ ω, Q 0 ω = (X0 ω).1
  dynamics : ∀ᵐ ω ∂P,
    (∀ j, Measurable (fun s => Q s ω j)) ∧
    (∀ t : ℝ, 0 < t → ∀ j : Fin J,
      ((Q t ω j : ℕ) : ℤ) =
        ((X0 ω).1 j : ℤ) + (arrCount N (fun i l => a i l ω) j t : ℤ)
          + ∑ k : Fin J,
              (routedCount (fun l => ψ k l ω) j
                (countRenewals (fun l => v k l ω) (B t ω k)) : ℤ)
          - (countRenewals (fun l => v j l ω) (B t ω j) : ℤ)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ j : Fin J,
      B t ω j = t - ∫ s in Set.Icc 0 t, (if Q s ω j = 0 then (1 : ℝ) else 0))
  meas_state : ∀ t, Measurable (fun ω =>
    stateAt N (X0 ω) (fun j l => a j l ω) (fun j l => v j l ω) (fun s => Q s ω) (fun s => B s ω) t)

attribute [instance] Realization.mΩ Realization.isProb

/-- The Markov state `Q̄(t)` of a realization. -/
noncomputable def Realization.qbar {J : ℕ} {N : Network J} {μ0 : Measure (State J)}
    (R : Realization N μ0) (t : ℝ) (ω : R.Ω) : State J :=
  stateAt N (R.X0 ω) (fun j l => R.a j l ω) (fun j l => R.v j l ω) (fun s => R.Q s ω)
    (fun s => R.B s ω) t

/-- `π` is a stationary distribution of the GJN `N` (p. 9): the network can be started from
`π`, and whenever `Q̄(0) ∼ π`, then `Q̄(t) ∼ π` for all `t ≥ 0`. -/
def IsStationary {J : ℕ} (N : Network J) (π : Measure (State J)) : Prop :=
  Nonempty (Realization N π) ∧
    ∀ R : Realization N π, ∀ t : ℝ, 0 ≤ t → R.P.map (R.qbar t) = π

/-- `E[f(Q̄(t)) | Q̄(0) = x]` (§3.1, p. 14): the expectation of `f(Q̄(t))` for the network
started from the deterministic state `x`, taken over realizations from `δ_x` (all of which have
the same law). -/
noncomputable def expectAt {J : ℕ} (N : Network J) (x : State J) (t : ℝ)
    (f : State J → ENNReal) : ENNReal :=
  ⨆ R : Realization N (Measure.dirac x), ∫⁻ ω, f (R.qbar t ω) ∂(R.P)

/-- The expectation operator `E_x f(Q̄(t))` of the Markov process `Q̄` on its state space
`𝒳 = ℤ₊^J × ℝ₊^{2J}` (the subtype of `InStateSpace` states): `expectAt` from `x`, with `f`
extended by `0` off `𝒳` (started in `𝒳`, `Q̄(t)` stays in `𝒳` almost surely). This is the
operator `E_x` of §3.1 (p. 14) that Definition 2 and (24)–(26) take suprema over. -/
noncomputable def expectOn {J : ℕ} (N : Network J) (x : {y : State J // InStateSpace y})
    (t : ℝ) (f : {y : State J // InStateSpace y} → ENNReal) : ENNReal := by
  classical
  exact expectAt N x.1 t (fun y => if h : InStateSpace y then f ⟨y, h⟩ else 0)

/-- The net input ("free") process `X(t)` of (6), p. 8:
`X_j(t) = Q_j(0) + (α_j + Σ_i μ_i p_ij − μ_j) t + (A_j(t) − α_j t)
  + Σ_i p_ij (S_i(B_i(t)) − μ_i B_i(t)) − (S_j(B_j(t)) − μ_j B_j(t))
  + Σ_i (R^i_j(S_i(B_i(t))) − p_ij S_i(B_i(t)))`. -/
noncomputable def Realization.netInput {J : ℕ} {N : Network J} {μ0 : Measure (State J)}
    (R : Realization N μ0) (t : ℝ) (ω : R.Ω) (j : Fin J) : ℝ :=
  let S : Fin J → ℝ := fun i => (countRenewals (fun l => R.v i l ω) (R.B t ω i) : ℝ)
  ((R.X0 ω).1 j : ℝ) + (alpha N j + ∑ i, mu N i * N.P i j - mu N j) * t
    + ((arrCount N (fun i l => R.a i l ω) j t : ℝ) - alpha N j * t)
    + ∑ i, N.P i j * (S i - mu N i * R.B t ω i)
    - (S j - mu N j * R.B t ω j)
    + ∑ i, ((routedCount (fun l => R.ψ i l ω) j
          (countRenewals (fun l => R.v i l ω) (R.B t ω i)) : ℝ) - N.P i j * S i)

/-- The fluid path `x_z(t) = z + (α − (I − P′)μ) t` (p. 11). -/
noncomputable def fluidInput {J : ℕ} (N : Network J) (z : Fin J → ℝ) (t : ℝ) : Fin J → ℝ :=
  z + t • (alpha N - (1 - N.Pᵀ) *ᵥ mu N)

/-- The diffusion-scaled queue length `z/√n` of a state `(z, a, v)`. -/
noncomputable def scaleQ {J : ℕ} (n : ℕ) (x : State J) : Fin J → ℝ :=
  fun j => (x.1 j : ℝ) / Real.sqrt n

theorem measurable_scaleQ {J : ℕ} (n : ℕ) : Measurable (scaleQ (J := J) n) := by
  unfold scaleQ
  fun_prop

/-- The law of `Q(0)/√n` when `Q̄(0) ∼ μ`, as a probability measure on `ℝ^J`. -/
noncomputable def scaledLaw {J : ℕ} (μ : Measure (State J)) [IsProbabilityMeasure μ] (n : ℕ) :
    ProbabilityMeasure (Fin J → ℝ) :=
  ⟨μ.map (scaleQ n), Measure.isProbabilityMeasure_map (measurable_scaleQ n).aemeasurable⟩

/-- The workload `w′z` of a state `(z, a, v)` (pp. 11, 17), as a nonnegative real (it is
nonnegative because `w ≥ 0` when `P` is substochastic). -/
noncomputable def workload {J : ℕ} (N : Network J) (x : State J) : NNReal :=
  Real.toNNReal (wvec N ⬝ᵥ fun j => (x.1 j : ℝ))

end GJNSteadyState.Interchange


