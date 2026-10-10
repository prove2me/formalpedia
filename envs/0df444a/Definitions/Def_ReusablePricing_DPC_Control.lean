-- Prove2me | Definitions.Def_ReusablePricing_DPC_Control
-- name    : ReusablePricing_DPC_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:32.870635+00:00
-- url     : https://prove2.me/theorems/385b54bb-9c7f-4e0d-b8f8-b7327eb7338a
-- title:
--   §4, pp. 8–12, ec5 — path law, DPC(ϵ), average loss, non-anticipating controls and the events 𝒜, 𝒢 of (EC.12)
-- statement:
--   This file defines the stochastic system run by a pricing control in the basic reusable-resource model, the Deterministic Price Control DPC($\epsilon$), its average loss, and the events used in its analysis.
--
--   **Paths.** In each period $t \in [1,T]$ either no request arrives or exactly one request of some type $j$ arrives. A sample path $\omega$ lists these outcomes, and $D^t_j(\omega) \in \{0,1\}$ indicates a type-$j$ arrival in period $t$. Under a rate vector $x$, one period's outcome is type $j$ with probability $x_j$ and "no request" with probability $1 - \sum_j x_j$.
--
--   **Available capacity** at the beginning of period $t$ (pp. 8, 11):
--   $$C^t_i = C_i - \sum_{s=(t-n+1)^+}^{t-1} \sum_j a_{ij} D^s_j ,$$
--   so $C^1 = C$.
--
--   **DPC($\epsilon$)** (p. 12). In period $t$, for each type $j$: if $C^t \succeq A^j$ the posted rate is the Euclidean projection onto $\Omega_\lambda$ (a coordinatewise clamp to $[0, \lambda_U]$) of
--   $$\lambda^{t,D}_j - \frac{\epsilon}{\underline n}\,\mathbf 1\{\lambda^{t,D}_j > 0\};$$
--   otherwise type $j$ is turned off (rate $0$). The rate in period $t$ depends only on the outcomes of periods $1, \dots, t-1$.
--
--   **Path law.** Periods are independent given the past: the probability of $\omega$ is the product over $t \in [1,T]$ of the probability of its period-$t$ outcome under the rate DPC posts in period $t$. $\mathbf E$ and $\mathbf P$ are the corresponding expectation and probability. The expected revenue is $\mathbf E[R^{DPC(\epsilon)}] = \mathbf E[\sum_{t=1}^T r^t(\lambda^t)]$, and the average loss is
--   $$\mathcal L(DPC(\epsilon)) = \frac{J^D - \mathbf E[R^{DPC(\epsilon)}]}{T}.$$
--
--   **Events of EC.3.** With $\Delta^s_j = D^s_j - \lambda^s_j$, for $b \in [1, T/n]$ and every $j$,
--   $$\mathcal A^b_j(\epsilon,\delta) = \Big\{ \Big|\sum_{s=(b-1)n+1}^{t} \Delta^s_j\Big| < \delta \text{ for all } t \in [(b-1)n+1, bn] \Big\}, \qquad \mathcal G(\epsilon,\delta) = \bigcap_{b,j} \mathcal A^b_j(\epsilon,\delta).$$
--
--   **General controls** (for Lemma 1). A non-anticipating control assigns to each period $t$ a rate vector in $\Omega_\lambda$ that depends only on the outcomes of periods before $t$. It runs under the same product path law. It is feasible for OPT when, on every path of positive probability, $\sum_{s=(t-n+1)^+}^{t} \sum_j a_{ij} D^s_j \le C_i$ for all $t \in [1,T]$ and $i$.
--
--   **Formalization Note.** Turning a type off (the paper's turn-off price $\bar p_j$) is rate $0$. The expected revenue is written $\mathbf E[\sum_t r^t(\lambda^t)]$, the tower-property form used in the proofs (EC.1, ec2; EC.3 Step 2, ec8). In (EC.12) the maximum over $t \le bn$ is taken over $t$ in the $b$-th cycle; for smaller $t$ the sum is empty. The path space is finite, so expectations are finite sums.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), pp. 7–9 (OPT, loss), pp. 11–12 (C^t, DPC(ϵ)), p. ec5 (Δ, (EC.12), 𝒢(ϵ, δ))

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model

namespace ReusablePricing.DPC

open Finset

noncomputable section

namespace Basic

variable (P : Basic)

/-- A sample path: the outcome of each period `1, …, T` (`ω ⟨t - 1, _⟩` for period `t`), either
`none` (no request) or `some j` (one request of service type `j`). -/
abbrev Path : Type := Fin P.T → Option (Fin P.J)

/-- The outcome of period `t` on the path `ω`; `none` outside `[1, T]`. -/
def outcome (t : ℕ) (ω : P.Path) : Option (Fin P.J) :=
  if h : 1 ≤ t ∧ t ≤ P.T then ω ⟨t - 1, by omega⟩ else none

/-- Realized demand `D^t_j ∈ {0, 1}`. -/
def D (t : ℕ) (ω : P.Path) (j : Fin P.J) : ℝ :=
  if P.outcome t ω = some j then 1 else 0

/-- Law of one period's outcome under the demand-rate vector `x`: a request of type `j` with
probability `x_j`, no request with probability `1 - ∑_j x_j`. -/
def q (x : Fin P.J → ℝ) : Option (Fin P.J) → ℝ
  | none => 1 - ∑ j, x j
  | some j => x j

/-- Available capacity at the beginning of period `t` (p. 8, p. 11):
`C^t_i = C_i - ∑_{s=(t-n+1)⁺}^{t-1} ∑_j a_{ij} D^s_j`. It reads only the outcomes of periods
`< t`; for `t = 1` the sum is empty and `C^1 = C`. -/
def freeCap (t : ℕ) (ω : P.Path) (i : Fin P.I) : ℝ :=
  (P.C i : ℝ) - ∑ s ∈ Icc (P.winStart t) (t - 1), ∑ j, (P.A i j : ℝ) * P.D s ω j

/-- The demand rate posted by DPC(ε) (p. 12) in period `t` for type `j`: if `C^t ⪰ A^j` it is the
Euclidean projection onto `Ω_λ` (coordinatewise clamp to `[0, λ_U]`) of
`λ^{t,D}_j - (ε / n̲) 1{λ^{t,D}_j > 0}`; otherwise type `j` is turned off (rate `0`).
It depends on `ω` only through `freeCap t ω`, i.e. through the outcomes of periods `< t`. -/
def dpcRate (ε : ℝ) (nl : ℕ) (t : ℕ) (ω : P.Path) (j : Fin P.J) : ℝ :=
  if ∀ i, (P.A i j : ℝ) ≤ P.freeCap t ω i then
    max 0 (min P.lamU (P.lamD t j - ε / nl * (if 0 < P.lamD t j then 1 else 0)))
  else 0

/-- Probability of the path `ω` under DPC(ε): independent periods, period `t` distributed by `q`
at the rate DPC posts in period `t`. -/
def pathProb (ε : ℝ) (nl : ℕ) (ω : P.Path) : ℝ :=
  ∏ t ∈ Icc 1 P.T, P.q (P.dpcRate ε nl t ω) (P.outcome t ω)

/-- Expectation under DPC(ε). -/
def E (ε : ℝ) (nl : ℕ) (X : P.Path → ℝ) : ℝ := ∑ ω, P.pathProb ε nl ω * X ω

open scoped Classical in
/-- Probability of an event under DPC(ε). -/
def prob (ε : ℝ) (nl : ℕ) (S : P.Path → Prop) : ℝ :=
  ∑ ω, if S ω then P.pathProb ε nl ω else 0

/-- Expected revenue of DPC(ε), in the form `E[∑_{t=1}^T r^t(λ^t)]`. -/
def expRevenue (ε : ℝ) (nl : ℕ) : ℝ :=
  P.E ε nl (fun ω => ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω))

/-- The average loss `L(DPC(ε)) = (J^D - E[R^{DPC(ε)}]) / T` (p. 9). -/
def loss (ε : ℝ) (nl : ℕ) : ℝ := (P.JD - P.expRevenue ε nl) / P.T

/-- The demand error `Δ^s_j = D^s_j - λ^s_j` under DPC(ε) (ec5). -/
def Delta (ε : ℝ) (nl : ℕ) (s : ℕ) (ω : P.Path) (j : Fin P.J) : ℝ :=
  P.D s ω j - P.dpcRate ε nl s ω j

/-- The event `𝒜^b_j(ε, δ)` of (EC.12): `|∑_{s=(b-1)n+1}^{t} Δ^s_j| < δ` for every `t` in the
`b`-th service cycle `[(b-1)n+1, bn]`. -/
def InA (ε : ℝ) (nl : ℕ) (δ : ℝ) (b : ℕ) (j : Fin P.J) (ω : P.Path) : Prop :=
  ∀ t ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
    |∑ s ∈ Icc ((b - 1) * P.n + 1) t, P.Delta ε nl s ω j| < δ

/-- The event `𝒢(ε, δ) = ⋂_{b, j} 𝒜^b_j(ε, δ)`, `b ∈ [1, T/n]`, `j ∈ [1, J]` (ec5). -/
def InG (ε : ℝ) (nl : ℕ) (δ : ℝ) (ω : P.Path) : Prop :=
  ∀ j, ∀ b ∈ Icc 1 (P.T / P.n), P.InA ε nl δ b j ω

/-- A general non-anticipating control in rate form (the set `Π` of p. 8): for each period
`t ∈ [1, T]` and path `ω`, a demand-rate vector in `Ω_λ` that depends on `ω` only through the
outcomes of periods `1, …, t - 1`. -/
structure RateControl where
  rate : ℕ → P.Path → Fin P.J → ℝ
  mem : ∀ t ∈ Icc 1 P.T, ∀ ω, rate t ω ∈ P.OmegaLam
  nonanticipating : ∀ t ∈ Icc 1 P.T, ∀ ω ω' : P.Path,
    (∀ s : Fin P.T, s.val + 1 < t → ω s = ω' s) → rate t ω = rate t ω'

variable {P}

/-- Path probability under a general rate control. -/
def RateControl.pathProb (π : P.RateControl) (ω : P.Path) : ℝ :=
  ∏ t ∈ Icc 1 P.T, P.q (π.rate t ω) (P.outcome t ω)

/-- Expectation under a general rate control. -/
def RateControl.E (π : P.RateControl) (X : P.Path → ℝ) : ℝ := ∑ ω, π.pathProb ω * X ω

/-- Expected revenue `E[∑_{t=1}^T r^t(λ^{t,π})]` of a general rate control. -/
def RateControl.expRevenue (π : P.RateControl) : ℝ :=
  π.E (fun ω => ∑ t ∈ Icc 1 P.T, P.r t (π.rate t ω))

/-- Feasibility for OPT (p. 8), almost surely: on every path of positive probability, for all
`t ∈ [1, T]` and `i`, `∑_{s=(t-n+1)⁺}^{t} ∑_j a_{ij} D^s_j ≤ C_i`. -/
def RateControl.Feasible (π : P.RateControl) : Prop :=
  ∀ ω, 0 < π.pathProb ω → ∀ t ∈ Icc 1 P.T, ∀ i : Fin P.I,
    ∑ s ∈ Icc (P.winStart t) t, ∑ j, (P.A i j : ℝ) * P.D s ω j ≤ (P.C i : ℝ)

end Basic

end

end ReusablePricing.DPC


