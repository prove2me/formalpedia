-- Prove2me | Definitions.Def_ReusablePricing_DPCB_Control
-- name    : ReusablePricing_DPCB_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:55.304269+00:00
-- url     : https://prove2.me/theorems/23c62e30-7079-4086-85f3-3f214ad230be
-- title:
--   §6, pp. 18–19 — batch partitions, availability C̃(t, s), the control DPC-B(m, ϵ), path law and average loss
-- statement:
--   This file defines the generalized batch-adjusted control DPC-B$(m,\epsilon)$ of Section 6 and the probability model under which it runs.
--
--   **Sample paths.** At most one request arrives per period. A sample path $\omega$ records, for each period $t \in [1,T]$, either no request or one request of a type $k$; $D^t_k(\omega) \in \{0,1\}$ indicates a type-$k$ request in period $t$.
--
--   **Batches.** For each type $k$, the horizon is partitioned into adjacent batches $\mathcal{T}_k^1, \dots, \mathcal{T}_k^{B_k}$ covering $[1,T]$, each containing exactly $m_k$ periods with $\lambda^{t,D}_k > 0$; $\beta_k(t)$ is the index of the batch containing $t$, and $\mathcal{T}_k^0 = \emptyset$.
--
--   **Availability.** $\tilde C_i(t,s)$ is the number of units of resource $i$ available for service at period $s$ at the beginning of period $t$, before the request of period $t$ arrives:
--   $$
--   \tilde C_i(t,s) = C_i - \sum_{k=1}^K \sum_{v \in [1,t-1] \,:\, v+\ell_k \le s \le v+\ell_k+n_k-1} a_{ik} D^v_k ,
--   $$
--   and $C^t = \tilde C(t,t)$ is the free capacity at the beginning of period $t$.
--
--   **The control.** With $\Delta^s_k = D^s_k - \lambda^s_k$, DPC-B$(m,\epsilon)$ posts in period $t$, for each type $k$,
--   $$
--   \lambda^t_k = \mathrm{Proj}_{[0,\lambda_U]}\Bigl[\lambda^{t,D}_k - \Bigl(\frac{\epsilon_k}{\underline{n}_k} + \frac{1}{m_k}\sum_{s \in \mathcal{T}_k^{\beta_k(t)-1}} \Delta^s_k\Bigr) \mathbf{1}\{\lambda^{t,D}_k > 0\}\Bigr]
--   $$
--   if $\tilde C(t, t+\ell_k) \succeq A^k$, and turns type $k$ off ($\lambda^t_k = 0$) otherwise. The rates are built period by period, so $\lambda^t$ depends only on the outcomes of periods $1, \dots, t-1$.
--
--   **Law and loss.** The periods are drawn in order: given the past, period $t$ brings a type-$k$ request with probability $\lambda^t_k$ and no request with probability $1 - \sum_k \lambda^t_k$. The probability of a path is the product of these factors, expectations are finite sums over paths, and the average loss is
--   $$
--   \mathcal{L}(\text{DPC-B}(m,\epsilon)) = \frac{J^D_H - \mathbf{E}\bigl[\sum_{t=1}^T r^t(\lambda^t)\bigr]}{T}.
--   $$
--   The file also defines $\min_k \epsilon_k$.
--
--   **Formalization Note** The turn-off price $\bar p_k$ is encoded as rate $0$. $\tilde C$ is defined by its defining sentence on p. 18; the index limits of the update rule of Step 2a do not match the explanation printed below it on p. 19, so the rule is not transcribed. The page defines $\tilde C(t,s)$ only for $s \le T$; the admission test is applied when the service starts within the horizon ($t + \ell_k \le T$), and a request whose service starts after period $T$ uses no capacity counted by DET-H or OPT-H and is not tested. The expected revenue is taken in the form $\mathbf{E}[\sum_t r^t(\lambda^t)]$ used in Step 2 of the proofs (ec8, ec12), which equals the expected collected revenue by the tower property. The partition is passed as data ($\beta$, $B$) together with a validity predicate; this is the paper's "we assume that the above partitioning is possible".
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. 7 (arrival model), p. 9 (average loss), p. 14 (𝒯^0 = ∅), p. 18 (A Generalized DPC-B: partitions 𝒫_k, β_k, Δ^t, C̃_i(t, s)), p. 19 (box DPC-B(m, ϵ))

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Model

open Finset

namespace ReusablePricing.DPCB

namespace General

variable (P : General)

/-- A sample path: the outcome of each of the `T` periods, either no request (`none`) or one
request of type `k` (`some k`). Period `t ∈ [1, T]` is coordinate `t - 1`. -/
abbrev Path : Type := Fin P.T → Option (Fin P.K)

/-- The outcome of period `t` on the path `ω` (`none` outside `[1, T]`). -/
def outcome (t : ℕ) (ω : P.Path) : Option (Fin P.K) :=
  if h : 1 ≤ t ∧ t ≤ P.T then ω ⟨t - 1, by omega⟩ else none

/-- Realized demand `D^t_k ∈ {0, 1}`: `1` iff a type-`k` request arrives in period `t`. -/
noncomputable def D (t : ℕ) (ω : P.Path) (k : Fin P.K) : ℝ :=
  if P.outcome t ω = some k then 1 else 0

/-- The batch partitions `𝒫_k` of p. 18, given by batch-index functions `β k` and batch counts
`B k`: batch `b` of type `k` is `{t ∈ [1, T] : β k t = b}`. The index starts at `1`, moves up by
`0` or `1` from one period to the next and ends at `B k`, so the batches are adjacent intervals
covering `[1, T]`; each batch holds exactly `m k` periods with `λ^{t,D}_k > 0`. -/
def BatchesValid (m : Fin P.K → ℕ) (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ) : Prop :=
  ∀ k, β k 1 = 1 ∧
    (∀ t, 1 ≤ t → t < P.T → β k (t + 1) = β k t ∨ β k (t + 1) = β k t + 1) ∧
    β k P.T = B k ∧
    ∀ b ∈ Icc 1 (B k), ((Icc 1 P.T).filter (fun t => β k t = b ∧ 0 < P.lamD t k)).card = m k

/-- `C̃_i(t, s)` (p. 18): the number of units of resource `i` available for service at period
`s` at the beginning of period `t`, before the request of period `t` arrives, i.e. `C_i` minus the
units that requests of periods `v ∈ [1, t - 1]` occupy at period `s`. -/
noncomputable def Ctil (t s : ℕ) (ω : P.Path) (i : Fin P.I) : ℝ :=
  (P.C i : ℝ) - ∑ k, ∑ v ∈ (Icc 1 (t - 1)).filter (fun v => v + P.ℓ k ≤ s ∧ s < v + P.ℓ k + P.n k),
    (P.A i k : ℝ) * P.D v ω k

/-- The free capacity at the beginning of period `t`, `C^t = C̃(t, t)`. -/
noncomputable def Ccur (t : ℕ) (ω : P.Path) (i : Fin P.I) : ℝ := P.Ctil t t ω i

/-- `∑_{s ∈ 𝒯_k^{β_k(t) - 1}} Δ^s_k` computed from a given sequence of earlier rates `prev`,
with `Δ^s_k = D^s_k - prev s k`; it is `0` in the first batch (`𝒯_k^0 = ∅`). -/
noncomputable def prevErrWith (β : Fin P.K → ℕ → ℕ) (prev : ℕ → Fin P.K → ℝ) (t : ℕ)
    (ω : P.Path) (k : Fin P.K) : ℝ :=
  ∑ s ∈ (Icc 1 (t - 1)).filter (fun s => β k s + 1 = β k t), (P.D s ω k - prev s k)

/-- Period `t`'s rate vector under DPC-B(m, ϵ) (p. 19, Steps 2b–2c), given the rates `prev` of
the earlier periods. Type `k` gets `Proj_{[0, λ_U]}[λ^{t,D}_k - (ϵ_k/n̲_k + prevErr/m_k)·1{λ^{t,D}_k > 0}]`
if `C̃(t, t + ℓ_k) ⪰ A^k` (tested when the service starts within the horizon, `t + ℓ_k ≤ T`), and
rate `0` (the turn-off price) otherwise. It reads the path only through periods `1, …, t - 1`. -/
noncomputable def stepRate (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (prev : ℕ → Fin P.K → ℝ) (t : ℕ) (ω : P.Path) (k : Fin P.K) : ℝ :=
  if t + P.ℓ k ≤ P.T → ∀ i, (P.A i k : ℝ) ≤ P.Ctil t (t + P.ℓ k) ω i then
    max 0 (min P.lamU (P.lamD t k -
      (ε k / (nl k : ℝ) + P.prevErrWith β prev t ω k / (m k : ℝ)) *
        (if 0 < P.lamD t k then 1 else 0)))
  else 0

/-- The rates of periods `1, …, t` under DPC-B(m, ϵ), built period by period: `ratesUpTo t ω s`
is the rate vector of period `s ≤ t` (and `0` for `s = 0` or `s > t`). -/
noncomputable def ratesUpTo (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (ω : P.Path) : ℕ → ℕ → Fin P.K → ℝ
  | 0 => fun _ _ => 0
  | t + 1 => fun s =>
      if s = t + 1 then P.stepRate nl m ε β (ratesUpTo nl m ε β ω t) (t + 1) ω
      else ratesUpTo nl m ε β ω t s

/-- The DPC-B(m, ϵ) rate vector `λ^t` of period `t` on the path `ω`. -/
noncomputable def rate (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (t : ℕ) (ω : P.Path) : Fin P.K → ℝ :=
  P.ratesUpTo nl m ε β ω t t

/-- The demand error `Δ^t_k = D^t_k - λ^t_k` under DPC-B(m, ϵ). -/
noncomputable def err (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (t : ℕ) (ω : P.Path) (k : Fin P.K) : ℝ :=
  P.D t ω k - P.rate nl m ε β t ω k

/-- `∑_{s ∈ 𝒯_k^{β_k(t) - 1}} Δ^s_k` under DPC-B(m, ϵ). -/
noncomputable def prevErr (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (t : ℕ) (ω : P.Path) (k : Fin P.K) : ℝ :=
  P.prevErrWith β (fun s => P.rate nl m ε β s ω) t ω k

/-- The one-period outcome law under the rate vector `x`: type `k` with probability `x k`, no
request with probability `1 - ∑_k x k`. -/
def outcomeProb (x : Fin P.K → ℝ) : Option (Fin P.K) → ℝ
  | none => 1 - ∑ k, x k
  | some k => x k

/-- The probability of the path `ω` under DPC-B(m, ϵ): independent periods, period `t` drawn from
the outcome law of its rate vector, which depends on the outcomes of periods `1, …, t - 1`. -/
noncomputable def pathProb (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (ω : P.Path) : ℝ :=
  ∏ t ∈ Icc 1 P.T, P.outcomeProb (P.rate nl m ε β t ω) (P.outcome t ω)

/-- Expectation under DPC-B(m, ϵ) of a path functional. -/
noncomputable def expect (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (X : P.Path → ℝ) : ℝ :=
  ∑ ω, P.pathProb nl m ε β ω * X ω

/-- Probability under DPC-B(m, ϵ) of an event of paths. -/
noncomputable def prob (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (E : P.Path → Prop) : ℝ :=
  by classical exact P.expect nl m ε β (fun ω => if E ω then 1 else 0)

/-- The average loss `L(DPC-B(m, ϵ)) = (J^D_H - E[∑_{t=1}^T r^t(λ^t)]) / T` (p. 9 and p. 17). -/
noncomputable def lossB (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ) : ℝ :=
  (P.JD - P.expect nl m ε β (fun ω => ∑ t ∈ Icc 1 P.T, P.r t (P.rate nl m ε β t ω))) / (P.T : ℝ)

/-- `min_k ϵ_k` (for `K ≥ 1`). -/
noncomputable def epsMin (ε : Fin P.K → ℝ) : ℝ := ⨅ k, ε k

end General

end ReusablePricing.DPCB


