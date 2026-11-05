-- Prove2me | Definitions.Def_CondBasedProd_Policy
-- name    : CondBasedProd_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:52.181321+00:00
-- url     : https://prove2.me/theorems/caa8f12d-4e47-4885-9361-6b52e8685c28
-- title:
--   Production policies, expected profit $J^u_\lambda$ (1), optimal profit $J^*_\lambda$ and marginal value $\Delta_\lambda$
-- statement:
--   A **production policy** $u$ is a measurable rule $\varphi$: after $j$ deterioration increments at times $\tau$, the production rate at elapsed time $v$ is $\varphi(j,v,\tau)\in[0,\bar s]$. From level $x$ the system uses $\xi-x$ exponential clocks, so deterioration stops at $\xi$, and under base rate $\lambda$ the increments have intensity $\lambda f(\varphi)$. The rate in force is $\varphi(j,v,\tau)$ for $\tau_j<v\le\tau_{j+1}$, and $0$ once the system has failed.
--
--   The expected profit from level $x$ with time $t$ to maintenance, display (1), is
--   $$
--   J^u_\lambda(x,t)=\mathbb E\Bigl[\int_0^t r(s_v)\,dv-c_m(x+N_t)\Bigr],
--   $$
--   where $N_t$ is the number of increments by elapsed time $t$. Then
--   $$
--   J^*_\lambda(x,t)=\sup_{u}J^u_\lambda(x,t),\qquad \Delta_\lambda(x,t)=J^*_\lambda(x,t)-J^*_\lambda(x+1,t).
--   $$
--   $\Delta_\lambda(x,t)$ is the marginal value of one level less deterioration, read for $x<\xi$ only.
--
--   **Formalization Note** Time in the source counts backward ($t$ is the time to maintenance); here the process runs in elapsed time $v=t-k$. A failed system runs at $s=0$ and keeps earning $r(0)$ until maintenance, since the integral in (1) covers the whole horizon. Integrability of the profit and boundedness of the supremum are true facts asserted in the milestone for Lemma 1.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, §3, display (1), pp.9–10; App. A.1, p.34

import Mathlib
import Definitions.Def_CondBasedProd_Model
import Definitions.Def_CondBasedProd_CountingProcess

open MeasureTheory Set
open scoped ENNReal
open GVRPricing.FixedPrice (clockLaw lastTime)

namespace CondBasedProd

/-- A **non-anticipating production policy** `u ∈ 𝒰` (arXiv:2308.07507v2, p.9), in **elapsed time**
`v = t − k`: `φ j v τ` is the production rate at elapsed time `v` after `j` deterioration increments
at times `τ`.

**Formalization Note.** `t` in the paper is the time to maintenance (backward); the process is built
in elapsed time. A policy is a deterministic measurable rule of the past increment times, reading
the "non-anticipating" of p.9 for the internal history (randomized rules are not included). The
constraint `∫_{k=0}^t dY_k ≤ ξ − X_t` is not a field: it is built into the process, which uses
exactly `ξ − x` clocks from the start level `x`. -/
structure Policy (M : Model) where
  /-- The rate rule. -/
  φ : (j : ℕ) → ℝ → (Fin j → ℝ) → ℝ
  measurable : ∀ j, Measurable (fun q : ℝ × (Fin j → ℝ) => φ j q.1 q.2)
  mem : ∀ j v τ, φ j v τ ∈ Icc 0 M.sbar

namespace Policy

variable {M : Model}

/-- The deterioration intensity `λ f(s)` under `u` at base rate `lam`. -/
def intensity (u : Policy M) (lam : ℝ) : IntensityRule :=
  fun j v τ => lam * M.f (u.φ j v τ)

open Classical in
/-- The production rate in force at elapsed time `v`, when `n` increments remain before failure:
`φ j v (τ₁,…,τ_j)` for `τ_j < v ≤ τ_{j+1}`, `j < n`, and `0` once all `n` increments have occurred. -/
noncomputable def rateAt (u : Policy M) (lam : ℝ) (n : ℕ) (E : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (CountingProcess.history (u.intensity lam) E j).elim 0 fun τ =>
    if lastTime j τ < v ∧
        ((v : ℝ) : WithTop ℝ) ≤ CountingProcess.eventTime (u.intensity lam) E (j + 1) then
      u.φ j v τ
    else 0

end Policy

/-- The realized profit `∫₀ᵗ r(s_v) dv − c_m(X_0)` inside (1) (arXiv:2308.07507v2, p.10), from the
start level `x` with `t` time to maintenance, for clock values `E`.

**Formalization Note.** The failed state runs at `s = 0` and keeps earning `r(0)` until maintenance:
the integral of (1) runs over the whole horizon and is not stopped at failure ("the only admissible
action is `s = 0`", App. A.1, p.34). -/
noncomputable def profit (M : Model) (lam : ℝ) (u : Policy M) (x : ℕ) (t : ℝ) (E : ℕ → ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..t, M.r (u.rateAt lam (M.ξ - x) E v)) -
    M.cm (x + CountingProcess.eventsBy (u.intensity lam) (M.ξ - x) t E)

/-- `J^u_λ(x,t)`, display (1), p.10: the expected profit under `u`. The increments are driven by
i.i.d. `Exp(1)` clocks, the published `GVRPricing.FixedPrice.clockLaw`. -/
noncomputable def value (M : Model) (lam : ℝ) (u : Policy M) (x : ℕ) (t : ℝ) : ℝ :=
  ∫ E, profit M lam u x t E ∂clockLaw

/-- `J*_λ(x,t) = sup_{u ∈ 𝒰} J^u_λ(x,t)`, p.10.

**Formalization Note.** Every `t ≥ 0` is covered, so the horizon `T` of the paper needs no
parameter. Bochner integrability of the profit and boundedness of this supremum are true facts,
asserted by `CondBasedProd.lemma_1`. -/
noncomputable def optValue (M : Model) (lam : ℝ) (x : ℕ) (t : ℝ) : ℝ :=
  ⨆ u : Policy M, value M lam u x t

/-- `Δ_λ(x,t) = J*_λ(x,t) − J*_λ(x+1,t)`, p.10. It is read only for `x < ξ`. -/
noncomputable def delta (M : Model) (lam : ℝ) (x : ℕ) (t : ℝ) : ℝ :=
  optValue M lam x t - optValue M lam (x + 1) t

end CondBasedProd


