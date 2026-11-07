-- Prove2me | Definitions.Def_OMSRArbitrary_Duals
-- name    : OMSRArbitrary_Duals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:59.539252+00:00
-- url     : https://prove2.me/theorems/139b9dd2-4f62-43a5-9964-fc90077d7c77
-- title:
--   The candidate dual $(\lambda_t,\theta_i)$ and the per-seed inequality (7)
-- statement:
--   Initialise all duals to $0$. If PG$(u)$ probes $(k,t)$ on thresholds $z$, set
--   $$\lambda_t=r_k(1-g(u_k))\,\mathbf 1\{z_t\le p_{kt}\},\qquad \theta_k\mathrel{+}=r_kg(u_k)\,\mathbf 1\{z_t\le p_{kt}\}.$$
--
--   For a resource $i$, a seed vector $u=(u_i,u_{-i})$, a target $\gamma$, numbers $\pi_t$ and a deterministic policy in the role of OPT with probe set $O_i$, the **per-seed inequality (7)** is
--   $$\mathbb E\Big[\sum_{t\in O_i}\lambda_t+\theta_i\,\Big|\,u_i,u_{-i}\Big]\ \ge\ r_i\,\mathbb E\Big[\sum_{t\in O_i}\mathbf 1\{z_t\le p_{it}\}\,\gamma(u_i,\pi_t)\,\Big|\,u_i,u_{-i}\Big],$$
--   the expectations being over $z$.
--
--   **Formalization Note** The two expectations of (7) are Lebesgue integrals with values in $[0,\infty]$ of the nonnegative integrands, at the fixed seed vector.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §3.1 (Candidate Dual Solution, Per-Seed Inequality), pp.13–14, eq. (7)

import Mathlib
import Definitions.Def_OMSRArbitrary_Policies

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw DetPolicy)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

/-- **The arrival dual** `λ_t`, arXiv:2611.03598, §3.1 ("Candidate Dual Solution"), p.13: if PG(u)
probes `(k, t)`, `λ_t := r_k(1 − g(u_k)) 1{z_t ≤ p_{kt}}`; `λ_t := 0` if it probes nothing at `t`.
Here PG(u) is the run with seeds `u` from all resources, on thresholds `z`. -/
def lam (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (z : Seeds m) (t : Fin m) : ℝ :=
  match pgProbe D g u Finset.univ 0 (corrOutcome D z) t with
  | some k => D.reward k * (1 - g (u k)) * (if z t ≤ D.probability (k, t) then 1 else 0)
  | none => 0

open Classical in
/-- **The resource dual** `θ_i`, arXiv:2611.03598, §3.1, p.13: each probe of `(i, t)` by PG(u)
adds `r_i g(u_i) 1{z_t ≤ p_{it}}` to `θ_i`. -/
def theta (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (z : Seeds m) (i : Fin n) : ℝ :=
  ∑ t : Fin m,
    if pgProbe D g u Finset.univ 0 (corrOutcome D z) t = some i ∧ z t ≤ D.probability (i, t)
    then D.reward i * g (u i) else 0

/-- **The per-seed inequality (7)**, arXiv:2611.03598, §3.1, p.14, for resource `i`, the seed
vector `u = (u_i, u_{−i})`, a target `γ`, numbers `π_t` (given as `πt i u z t`) and a
deterministic policy `π` in the role of OPT:
`E[∑_{t∈O_i} λ_t + θ_i | u_i = u, u_{−i}] ≥ r_i E[∑_{t∈O_i} 1{z_t ≤ p_{it}} γ(u, π_t) | u_i = u, u_{−i}]`,
the expectations being over `z` with all seeds fixed.

**Formalization Note.** Both expectations are Lebesgue integrals `∫⁻` over `z ∼ seedLaw m` of the
nonnegative integrands (`ENNReal.ofReal`), so that the right side keeps its value even when it
is `+∞` (a generic `γ` need not be bounded); "conditional on the seeds" is the integral at the
fixed seed vector `u`. -/
def PerSeedInequality (D : Instance n m) (g : ℝ → ℝ) (γ : ℝ → ℝ → ℝ)
    (πt : Fin n → Seeds n → Seeds m → Fin m → ℝ) (π : DetPolicy n m) (i : Fin n)
    (u : Seeds n) : Prop :=
  ∫⁻ z, ENNReal.ofReal (D.reward i * ∑ t ∈ optProbeSet D π z i,
      (if z t ≤ D.probability (i, t) then γ (u i) (πt i u z t) else 0)) ∂seedLaw m ≤
    ∫⁻ z, ENNReal.ofReal ((∑ t ∈ optProbeSet D π z i, lam D g u z t) + theta D g u z i)
      ∂seedLaw m

end OMSRArbitrary


