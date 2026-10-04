-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_WaitModel
-- name    : DimCallCenters_Rationalized_WaitModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:49.31706+00:00
-- url     : https://prove2.me/theorems/dc24a212-3747-4956-a719-28d6583cee8f
-- title:
--   Standing assumptions of Section 2: service rate $\mu$ and waiting-cost functions $D_\lambda$
-- statement:
--   The M/M/N cost model of Borst, Mandelbaum and Reiman has a fixed **service rate** $\mu > 0$ and, for every arrival rate $\lambda > 0$, a **waiting-cost function** $D_\lambda : [0,\infty) \to \mathbb R$: a customer who waits $t$ time units costs $D_\lambda(t)$. The standing assumptions of Section 2 are
--
--   1. $D_\lambda(0) = 0$;
--   2. $D_\lambda$ is strictly increasing on $[0,\infty)$;
--   3. the conditional expected waiting cost $G(N,\lambda)$ is finite for every $N > \lambda/\mu$, i.e. for every $\theta > 0$ the function $t \mapsto D_\lambda(t)\,e^{-\theta t}$ is integrable on $(0,\infty)$.
--
--   A `WaitModel` packages $\mu$, the family $(D_\lambda)_{\lambda>0}$ and these three properties. Every theorem of the mission is stated for an arbitrary such model.
--
--   **Formalization Note** The waiting time itself (Poisson arrivals, exponential service) is not modelled: the paper's analysis only uses the closed-form cost. Finiteness of $G$ is encoded as integrability, because a Lean Bochner integral of a non-integrable function is $0$. The values $D_\lambda$ for $\lambda \le 0$ and $D_\lambda(t)$ for $t < 0$ are unconstrained and never used.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), pp. 10-11, Section 2 (standing assumptions on mu and D_lambda)

import Mathlib

namespace DimCallCenters.Rationalized

/-- The standing assumptions of Section 2 (pp. 10–11) on the service rate and the waiting-cost
functions: `μ > 0` is fixed; for every arrival rate `lam > 0`, `D lam = D_λ` vanishes at `0`, is
strictly increasing on `[0, ∞)`, and `t ↦ D_λ(t) e^{-θ t}` is integrable on `(0, ∞)` for every
`θ > 0` (the paper's "G(N, λ) is finite for all λ/μ < N"). -/
structure WaitModel where
  μ : ℝ
  hμ : 0 < μ
  D : ℝ → ℝ → ℝ
  hD0 : ∀ lam : ℝ, 0 < lam → D lam 0 = 0
  hDmono : ∀ lam : ℝ, 0 < lam → StrictMonoOn (D lam) (Set.Ici 0)
  hDint : ∀ lam : ℝ, 0 < lam → ∀ θ : ℝ, 0 < θ →
    MeasureTheory.IntegrableOn (fun t => D lam t * Real.exp (-θ * t)) (Set.Ioi 0)

end DimCallCenters.Rationalized


