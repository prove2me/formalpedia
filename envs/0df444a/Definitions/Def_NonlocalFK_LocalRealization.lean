-- Prove2me | Definitions.Def_NonlocalFK_LocalRealization
-- name    : NonlocalFK_LocalRealization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:09.686284+00:00
-- url     : https://prove2.me/theorems/72f5579a-cf79-464f-ac1b-4bf697319a0e
-- title:
--   The diffusion (A.4) and the payoff of (A.3)
-- statement:
--   A **realization of the diffusion** from $(t,x)$ consists of a filtered probability space, a $d$-dimensional $\mathcal F$-Brownian motion $B$ and an adapted continuous process $\xi$ on $[t,T]$ with $\xi_t=x$ and
--
--   $$
--   d\xi_s=b(s,\xi_s)\,ds+\sigma(s,\xi_s)\,dB_s .
--   $$
--
--   With $\tau$ the first time $\xi$ hits $\partial\mathcal O$, the module defines $\tau\wedge T$ and the functional
--
--   $$
--   \int_t^{\tau\wedge T}e^{-r(s-t)}f(s,\xi_s)\,ds+e^{-r((\tau\wedge T)-t)}g(\tau\wedge T,\xi_{\tau\wedge T})
--   $$
--
--   of the Feynman–Kac representation for the local problem.
--
--   **Formalization Note** The stochastic integrals are the local Itô integrals `HasItoIntegral`, coordinate by coordinate. $\tau$ need not exist on $[t,T]$, so $\tau\wedge T$ is the infimum of the hitting times in $[t,T]$ together with $T$.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, Proposition A.1, eq. (A.3)-(A.4), p.23

import Definitions.Def_NonlocalFK_Diffusion
import Definitions.Def_NonlocalFK_IsBrownianFamily

open MeasureTheory Set

noncomputable section

namespace NonlocalFK

/-- A realization of the diffusion `ξ` of Proposition A.1 (Dai, Kou, Yang, SSRN 3541591, p.23): it
starts from `x` at time `t` and follows (A.4), `dξ_s = b(s, ξ_s)ds + σ(s, ξ_s)dB_s`, on `[t, T]`,
with a `d`-dimensional `𝓕`-Brownian motion `B`.

**Formalization Note.** The stochastic integrals are the local Itô integrals
`EntropyMFG.Enhanced.HasItoIntegral`, coordinate by coordinate. The realization is a weak one: the
probability space is part of the data. -/
structure LocalRealization {d : ℕ} (c : Diffusion d) (t : ℝ) (x : E d)
    (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  P : Measure Ω
  F : Filtration ℝ mΩ
  B : Fin d → ℝ → Ω → ℝ
  ξ : ℝ → Ω → E d
  brownian : IsBrownianFamily P F B
  adapted : ∀ s ∈ Icc t c.T, Measurable[F s] (ξ s)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun s => ξ s ω) (Icc t c.T)
  start : ∀ᵐ ω ∂P, ξ t ω = x
  sde : ∃ J : Fin d → Fin d → ℝ → Ω → ℝ,
    (∀ k j, EntropyMFG.Enhanced.HasItoIntegral P F (B j) t c.T
      (fun s ω => c.σ (s, ξ s ω) k j) (J k j)) ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t c.T, ∀ k,
      ξ s ω k = x k + (∫ u in t..s, c.b (u, ξ u ω) k) + ∑ j, J k j s ω

namespace LocalRealization

variable {d : ℕ} {c : Diffusion d} {t : ℝ} {x : E d} {Ω : Type*} [MeasurableSpace Ω]
  (R : LocalRealization c t x Ω)

/-- The time `τ ∧ T`, with `τ` the first time `ξ` hits `∂𝒪` (SSRN 3541591, p.23).

**Formalization Note.** `τ` need not exist on `[t, T]`, so `τ ∧ T` is written directly as the
infimum of the hitting times in `[t, T]` together with `T`. That set is nonempty and bounded below. -/
def exitTime (ω : Ω) : ℝ := sInf ({s | s ∈ Icc t c.T ∧ R.ξ s ω ∈ frontier c.O} ∪ {c.T})

/-- The functional inside the expectation of (A.3), p.23:
`∫_t^{τ∧T} e^{−r(s−t)} f(s, ξ_s) ds + e^{−r((τ∧T)−t)} g(τ∧T, ξ_{τ∧T})`. -/
def payoff (g : ℝ × E d → ℝ) (ω : Ω) : ℝ :=
  (∫ s in t..R.exitTime ω, Real.exp (-c.r * (s - t)) * c.f (s, R.ξ s ω)) +
    Real.exp (-c.r * (R.exitTime ω - t)) * g (R.exitTime ω, R.ξ (R.exitTime ω) ω)

end LocalRealization

end NonlocalFK


