-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_IsJumpHoldCTMC
-- name    : ProcessingNetworks_MArP_IsJumpHoldCTMC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:58.687092+00:00
-- url     : https://prove2.me/theorems/e2639e64-fe94-4194-af1a-ec1fd2e020de
-- title:
--   The continuous-time Markov chain constructed from its jump chain and exponential clocks ((D.5)–(D.6))
-- statement:
--   Let $\Lambda$ be a generator with jump matrix $G$, and $\rho$ a distribution on $\mathcal S$. The process $X$ is the **continuous-time Markov chain** with initial distribution $\rho$ and generator $\Lambda$, constructed from $(Y,\tau)$, if
--
--   1. $Y=\{Y_n\}$ is a discrete-time Markov chain with initial distribution $\rho$ and transition matrix $G$;
--   2. $\tau_0,\tau_1,\dots$ are i.i.d. exponential random variables with mean $1$, independent of $Y$;
--   3. with $\sigma_0=0$ and $\sigma_{n+1}=\sigma_n+\tau_n/\lambda(Y_n)$, one has $X(t)=Y_n$ for $\sigma_n\le t<\sigma_{n+1}$, almost surely.
--
--   The book states that whenever a CTMC is mentioned, it is envisioned to be constructed in this way.
--
--   **Formalization Note** Non-explosion ($\sigma_n\to\infty$) is not part of this predicate. It is the regularity hypothesis of Appendix D and is automatic on a finite state space, so theorems on a general countable space take it as a separate almost-sure hypothesis. This predicate does not use the published structure `ProcessingNetworks.Stability.MarkovRepresentation`, which also carries fields of a processing network and every-path non-explosion. Times are real numbers and only $t\ge 0$ is constrained.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section D.2, eqs. (D.5)–(D.6), pp.288–289 (PDF pp.304–305); p.290 (PDF p.306)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_MArP_IsDTMC
import Definitions.Def_ProcessingNetworks_MArP_jumpMatrix

open MeasureTheory ProbabilityTheory

namespace ProcessingNetworks.MArP

/-- `X` is the continuous-time Markov chain with generator `Λ` and initial distribution `ρ`,
constructed from a jump chain `Y` and clocks `τ` as in (D.5)–(D.6) (Dai & Harrison, Processing
Networks, pre-publication draft 2020-4-2, Section D.2, pp.288–289, PDF pp.304–305; p.290, PDF p.306:
"Whenever a CTMC `X` is mentioned, without loss of generality we envision `X` to be constructed as in
(D.5)"). `Y` is a DTMC with initial distribution `ρ` and transition matrix the jump matrix `G`,
`τ₀, τ₁, …` are i.i.d. exponential with mean 1 and independent of `Y`, `σ₀ = 0`,
`σ_{n+1} = σ_n + τ_n / λ(Y_n)` (`ProcessingNetworks.Stability.jumpTime`), and `X(t) = Y_n` for
`σ_n ≤ t < σ_{n+1}`.

**Formalization Note.** Non-explosion is not a field. Definition D.2 is a property of `Λ`, assumed
through "regular" in Appendix D and automatic for a finite state space, so theorems on a general `S`
take the hypothesis that `σ_n → ∞` almost surely. The sample-path identity holds on an event of full
probability, since a clock is positive only almost surely. This predicate deliberately avoids the
published structure `ProcessingNetworks.Stability.MarkovRepresentation`, which bundles fields of a
stochastic processing network and every-path non-explosion. `X` is indexed by `ℝ`; only `t ≥ 0` is
constrained. -/
structure IsJumpHoldCTMC {S Ω : Type*} [MeasurableSpace S] [MeasureSpace Ω] {Λ : S → S → ℝ}
    (hΛ : IsGenerator Λ) (ρ : PMF S) (Y : ℕ → Ω → S) (τ : ℕ → Ω → ℝ) (X : ℝ → Ω → S) : Prop where
  jump_chain : IsDTMC (jumpMatrix hΛ) ρ Y
  clock_measurable : ∀ n, Measurable (τ n)
  clock_exp : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ℙ {ω | s < τ n ω} = ENNReal.ofReal (Real.exp (-s))
  clock_iid : iIndepFun τ ℙ
  clock_indep_jump_chain :
    Indep (MeasurableSpace.comap (fun ω n => τ n ω) inferInstance)
      (MeasurableSpace.comap (fun ω n => Y n ω) inferInstance) ℙ
  sample_path : ∀ᵐ ω, ∀ (n : ℕ) (t : ℝ),
    ProcessingNetworks.Stability.jumpTime (exitRate Λ) Y τ n ω ≤ t →
      t < ProcessingNetworks.Stability.jumpTime (exitRate Λ) Y τ (n + 1) ω → X t ω = Y n ω

end ProcessingNetworks.MArP


