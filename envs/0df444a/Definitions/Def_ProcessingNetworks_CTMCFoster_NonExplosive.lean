-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_NonExplosive
-- name    : ProcessingNetworks_CTMCFoster_NonExplosive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:42.800405+00:00
-- url     : https://prove2.me/theorems/b3467519-5cbf-4a5e-8795-ab1b2ddae574
-- title:
--   Non-explosion of a generator (Definition D.2)
-- statement:
--   Let $G$ be a jump matrix and $\lambda$ the exit rates on a countable set $\mathscr S$. In the sample-path construction of a continuous-time Markov chain, $Y=(Y_n)$ is a discrete-time chain with transition matrix $G$, the $\tau_n$ are i.i.d. exponential clocks of mean one, independent of $Y$, and
--
--   $$
--   \sigma_0=0,\qquad \sigma_{n+1}=\sigma_n+\tau_n/\lambda(Y_n).
--   $$
--
--   The chain is **non-explosive** if, for each state $i$,
--
--   $$
--   \mathbb P_i\{\sigma_\infty=\infty\}=1,\qquad \sigma_\infty=\lim_{n\to\infty}\sigma_n.
--   $$
--
--   A generator is regular when it satisfies (D.2) and is non-explosive; the book assumes regularity from this point on, and Theorem D.17 depends on it.
--
--   **Formalization Note** The property is stated for every realization of the construction on a probability space. The conclusion is almost sure, not on every path. Measurability of the events $\{Y_n=x\}$ and of the clocks is part of "a realization", and independence is between $\sigma(\tau_n:n\ge0)$ and $\sigma(Y_n:n\ge0)$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition D.2, eq. (D.7), p.289 (PDF 305), with (D.5)–(D.6), pp.288–289 (PDF 304–305)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.CTMCFoster

open MeasureTheory ProbabilityTheory Filter

/-- Non-explosion (Definition D.2): `P_i {σ_∞ = ∞} = 1` for each state `i`, where `σ_n` are the
jump times of the sample-path construction (D.5)–(D.6). The construction is taken on an arbitrary
probability space: `Y` is a discrete-time Markov chain with transition matrix `jump` started at
`i`, the clocks `τ_n` are i.i.d. unit-mean exponential and independent of `Y`, and
`σ_{n+1} = σ_n + τ_n / λ(Y_n)`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition D.2,
eq. (D.7), p.289 (PDF 305), with (D.5)–(D.6), pp.288–289 (PDF 304–305).

**Formalization Note** The conclusion is almost sure, as (D.7) says, not on every path as in the
field `nonexplosive` of `Stability.MarkovRepresentation`; the Reuter-type criterion
`∑ₙ 1/λ(Yₙ) = ∞` is not used. Independence is stated between `σ(τ_n : n)` and `σ(Y_n : n)`. The
probability space ranges over `Type`, which loses nothing: the law of `(Y, τ)` is determined and is
realized on a space in `Type`. -/
def NonExplosive {S : Type*} (jump : S → PMF S) (rate : S → ℝ) : Prop :=
  ∀ (i : S) (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℕ → Ω → S) (clock : ℕ → Ω → ℝ),
    (∀ (n : ℕ) (x : S), MeasurableSet {ω | Y n ω = x}) →
    (∀ n : ℕ, Measurable (clock n)) →
    Stability.IsJumpChain jump Y →
    (∀ᵐ ω, Y 0 ω = i) →
    (∀ (n : ℕ) (s : ℝ), 0 ≤ s → ℙ {ω | s < clock n ω} = ENNReal.ofReal (Real.exp (-s))) →
    iIndepFun clock ℙ →
    Indep (⨆ n, MeasurableSpace.comap (clock n) inferInstance)
      (⨆ n, MeasurableSpace.comap (Y n) ⊤) ℙ →
    ∀ᵐ ω, Tendsto (fun n => Stability.jumpTime rate Y clock n ω) atTop atTop

end ProcessingNetworks.CTMCFoster


