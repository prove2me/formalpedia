-- Prove2me | Definitions.Def_ArapostathisAC_CanonicalPolicy_SamplePath
-- name    : ArapostathisAC_CanonicalPolicy_SamplePath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:41:49.67848+00:00
-- url     : https://prove2.me/theorems/608003ec-91bf-4110-83af-c12e4691feab
-- title:
--   Sample path average cost, path measures from an initial law, sample path AC optimality, and Mandl's discrepancy function
-- statement:
--   This file adds the pathwise objects of Theorem 6.3 (v)–(vi) to the controlled Markov process $(S, A, U, P, c)$ of §2.
--
--   **Sample path average cost.** Along a trajectory $\omega = ((x_0, a_0), (x_1, a_1), \dots)$ the running average cost is $\frac1N \sum_{t=0}^{N-1} c(x_t, a_t)$, and the sample path average cost is
--   $$J_S = \limsup_{N\to\infty} \frac1N \sum_{t=0}^{N-1} c(X_t, A_t),$$
--   an extended real-valued random variable on the canonical sample space (pp. 286–287).
--
--   **Initial laws.** For a probability measure $\mu$ on $S$ and a policy $\pi$, $\mathcal P^\pi_\mu$ is the law of the trajectory when $X_0 \sim \mu$, $A_0 \sim \pi_0(\cdot \mid X_0)$, and thereafter the process evolves as under $\mathcal P^\pi_x$.
--
--   **Sample path AC optimality** (p. 288). A policy $\pi^* \in \Pi$ is sample path AC optimal if there is a constant $\rho^*$ such that, for any initial law $\mu$,
--   $$J_S = \rho^* \quad \mathcal P^{\pi^*}_\mu\text{-a.s.},$$
--   while, for any policy $\pi \in \Pi$ and any initial law $\mu'$, $J_S \ge \rho^*$ $\mathcal P^\pi_{\mu'}$-a.s.
--
--   **Mandl's discrepancy function** (p. 318). For a bounded measurable $h$ on $S$ and a constant $\rho^*$,
--   $$\Phi(x, a) = c(x, a) + \int_S h(y)\, P(dy \mid x, a) - \rho^* - h(x).$$
--
--   These objects state the almost-sure parts of Theorem 6.3: the comparison of every policy's pathwise average cost with $\rho^*$, and the pathwise optimality of a canonical policy.
--
--   **Formalization Note.** $J_S$ is a limit superior in `EReal`. Initial laws are probability measures; $\mathcal P^\pi_\mu$ is `Kernel.trajMeasure` started from the law of $(X_0, A_0)$, obtained by composing $\mu$ with the measurable kernel $x \mapsto \delta_x \otimes \pi_0(\cdot\mid x)$, so no junk value of `Measure.map` can occur. The paper writes $J^*_S(\mu, \pi)$ on p. 288 for this random variable; the asterisk carries no further meaning. $\Phi$ is given on all of $S \times A$ and used only on $K$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 286–287 (sample path average cost), p. 288 (sample path AC optimality), p. 318 (Theorem 6.3 (v), Φ)

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The running average cost along a trajectory `ω = ((x₀, a₀), (x₁, a₁), …)`:
`(1/N) ∑_{t=0}^{N-1} c(x_t, a_t)` (with value `0` at `N = 0`). -/
noncomputable def avgPathCost (M : BorelCMP S A) (N : ℕ) (ω : ℕ → S × A) : ℝ :=
  (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, M.c (ω t)

/-- The sample path average cost (pp. 286–287): `J_S = limsup_{N → ∞} (1/N) ∑_{t=0}^{N-1} c(X_t, A_t)`,
an extended real-valued random variable on the canonical sample space `(S × A)^ℕ`. -/
noncomputable def sampleAvgCost (M : BorelCMP S A) (ω : ℕ → S × A) : EReal :=
  limsup (fun N : ℕ => ((avgPathCost M N ω : ℝ) : EReal)) atTop

omit [StandardBorelSpace S] [TopologicalSpace A] [BorelSpace A] in
lemma measurable_initArg :
    Measurable (fun x : S => ((fun j : Fin 0 => j.elim0 : Fin 0 → S × A), x)) :=
  measurable_const.prodMk measurable_id

/-- The kernel giving the law of `(x₀, a₀)` from `x₀`: `x₀` is kept and `a₀ ∼ π₀(· | x₀)`. -/
noncomputable def initKernel {M : BorelCMP S A} (π : Policy M) : Kernel S (S × A) :=
  Kernel.deterministic id measurable_id ×ₖ
    (π.rule 0).comap (fun x : S => ((fun j : Fin 0 => j.elim0 : Fin 0 → S × A), x))
      measurable_initArg

/-- The probability measure `𝒫^π_μ` (p. 285) on trajectories `ω = ((x₀, a₀), (x₁, a₁), …)` for an
initial law `μ` of `X₀`, given by the Ionescu-Tulcea theorem: `x₀ ∼ μ`, `a₀ ∼ π₀(· | x₀)`, and
then the step kernel of `pathMeasure`. -/
noncomputable def pathLaw (M : BorelCMP S A) (π : Policy M) (μ : Measure S) :
    Measure (ℕ → S × A) :=
  Kernel.trajMeasure (X := fun _ => S × A) (initKernel π ∘ₘ μ) (stepKernel M π)

/-- Sample path AC optimality (p. 288): there is a constant `ρ*` such that, for every initial law
`μ`, `J_S = ρ*` `𝒫^{π*}_μ`-a.s., while for every policy `π ∈ Π` and every initial law `μ'`,
`J_S ≥ ρ*` `𝒫^π_{μ'}`-a.s. Initial laws are probability measures on `S`. -/
def IsSamplePathOptimal (M : BorelCMP S A) (πs : Policy M) : Prop :=
  ∃ ρs : ℝ,
    (∀ μ : Measure S, IsProbabilityMeasure μ →
      ∀ᵐ ω ∂(pathLaw M πs μ), sampleAvgCost M ω = (ρs : EReal)) ∧
    (∀ (π : Policy M) (μ : Measure S), IsProbabilityMeasure μ →
      ∀ᵐ ω ∂(pathLaw M π μ), (ρs : EReal) ≤ sampleAvgCost M ω)

/-- Mandl's discrepancy function (p. 318, Theorem 6.3 (v)):
`Φ(x, a) = c(x, a) + ∫ h(y) P(dy | x, a) - ρ* - h(x)`. -/
noncomputable def mandl (M : BorelCMP S A) (h : S → ℝ) (ρs : ℝ) (p : S × A) : ℝ :=
  M.c p + ∫ y, h y ∂(M.P p) - ρs - h p.1

end ArapostathisAC.CanonicalPolicy


