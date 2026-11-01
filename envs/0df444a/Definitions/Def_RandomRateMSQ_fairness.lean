-- Prove2me | Definitions.Def_RandomRateMSQ_fairness
-- name    : RandomRateMSQ_fairness
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:27:22.456719+00:00
-- url     : https://prove2.me/theorems/a8b47e97-a1e6-47ee-8989-19b06a09b6cc
-- title:
--   The fairness process $\eta^n$, the times $\tau^n_\varepsilon$, the shifts $S^n_\varepsilon\eta^n$, Assumption 3
-- statement:
--   For $\varepsilon\ge0$, $\tau^n_\varepsilon=\inf\{t:\int_0^t\hat I^n(s)\,ds>\varepsilon\}\in[0,\infty]$ (with $\inf\emptyset=\infty$). The **fairness process** is the probability measure on $\mathbb R_+$
--
--   $$
--   \eta^n_t(A)=\begin{cases}\dfrac{\int_0^t\sum_k\delta_{\tilde\mu^n_k}(A)\,I^n_k(s)\,ds}{\int_0^t\sum_kI^n_k(s)\,ds}, & t>\tau^n_0,\\[2mm] \zeta(A), & t\le\tau^n_0,\end{cases}
--   $$
--
--   the share of the idleness up to $t$ that fell on servers with rate in $A$; $\zeta$ is a fixed placeholder. Its **$\varepsilon$-shift** is $S^n_\varepsilon\eta^n_t=\eta^n_t$ if $t>\tau^n_\varepsilon$ and $\zeta$ otherwise (3.4); the same shift with a limit time $\tau_\varepsilon$ and a limit process $\eta$ is $S_\varepsilon\eta$ of Definition 1.
--
--   **Assumption 3.** For all $\rho,\varrho>0$ and $T>0$ there is $M$ with
--
--   $$
--   \liminf_{n\to\infty}P\Big(\int_M^\infty\mu\,d\eta^n_t(\mu)<\varrho\ \text{for all }t\in[0,T]\Big)>1-\rho .
--   $$
--
--   The fairness process records how the total idleness is shared among servers of different speeds; its mean enters the limit equation.
--
--   **Formalization Note** The ratio is the normalization of the finite measure $\sum_k\big(\int_0^tI^n_k\big)\delta_{\tilde\mu^n_k}$, positive for $t>\tau^n_0$. The tail integral in Assumption 3 is a lower Lebesgue integral in $[0,\infty]$ and the lim inf is taken in $[0,\infty]$ against $\max(1-\rho,0)$, which over all $\rho>0$ is the printed condition. Assumption 3 at $t=0$ forces $\zeta$ to have a finite mean.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, §3.2, pp.9–10 (τⁿ_ε, (3.4), Definition 1, Assumption 3)

import Mathlib
import Definitions.Def_RandomRateMSQ_Scaled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

variable {Ω : Type*} {n : ℕ}

/-- The scaled cumulative idleness `∫₀ᵗ Îⁿ(s) ds`. -/
noncomputable def cumIhat (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ := cumInt (Ihat s ω) t

/-- The random time `τⁿ_ε := inf{t : ∫₀ᵗ Îⁿ(s) ds > ε}` (Büke–Qin, arXiv:1905.04198v1, p.9).

**Formalization Note.** Computed in `ℝ≥0∞`, so `inf ∅ = ∞` (never a junk `0`). -/
noncomputable def tau (s : System Ω n) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ε < cumIhat s ω t), (t : ℝ≥0∞)

/-- The Dirac mass at `x`, as a finite measure on `ℝ₊`. -/
noncomputable def diracFM (x : ℝ≥0) : FiniteMeasure ℝ≥0 := ⟨Measure.dirac x, inferInstance⟩

/-- The cumulative idleness measure `A ↦ Σₖ δ_{µ̃ⁿₖ}(A) ∫₀ᵗ Iⁿₖ(s) ds` on `ℝ₊` (the numerator of
(3.4), arXiv:1905.04198v1, p.9), a finite sum of Dirac masses at the servers' rates weighted by
their cumulative idle times. -/
noncomputable def idleMeasure (s : System Ω n) (ω : Ω) (t : ℝ≥0) : FiniteMeasure ℝ≥0 :=
  ∑ k, (Real.toNNReal (cumInt (fun r => (s.I k ω r : ℝ)) t)) • diracFM (s.rate k ω)

/-- The **fairness process** (3.4) (arXiv:1905.04198v1, p.9):
`ηⁿₜ(A) = (∫₀ᵗ Σₖ δ_{µ̃ⁿₖ}(A) Iⁿₖ(s) ds)/(∫₀ᵗ Σₖ Iⁿₖ(s) ds)` if `t > τⁿ₀`, and `ηⁿₜ = ζ` (the
placeholder) if `t ≤ τⁿ₀`: the share of the idleness up to `t` that fell on servers with rate in
`A`.

**Formalization Note.** The ratio is `FiniteMeasure.normalize` of `idleMeasure`. For `t > τⁿ₀` the
total mass `Σₖ ∫₀ᵗ Iⁿₖ` is positive, so the normalization is the printed ratio. -/
noncomputable def fairness (ζ : ProbabilityMeasure ℝ≥0) (s : System Ω n) (ω : Ω) (t : ℝ≥0) :
    ProbabilityMeasure ℝ≥0 :=
  if tau s 0 ω < (t : ℝ≥0∞) then (idleMeasure s ω t).normalize else ζ

/-- The **shift** of (3.4) (arXiv:1905.04198v1, p.10): `(S η)ₜ = ηₜ` if `t > τ` and `ζ` if
`t ≤ τ`. With `τ = τⁿ_ε` and `η = ηⁿ` it is `Sⁿ_ε ηⁿ`; with the limit `τ_ε` and the limit `η` it is
Definition 1's `S_ε η` ("define S_ε η by replacing τⁿ_ε with τ_ε in (3.4)"). -/
noncomputable def shift (ζ : ProbabilityMeasure ℝ≥0) (τ : ℝ≥0∞)
    (η : ℝ≥0 → ProbabilityMeasure ℝ≥0) (t : ℝ≥0) : ProbabilityMeasure ℝ≥0 :=
  if τ < (t : ℝ≥0∞) then η t else ζ

/-- The `ε`-shifted fairness process `Sⁿ_ε ηⁿ` (3.4) (arXiv:1905.04198v1, p.10). -/
noncomputable def shiftedFairness (ζ : ProbabilityMeasure ℝ≥0) (s : System Ω n) (ε : ℝ)
    (ω : Ω) : ℝ≥0 → ProbabilityMeasure ℝ≥0 :=
  shift ζ (tau s ε ω) (fairness ζ s ω)

/-- **Assumption 3** (arXiv:1905.04198v1, p.10): "For any given ρ, ϱ > 0 and T > 0, there exists
an M such that lim inf_{n→∞} P(∫_M^∞ µ dηⁿₜ(µ) < ϱ, for all t ∈ [0, T]) > 1 − ρ."

**Formalization Note.** The tail integral `∫_{[M,∞)} µ dηⁿₜ` is a lower Lebesgue integral in
`[0, ∞]`, so an infinite tail is never a junk `0`; the `lim inf` of the probabilities is taken in
`[0, ∞]` and compared with `max(1 − ρ, 0)` (for `ρ ≥ 1` this asks for a positive `lim inf`, which
the case `ρ = 1/2` already provides, so the assumption is the printed one). Since `ηⁿ₀ = ζ`, the
assumption forces `ζ` to have a finite mean. -/
def Assumption3 [MeasurableSpace Ω] (P : Measure Ω) (ζ : ProbabilityMeasure ℝ≥0)
    (sys : ∀ n, System Ω n) : Prop :=
  ∀ ρ ϱ : ℝ, 0 < ρ → 0 < ϱ → ∀ T : ℝ≥0, 0 < T → ∃ M : ℝ≥0,
    ENNReal.ofReal (1 - ρ) < liminf (fun n => P {ω | ∀ t : ℝ≥0, t ≤ T →
      ∫⁻ x in Set.Ici M, (x : ℝ≥0∞) ∂(fairness ζ (sys n) ω t : Measure ℝ≥0) < ENNReal.ofReal ϱ})
      atTop

end RandomRateMSQ


