-- Prove2me | Definitions.Def_SwitchOptStop_Boundary_Basics
-- name    : SwitchOptStop_Boundary_Basics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:12.916037+00:00
-- url     : https://prove2.me/theorems/34185dbb-e9bf-40d5-896b-6824e04f5185
-- title:
--   Two-state Markov chain with generator Q, 𝔽-Brownian motion, and the EReal optimal stopping value inf_τ E∫₀^τ c_t dt
-- statement:
--   General objects used by the switching-diffusion optimal stopping problem of Ernst and Mei.
--
--   1. **Two-state chain.** For a generator $Q=(q_{\iota\kappa})$ on the states $\{1,2\}$ with jump rates $r_1=q_{12}$, $r_2=q_{21}$, the transition function is
--   $$
--   e^{tQ}_{\iota\kappa}=\pi_\kappa+(\delta_{\iota\kappa}-\pi_\kappa)\,e^{-(r_1+r_2)t},\qquad \pi=\frac{(r_2,r_1)}{r_1+r_2},
--   $$
--   which reduces to the identity when $r_1+r_2=0$. A process $\alpha$ is a two-state Markov chain with generator $Q$ with respect to a filtration $\mathbb F$ if it is $\mathbb F$-adapted, every path is right-constant with finitely many jumps on bounded intervals, and $P(\alpha_{s+t}=\kappa\mid\mathcal F_s)=e^{tQ}_{\alpha_s\kappa}$ almost surely for all $s,t\ge 0$.
--
--   2. **$\mathbb F$-Brownian motion.** A standard real Brownian motion $W$ with continuous paths, adapted to $\mathbb F$, whose future increments $(W_{s+u}-W_s)_{u\ge0}$ are independent of $\mathcal F_s$ for every $s$.
--
--   3. **Stopping cost and value.** For a running cost $c_t(\omega)$, a measure $\mu$ and a random time $\tau:\Omega\to[0,\infty]$,
--   $$
--   J(\tau)=\mathbb E_\mu\int_0^{\tau} c_t^+\,dt-\mathbb E_\mu\int_0^{\tau} c_t^-\,dt\in[-\infty,\infty],
--   $$
--   and the value of the stopping problem is $\inf_\tau J(\tau)$ over all stopping times $\tau$ (possibly infinite) of a given filtration $\mathbb G$.
--
--   These are the building blocks of the regime-switching model and of the value functions $V$, $V^N$, $\tilde V^{1,N}$.
--
--   **Formalization Note** States are `Fin 2`, 0-based (Lean `0` is the paper's state 1). Stopping times take values in `WithTop ℝ≥0`, so $\tau=\infty$ is allowed. The cost is computed in `EReal` from two lower Lebesgue integrals, never with a Bochner integral, because the cost need not be integrable (the paper's (2.5) "does not necessarily hold"); a Bochner integral would silently return $0$.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, pp. 1–4, §1 (Markov chain α, Brownian motion W), (2.1), (2.6)

import Mathlib

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Transition function `exp(tQ)_{ικ}` of a two-state generator `Q = (q_{ικ})` (states `0, 1`,
0-based), in closed form: with jump rates `r₀ = q₀₁`, `r₁ = q₁₀` and `π = (r₁, r₀)/(r₀ + r₁)`,
`exp(tQ)_{ικ} = π_κ + (δ_{ικ} − π_κ) e^{−(r₀ + r₁) t}`. When `r₀ + r₁ = 0` (so `Q = 0` for a generator)
Lean's `x / 0 = 0` gives `π = 0` and the formula reduces to the identity `δ_{ικ}`, which is `exp(t·0)`. -/
noncomputable def twoStateTrans (q : Fin 2 → Fin 2 → ℝ) (t : ℝ) (ι κ : Fin 2) : ℝ :=
  let r0 := q 0 1
  let r1 := q 1 0
  let π : Fin 2 → ℝ := ![r1 / (r0 + r1), r0 / (r0 + r1)]
  π κ + ((if ι = κ then 1 else 0) - π κ) * Real.exp (-(r0 + r1) * t)

/-- `α` is a continuous-time Markov chain on the two states `Fin 2` with generator `Q = (q_{ικ})`
with respect to the filtration `𝔽`:
1. `α` is `𝔽`-adapted;
2. every path is right-constant: from each time it stays put for a positive time;
3. every path has finitely many jump times in every bounded interval `[0, T]`;
4. Markov property with transition function `exp(tQ)`: for all `s, t ≥ 0` and every state `κ`,
   `P(α_{s+t} = κ | 𝔽_s) = exp(tQ)_{α_s, κ}` almost surely. -/
def IsTwoStateChain {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (q : Fin 2 → Fin 2 → ℝ) (α : ℝ≥0 → Ω → Fin 2) : Prop :=
  (∀ t, Measurable[𝔽 t] (α t)) ∧
  (∀ (ω : Ω) (t : ℝ≥0), ∃ h : ℝ≥0, 0 < h ∧ ∀ s, t ≤ s → s < t + h → α s ω = α t ω) ∧
  (∀ (ω : Ω) (T : ℝ≥0),
    {t : ℝ≥0 | t ≤ T ∧ ∀ h : ℝ≥0, 0 < h → ∃ s, s < t ∧ t < s + h ∧ α s ω ≠ α t ω}.Finite) ∧
  (∀ (s t : ℝ≥0) (κ : Fin 2),
    P[(α (s + t) ⁻¹' {κ}).indicator (fun _ => (1 : ℝ)) | 𝔽 s]
      =ᵐ[P] fun ω => twoStateTrans q (t : ℝ) (α s ω) κ)

/-- `W` is a standard real Brownian motion with respect to the filtration `𝔽`: a Brownian motion
(Mathlib's `IsBrownianReal`), with continuous paths for every `ω`, `𝔽`-adapted, and whose future
increment path `u ↦ W_{s+u} − W_s` is independent of `𝔽_s` for every `s ≥ 0`. -/
def IsFBrownian {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P ∧ (∀ ω, Continuous fun t => W t ω) ∧ Adapted 𝔽 W ∧
  ∀ s : ℝ≥0, Indep (MeasurableSpace.comap (fun ω (u : ℝ≥0) => W (s + u) ω - W s ω) inferInstance)
    (𝔽 s) P

/-- The expected discounted running cost `E ∫₀^τ c_t dt` of a (possibly infinite) random time
`τ : Ω → [0, ∞]`, in `EReal`: the lower Lebesgue integral of the positive part of `c` over
`{(t, ω) : 0 ≤ t < τ(ω)}` minus that of the negative part. It is `+∞` when the positive part has
infinite expectation and the negative part does not; it never uses a Bochner integral, which would
silently return `0` on a non-integrable cost. -/
noncomputable def costJ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : EReal :=
  ((∫⁻ ω, ∫⁻ t in {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < τ ω},
      ENNReal.ofReal (c t ω) ∂volume ∂μ : ℝ≥0∞) : EReal)
  - ((∫⁻ ω, ∫⁻ t in {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < τ ω},
      ENNReal.ofReal (-c t ω) ∂volume ∂μ : ℝ≥0∞) : EReal)

/-- The value `inf_τ E ∫₀^τ c_t dt` of the optimal stopping problem with running cost `c`, over all
`𝔾`-stopping times `τ : Ω → [0, ∞]` (the value `∞` is allowed), in `EReal`. -/
noncomputable def stopValE {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (𝔾 : Filtration ℝ≥0 mΩ) (c : ℝ → Ω → ℝ) : EReal :=
  ⨅ τ : {τ : Ω → WithTop ℝ≥0 // IsStoppingTime 𝔾 τ}, costJ μ c τ.1

end SwitchOptStop.Boundary


