-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
-- name    : RankBasedSDI_LoadBalancing_RankBasedEquations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:12.57389+00:00
-- url     : https://prove2.me/theorems/5fc483c5-41a9-4c30-b475-b4fb6afed061
-- title:
--   Weak solutions of (SDE), (SDER), (SDI), (SDIR) and pathwise uniqueness
-- statement:
--   Let data $b,m\in\mathbb R^N$ and $\sigma\in(0,\infty)^N$ be given, and write $\mathcal R_i(t)=\mathrm{rank}(i;X(t))$. A **weak solution of (SDIR)** consists of the following:
--
--   - a stochastic basis $(\Omega,\mathcal F,\mathbb F,P)$ satisfying the usual conditions;
--   - an $\mathbb F$-Brownian motion $B$ in dimension $N$;
--   - $\mathbb F$-adapted processes $(X,L)$ with sample paths in $C(\mathbb R_+,\mathbb R^N_+)\times C^{\uparrow}_0(\mathbb R_+,\mathbb R_+)^N$;
--   - an $\mathbb F$-progressively measurable process $\beta$ (the rank-dependent drift).
--
--   These must satisfy, almost surely, for all $t\ge0$ and $i\in[N]$:
--
--   $$
--   X_i(t)=X_{0,i}+\sigma_iB_i(t)+m_it+\int_0^t\beta_i(s)\,ds+L_i(t),
--   $$
--
--   with $\beta(t)\in\mathrm{conv}\{b_\pi:\pi\in\mathfrak P(X(t))\}$ for a.e. $t\in\mathbb R_+$, and $\int_0^\infty X_i(t)\,dL_i(t)=0$. Here $X_0=X(0)$ is $\mathcal F_0$-measurable.
--
--   A **weak solution of (SDER)** is the same without $\beta$, with the drift $\int_0^t b_{\mathcal R_i(s)}\,ds$. **(SDI)** and **(SDE)** are the corresponding equations without $L$, with $X$ having paths in $C(\mathbb R_+,\mathbb R^N)$.
--
--   **Pathwise uniqueness** holds for (SDIR) if the following is true for any two weak solutions $(X,L,B)$ and $(\tilde X,\tilde L,B)$ on the same stochastic basis, with the same Brownian motion and a common initial value: $X$ and $\tilde X$ are indistinguishable, and so are $L$ and $\tilde L$. For (SDI) the condition is the same, without $L$.
--
--   **Formalization Note** Processes are maps $\Omega\to\mathbb R\to\mathbb R^N$, evaluated at $t\ge0$, and filtrations are indexed by $\mathbb R_{\ge0}$. Sample-path properties are required for every $\omega$. The equations, the a.e.-$t$ inclusion and the complementarity are required $P$-a.s. The drift integral is a Bochner interval integral of a measurable, a.e.-bounded integrand. The complementarity is the `lintegral` condition of `Reflection`. In the uniqueness definitions the stochastic bases range over `Ω : Type` (universe 0).
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, pp. 6–8, §2.3, (SDE), (SDER), (SDI), (SDIR), definitions of weak solution and pathwise uniqueness

import Mathlib
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RankBasedSDI.LoadBalancing

/-!
Atar & Ichiba, arXiv:2409.15121v1, §2.3 pp. 6–8: weak solutions of the rank-based equations
(SDE), (SDER), (SDI), (SDIR) with data `b, m ∈ ℝ^N`, `σ ∈ (0,∞)^N`, and pathwise uniqueness.

Conventions. Processes are maps `Ω → ℝ → (Fin N → ℝ)` used at times `t ≥ 0`; the filtration is
indexed by `ℝ≥0`. The initial condition `X₀` is `X(0)` (the equation at `t = 0` forces
`X(0) = X₀`), so "`X₀ ∈ 𝓕₀`" is adaptedness of `X` at time `0`. Sample-path properties hold for
every `ω`; the equations, the drift inclusion and the complementarity hold `P`-a.s. The drift
integral `∫_0^t β_i(s) ds` is a Bochner interval integral: `β` is progressively measurable, hence
measurable in `s`, and a.e. bounded (its values lie a.e. in a compact convex hull), so the
integral is genuine.
-/

/-- **Weak solution of (SDIR)** (pp. 7–8): a stochastic basis `(Ω, 𝓕, 𝔽, P)` satisfying the usual
conditions, an `𝔽`-Brownian motion `B` in dimension `N`, and `𝔽`-adapted `(X, L)` with sample
paths in `C(ℝ₊, ℝ^N_+) × C↑₀(ℝ₊, ℝ₊)^N`, together with an `𝔽`-progressively measurable
rank-dependent drift `β`, such that a.s., for all `t ≥ 0` and `i ∈ [N]`,
`X_i(t) = X_{0,i} + σ_i B_i(t) + m_i t + ∫_0^t β_i(s) ds + L_i(t)`,
`β(t) ∈ conv{b_π : π ∈ 𝔓(X(t))}` for a.e. `t ∈ ℝ₊`, and `∫_0^∞ X_i(t) dL_i(t) = 0`. -/
structure IsWeakSolutionSDIR {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X L B β : Ω → ℝ → Fin N → ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  usual : UsualConditions P F
  brownian : IsFBrownian P F B
  adapted_X : ∀ t : ℝ≥0, Measurable[F t] (fun ω => X ω t)
  adapted_L : ∀ t : ℝ≥0, Measurable[F t] (fun ω => L ω t)
  progressive_β : IsProgressive F (fun (t : ℝ≥0) ω => β ω t)
  continuous_X : ∀ ω (i : Fin N), ContinuousOn (fun t => X ω t i) (Set.Ici 0)
  nonneg_X : ∀ ω (t : ℝ), 0 ≤ t → ∀ i : Fin N, 0 ≤ X ω t i
  regulator_L : ∀ ω (i : Fin N), IsC0Up (fun t => L ω t i)
  equation : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin N,
    X ω t i = X ω 0 i + σ i * B ω t i + m i * t + (∫ s in (0 : ℝ)..t, β ω s i) + L ω t i
  inclusion : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), β ω t ∈ driftSet b (X ω t)
  complementary : ∀ᵐ ω ∂P, ∀ i : Fin N,
    StieltjesComplementary (fun t => X ω t i) (fun t => L ω t i)

/-- **Weak solution of (SDER)** (pp. 6–7): as for (SDIR), with the drift fixed to the
rank-based drift `b_{ℛ_i(s)}`, `ℛ_i(s) = rank(i; X(s))`:
`X_i(t) = X_{0,i} + σ_i B_i(t) + m_i t + ∫_0^t b_{ℛ_i(s)} ds + L_i(t) ≥ 0`,
`∫_0^∞ X_i(t) dL_i(t) = 0`. -/
structure IsWeakSolutionSDER {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X L B : Ω → ℝ → Fin N → ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  usual : UsualConditions P F
  brownian : IsFBrownian P F B
  adapted_X : ∀ t : ℝ≥0, Measurable[F t] (fun ω => X ω t)
  adapted_L : ∀ t : ℝ≥0, Measurable[F t] (fun ω => L ω t)
  continuous_X : ∀ ω (i : Fin N), ContinuousOn (fun t => X ω t i) (Set.Ici 0)
  nonneg_X : ∀ ω (t : ℝ), 0 ≤ t → ∀ i : Fin N, 0 ≤ X ω t i
  regulator_L : ∀ ω (i : Fin N), IsC0Up (fun t => L ω t i)
  equation : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin N,
    X ω t i = X ω 0 i + σ i * B ω t i + m i * t +
      (∫ s in (0 : ℝ)..t, rankDrift b (X ω s) i) + L ω t i
  complementary : ∀ᵐ ω ∂P, ∀ i : Fin N,
    StieltjesComplementary (fun t => X ω t i) (fun t => L ω t i)

/-- **Weak solution of (SDI)** (pp. 7–8): (SDIR) without reflection, on the state space `ℝ^N`:
`X_i(t) = X_{0,i} + σ_i B_i(t) + m_i t + ∫_0^t β_i(s) ds`,
`β(t) ∈ conv{b_π : π ∈ 𝔓(X(t))}` for a.e. `t`, with `β` progressively measurable. -/
structure IsWeakSolutionSDI {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X B β : Ω → ℝ → Fin N → ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  usual : UsualConditions P F
  brownian : IsFBrownian P F B
  adapted_X : ∀ t : ℝ≥0, Measurable[F t] (fun ω => X ω t)
  progressive_β : IsProgressive F (fun (t : ℝ≥0) ω => β ω t)
  continuous_X : ∀ ω (i : Fin N), ContinuousOn (fun t => X ω t i) (Set.Ici 0)
  equation : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin N,
    X ω t i = X ω 0 i + σ i * B ω t i + m i * t + (∫ s in (0 : ℝ)..t, β ω s i)
  inclusion : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), β ω t ∈ driftSet b (X ω t)

/-- **Weak solution of (SDE)** (pp. 6–7): `X_i(t) = X_{0,i} + σ_i B_i(t) + m_i t +
∫_0^t b_{ℛ_i(s)} ds`, `ℛ_i(s) = rank(i; X(s))`, on the state space `ℝ^N`. -/
structure IsWeakSolutionSDE {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X B : Ω → ℝ → Fin N → ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  usual : UsualConditions P F
  brownian : IsFBrownian P F B
  adapted_X : ∀ t : ℝ≥0, Measurable[F t] (fun ω => X ω t)
  continuous_X : ∀ ω (i : Fin N), ContinuousOn (fun t => X ω t i) (Set.Ici 0)
  equation : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin N,
    X ω t i = X ω 0 i + σ i * B ω t i + m i * t + (∫ s in (0 : ℝ)..t, rankDrift b (X ω s) i)

/-- **Pathwise uniqueness for (SDIR)** (p. 7, extended to (SDIR) on p. 8): for any two weak
solutions `(X, L, B)` and `(X̃, L̃, B)` (with drifts `β`, `β̃`) on the same stochastic basis, with
the same Brownian motion and common initial value `X(0) = X̃(0)` a.s., the processes `X` and `X̃`
are indistinguishable, and so are `L` and `L̃`. Stochastic bases range over `Ω : Type`. -/
def PathwiseUniqueSDIR {N : ℕ} (b m σ : Fin N → ℝ) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B X L β X' L' β' : Ω → ℝ → Fin N → ℝ),
    IsWeakSolutionSDIR b m σ P F X L B β → IsWeakSolutionSDIR b m σ P F X' L' B β' →
    (∀ᵐ ω ∂P, X ω 0 = X' ω 0) →
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X ω t = X' ω t) ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → L ω t = L' ω t)

/-- **Pathwise uniqueness for (SDI)**: two weak solutions on the same basis with the same
Brownian motion and a.s. equal initial values are indistinguishable. -/
def PathwiseUniqueSDI {N : ℕ} (b m σ : Fin N → ℝ) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B X β X' β' : Ω → ℝ → Fin N → ℝ),
    IsWeakSolutionSDI b m σ P F X B β → IsWeakSolutionSDI b m σ P F X' B β' →
    (∀ᵐ ω ∂P, X ω 0 = X' ω 0) →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X ω t = X' ω t

end RankBasedSDI.LoadBalancing


