-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_OpenLoop
-- name    : ProgCorrMFG_Approx_OpenLoop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:28.224482+00:00
-- url     : https://prove2.me/theorems/3d7aeb6b-a4da-4e55-b6ad-e7bb640e2c6d
-- title:
--   §5.1, Definitions 5.1, 5.3, (5.2), (5.3) — open-loop policies, cost $\hat J$ and open-loop correlated solutions
-- statement:
--   This file defines the mean field game in stochastic open-loop strategies.
--
--   **Open-loop policies (Definition 5.1).** For $\mathfrak m_0$ and $\rho$ as before, a realization of an open-loop policy is a probability space with σ-algebras $\{\mathcal G_t\}_{t=0}^{T-1}$, carrying $X_t$, $\Phi$, $\mu$, $\xi_t$ and $\Gamma$-valued controls $u_t$ such that:
--   1. i)–iv) $X_0\sim\mathfrak m_0$, $(\Phi,\mu)\sim\rho$, the $\xi_t$ are i.i.d. $\nu$, and the three are independent;
--   2. iv') $\{\mathcal G_t\}$ is a filtration; $\xi_t$ is $\mathcal G_t$-measurable and $(\xi_{t+1},\dots,\xi_T)$ is independent of $\mathcal G_t$; $\mathcal G_t=\mathcal H_t\vee\sigma(\mu^{(t)})\vee\sigma(\Phi)\vee\sigma(X_0)$ with $\mathcal H_t$ independent of $\sigma(\Phi,\mu,X_0)$; and $u_t$ is $\mathcal G_t$-measurable;
--   3. v) almost surely $X_{t+1}=\Psi(t,X_t,\mu_t,u_t,\xi_{t+1})$.
--
--   Its cost (5.3) is $\hat J(\mathfrak m_0,\rho,u)=\mathbb E\big[\sum_{t=0}^{T-1}f(t,X_t,\mu_t,u_t)+F(X_T,\mu_T)\big]$. The policy $u^\iota_t=\Phi(t,X_t)$ of (5.2) follows the suggestion.
--
--   **Open-loop correlated solutions (Definition 5.3).** $\rho$ is an open-loop correlated solution if (Opt) $\hat J(\mathfrak m_0,\rho,u^\iota)\le\hat J(\mathfrak m_0,\rho,u)$ for every open-loop policy $u$, and (Con) in every realization of $(\mathfrak m_0,\rho,u^\iota)$, $\mu_t(\cdot)=\mathbb P(X_t\in\cdot\,|\,\mathcal F^\mu)$ for all $t$.
--
--   **Formalization Note** $\mathcal G_t$ is `filt t` and $\mathcal H_t$ is `aux t`, indexed by `Fin T`; the noise $\xi_{s+1}$ has index $s$, so "$\xi_t$ is $\mathcal G_t$-measurable" reads `noise s` is `filt t`-measurable when $s+1=t$, and the future noises are those with index $\ge t$. Completeness of the space and of the filtration is dropped. Costs are expected costs of realizations and (Opt) is required for every realization of each side.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, pp. 8–9, Definition 5.1, (5.1), (5.2), (5.3), Definition 5.3

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval

/-- A realization of `(𝔪₀, ρ, (u_t)_t)` for an open-loop control policy (Definition 5.1, p. 8), on a
probability space `(Ω, P)` with σ-algebras `𝒢_t` (`filt t`) and `ℋ_t` (`aux t`),
`t ∈ ⟦0, T−1⟧`. Fields: states `X_t`, suggestion `Φ`, flow `μ`, noises `ξ_{t+1}` (`noise ω t`)
and controls `u_t ∈ Γ` (`ctrl ω t`).
* `law` is i)–iv): `(X_0, ξ, (Φ, μ))` has the product law `𝔪₀ ⊗ ν^{⊗T} ⊗ ρ`;
* iv'): `{𝒢_t}` is a filtration; `ξ_t` is `𝒢_t`-measurable (`noise_adapted`, for `t ≥ 1`);
  `(ξ_{t+1}, …, ξ_T)` is independent of `𝒢_t` (`noise_indep`);
  `𝒢_t = ℋ_t ∨ σ(μ^{(t)}) ∨ σ(Φ) ∨ σ(X_0)` with `ℋ_t` independent of `σ(Φ, μ, X_0)`;
  `u_t` is `𝒢_t`-measurable;
* `dynamics` is v), (5.1): `X_{t+1} = Ψ(t, X_t, μ_t, u_t, ξ_{t+1})` almost surely. -/
structure OLRealization {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace G]
    (M : Model T X G) (m₀ : Measure X) (ρ : Measure (Strat T X G × Flow T X))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  state : Ω → Fin (T + 1) → X
  sugg : Ω → Strat T X G
  flow : Ω → Flow T X
  noise : Ω → Fin T → I
  ctrl : Ω → Fin T → G
  filt : Fin T → MeasurableSpace Ω
  aux : Fin T → MeasurableSpace Ω
  measurable_state : Measurable state
  measurable_sugg : Measurable sugg
  measurable_flow : Measurable flow
  measurable_noise : Measurable noise
  law : P.map (fun ω => (state ω 0, noise ω, (sugg ω, flow ω))) =
    m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ)
  filt_mono : Monotone filt
  aux_le : ∀ t, aux t ≤ mΩ
  filt_eq : ∀ t : Fin T, filt t =
    aux t ⊔ MeasurableSpace.comap (fun ω (s : {s : Fin (T + 1) // s ≤ t.castSucc}) => flow ω s)
      inferInstance ⊔ MeasurableSpace.comap sugg inferInstance ⊔
      MeasurableSpace.comap (fun ω => state ω 0) inferInstance
  aux_indep : ∀ t : Fin T, Indep (aux t)
    (MeasurableSpace.comap (fun ω => (sugg ω, flow ω, state ω 0)) inferInstance) P
  noise_adapted : ∀ s t : Fin T, s.1 + 1 = t.1 → Measurable[filt t] (fun ω => noise ω s)
  noise_indep : ∀ t : Fin T, Indep
    (MeasurableSpace.comap (fun ω (s : {s : Fin T // t ≤ s}) => noise ω s) inferInstance) (filt t) P
  ctrl_adapted : ∀ t : Fin T, Measurable[filt t] (fun ω => ctrl ω t)
  dynamics : ∀ᵐ ω ∂P, ∀ t : Fin T,
    state ω t.succ = M.Ψ t (state ω t.castSucc) (flow ω t.castSucc) (ctrl ω t) (noise ω t)

/-- The cost (5.3): `Ĵ(𝔪₀, ρ, u) := 𝔼[∑_{t=0}^{T−1} f(t, X_t, μ_t, u_t) + F(X_T, μ_T)]`. -/
noncomputable def OLRealization.cost {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X]
    [MeasurableSpace G] {M : Model T X G} {m₀ : Measure X} {ρ : Measure (Strat T X G × Flow T X)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (R : OLRealization M m₀ ρ P) : ℝ :=
  ∫ ω, ((∑ t : Fin T, M.f t (R.state ω t.castSucc) (R.flow ω t.castSucc) (R.ctrl ω t)) +
    M.F (R.state ω (Fin.last T)) (R.flow ω (Fin.last T))) ∂P

/-- The realization uses the policy `u^ι_t := Φ(t, X_t)` of (5.2). -/
def OLRealization.IsIota {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X]
    [MeasurableSpace G] {M : Model T X G} {m₀ : Measure X} {ρ : Measure (Strat T X G × Flow T X)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (R : OLRealization M m₀ ρ P) : Prop :=
  ∀ ω (t : Fin T), R.ctrl ω t = R.sugg ω t (R.state ω t.castSucc)

/-- Definition 5.3 (p. 9): `ρ` is an open-loop correlated solution with initial distribution `𝔪₀` if
* (Opt) `Ĵ(𝔪₀, ρ, u^ι) ≤ Ĵ(𝔪₀, ρ, u)` for every open-loop policy `u ∈ 𝒜` (for every realization of
  each side), and
* (Con) for every realization of `(𝔪₀, ρ, u^ι)`, `μ_t(·) = ℙ(X_t ∈ · | 𝓕^μ)` a.s. for every `t`,
  `𝓕^μ = σ((μ_t)_{t=0}^T)`. -/
def IsOLCorrelatedSolution {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X]
    [MeasurableSpace G] (M : Model T X G) (m₀ : Measure X)
    (ρ : Measure (Strat T X G × Flow T X)) : Prop :=
  (∀ (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (R₀ : OLRealization M m₀ ρ P₀), R₀.IsIota →
      ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (R₁ : OLRealization M m₀ ρ P₁), R₀.cost ≤ R₁.cost) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (R : OLRealization M m₀ ρ P), R.IsIota → ∀ (t : Fin (T + 1)) (x : X),
      (fun ω => ((R.flow ω t : Meas X) : X → ℝ) x) =ᵐ[P]
        condExp (MeasurableSpace.comap R.flow inferInstance) P
          ({ω | R.state ω t = x}.indicator (fun _ => (1 : ℝ))))

end ProgCorrMFG.Approx


