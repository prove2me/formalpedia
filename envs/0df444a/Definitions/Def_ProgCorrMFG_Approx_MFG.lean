-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_MFG
-- name    : ProgCorrMFG_Approx_MFG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:17.260453+00:00
-- url     : https://prove2.me/theorems/8d0911c8-328a-4518-8d82-ad1c4a373b53
-- title:
--   §4, Definitions 4.1, 4.3, (R1), (R2), Theorem 6.2 — MFG realizations, cost $J$, correlated solutions, (R1)–(R2), $\gamma^N$
-- statement:
--   This file defines the mean field game with a mediator, its correlated solutions, and the suggestion $\gamma^N$ of Theorem 6.2.
--
--   **Realizations (Definition 4.1).** Fix $\mathfrak m_0\in\mathcal P(\mathcal X)$, a correlated suggestion $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ and a strategy modification $w:\mathcal R\to\widehat{\mathcal R}$. A realization of $(\mathfrak m_0,\rho,w)$ is a probability space carrying a state process $(X_t)_{t=0}^T$, a restricted strategy $\Phi$, a flow $\mu=(\mu_t)_{t=0}^T$ and noises $(\xi_t)_{t=1}^T$ such that $X_0\sim\mathfrak m_0$, $(\Phi,\mu)\sim\rho$, the $\xi_t$ are i.i.d. $\nu$, the three are independent, and almost surely
--   $$X_{t+1}=\Psi\big(t,X_t,\mu_t,w\circ\Phi(t,X,\mu),\xi_{t+1}\big),\qquad t\in[\![0,T-1]\!].$$
--   Its cost (4.2) is $J(\mathfrak m_0,\rho,w)=\mathbb E\big[\sum_{t=0}^{T-1}f(t,X_t,\mu_t,w\circ\Phi(t,X^{(t)},\mu^{(t)}))+F(X_T,\mu_T)\big]$.
--
--   **Correlated solutions (Definition 4.3).** $\rho$ is a correlated solution with initial distribution $\mathfrak m_0$ if (Opt) $J(\mathfrak m_0,\rho,\iota)\le J(\mathfrak m_0,\rho,w)$ for every $w$, and (Con) in every realization of $(\mathfrak m_0,\rho,\iota)$,
--   $$\mu_t(\cdot)=\mathbb P\big(X_t\in\cdot\,\big|\,\mathcal F^\mu\big),\qquad t\in[\![0,T]\!],\qquad\mathcal F^\mu=\sigma\big((\mu_s)_{s=0}^T\big).$$
--
--   **(R1)** For every $\varphi\in\mathcal R$ with $\rho(\{\varphi\}\times\mathcal P(\mathcal X)^{T+1})>0$ there is a finite set $\mathcal P_\varphi$ of flows carrying all of $\rho(\{\varphi\}\times\cdot)$, each of whose points has positive $\rho(\{\varphi\}\times\cdot)$-mass.
--
--   **(R2)** There are Borel maps $\alpha_t:[0,1]\times\mathcal P(\mathcal X)^{t+2}\to\mathcal E=\Gamma^{\mathcal X}$ such that $\rho$ is the law of $\big((\alpha_t(Z,\mu^{(t+1)}))_{t=0}^{T-1},\mu\big)$ when $Z\sim\nu$ is independent of $\mu\sim\rho_2$, the second marginal of $\rho$.
--
--   **The suggestion of Theorem 6.2.** Given a disintegration $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\rho_2(dm)$,
--   $$\gamma^N(C_1\times\cdots\times C_N)=\int_{\mathcal P(\mathcal X)^{T+1}}\prod_{j=1}^N\rho_1(C_j|m)\,\rho_2(dm),$$
--   a measure on $\mathcal R^N$, which is pushed into $\mathcal P(\widehat{\mathcal R}_N^N)$ through the inclusion of restricted strategies.
--
--   **Formalization Note** Conditions i)–iv) are one product-law identity. Costs are expected costs of realizations, and (Opt) is required for every realization of each side. (Con) is written with Lean's conditional expectation given $\sigma(\mu)$, coordinatewise in $x$. (R2) is read in distribution (Remark 6.1): on a fixed probability space an independent uniform $Z$ need not exist. $\gamma^N$ is defined by its atoms $\gamma^N\{(\varphi_1,\dots,\varphi_N)\}=\int\prod_j\rho_1(\{\varphi_j\}|m)\rho_2(dm)$, which determine it on the finite set $\mathcal R^N$.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 7 (Definition 4.1, (4.1), (4.2), Definition 4.3), p. 9 ((R1)), p. 15 ((R2), Remark 6.1, Theorem 6.2)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval

/-- A realization of `(𝔪₀, ρ, w)` (Definition 4.1, p. 7), for a correlated suggestion
`ρ ∈ 𝒫(ℛ × 𝒫(𝒳)^{T+1})` and a strategy modification `w ∈ 𝒟̂ = {w : ℛ → ℛ̂}`, on a probability space
`(Ω, P)`. Fields: the state process `X_t` (`state ω t`), the suggestion `Φ` (`sugg ω`), the flow
`μ = (μ_t)_t` (`flow ω`) and the noises `ξ_{t+1}` (`noise ω t`, `t ∈ ⟦0, T−1⟧`).
* `law` is i)–iv): `(X_0, ξ, (Φ, μ))` has the product law `𝔪₀ ⊗ ν^{⊗T} ⊗ ρ`;
* `dynamics` is v), (4.1): `X_{t+1} = Ψ(t, X_t, μ_t, w ∘ Φ(t, X, μ), ξ_{t+1})` almost surely. -/
structure MFGRealization {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace G]
    (M : Model T X G) (m₀ : Measure X) (ρ : Measure (Strat T X G × Flow T X))
    (w : Strat T X G → Prog T X G) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) where
  state : Ω → Fin (T + 1) → X
  sugg : Ω → Strat T X G
  flow : Ω → Flow T X
  noise : Ω → Fin T → I
  measurable_state : Measurable state
  measurable_sugg : Measurable sugg
  measurable_flow : Measurable flow
  measurable_noise : Measurable noise
  law : P.map (fun ω => (state ω 0, noise ω, (sugg ω, flow ω))) =
    m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ)
  dynamics : ∀ᵐ ω ∂P, ∀ t : Fin T,
    state ω t.succ = M.Ψ t (state ω t.castSucc) (flow ω t.castSucc)
      ((w (sugg ω) t).1 (state ω) (flow ω)) (noise ω t)

/-- The cost (4.2) of a realization:
`𝔼[∑_{t=0}^{T−1} f(t, X_t, μ_t, w ∘ Φ(t, X^{(t)}, μ^{(t)})) + F(X_T, μ_T)]`. -/
noncomputable def MFGRealization.cost {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X]
    [MeasurableSpace G] {M : Model T X G} {m₀ : Measure X} {ρ : Measure (Strat T X G × Flow T X)}
    {w : Strat T X G → Prog T X G} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (R : MFGRealization M m₀ ρ w P) : ℝ :=
  ∫ ω, ((∑ t : Fin T, M.f t (R.state ω t.castSucc) (R.flow ω t.castSucc)
      ((w (R.sugg ω) t).1 (R.state ω) (R.flow ω))) +
    M.F (R.state ω (Fin.last T)) (R.flow ω (Fin.last T))) ∂P

/-- Definition 4.3 (p. 7): `ρ` is a correlated solution of the mean field game with initial
distribution `𝔪₀` if
* (Opt) `J(𝔪₀, ρ, ι) ≤ J(𝔪₀, ρ, w)` for every `w ∈ 𝒟̂` (for every realization of each side), and
* (Con) for every realization of `(𝔪₀, ρ, ι)`, `μ_t(·) = ℙ(X_t ∈ · | 𝓕^μ)` a.s. for every `t`,
  where `𝓕^μ = σ((μ_t)_{t=0}^T)` is generated by the whole flow. -/
def IsCorrelatedSolution {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [MeasurableSpace G] (M : Model T X G) (m₀ : Measure X)
    (ρ : Measure (Strat T X G × Flow T X)) : Prop :=
  (∀ (w : Strat T X G → Prog T X G)
      (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (R₀ : MFGRealization M m₀ ρ iotaMFG P₀)
      (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
      (R₁ : MFGRealization M m₀ ρ w P₁),
      R₀.cost ≤ R₁.cost) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (R : MFGRealization M m₀ ρ iotaMFG P) (t : Fin (T + 1)) (x : X),
      (fun ω => ((R.flow ω t : Meas X) : X → ℝ) x) =ᵐ[P]
        condExp (MeasurableSpace.comap R.flow inferInstance) P
          ({ω | R.state ω t = x}.indicator (fun _ => (1 : ℝ))))

/-- Assumption (R1) (p. 9): for every `φ ∈ ℛ` with `ℙ(Φ = φ) = ρ({φ} × 𝒫(𝒳)^{T+1}) > 0` there is a
finite set `𝒫_φ ⊂ 𝒫(𝒳)^{T+1}` carrying all of `ρ({φ} × ·)`, each point of which has positive mass. -/
def R1 {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (ρ : Measure (Strat T X G × Flow T X)) : Prop :=
  ∀ φ : Strat T X G, 0 < ρ ({φ} ×ˢ Set.univ) →
    ∃ Pφ : Finset (Flow T X), ρ ({φ} ×ˢ (↑Pφ : Set (Flow T X))ᶜ) = 0 ∧
      ∀ m ∈ Pφ, 0 < ρ {(φ, m)}

/-- Assumption (R2) (p. 15), in distributional form (Remark 6.1): there are Borel maps
`α_t : [0,1] × 𝒫(𝒳)^{t+2} → ℰ = {𝒳 → Γ}`, `t ∈ ⟦0, T−1⟧`, such that `ρ` is the law of
`((α_t(Z, μ^{(t+1)}))_t, μ)` with `Z ∼ ν` independent of `μ ∼ ρ₂` (the second marginal of `ρ`). -/
def R2 {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (ρ : Measure (Strat T X G × Flow T X)) : Prop :=
  ∃ α : (t : Fin T) → I → (Fin (t.1 + 2) → Meas X) → (X → G),
    (∀ t, Measurable (fun p : I × (Fin (t.1 + 2) → Meas X) => α t p.1 p.2)) ∧
    ρ = ((volume : Measure I).prod (ρ.map Prod.snd)).map
      (fun p : I × Flow T X => ((fun t => α t p.1 (histSucc p.2 t)), p.2))

/-- The correlated suggestion of Theorem 6.2, `γ^N ∈ 𝒫(ℛ^N)`,
`γ^N(C_1 × ⋯ × C_N) = ∫ ∏_{j=1}^N ρ₁(C_j | m) ρ₂(dm)`; as `ℛ^N` is finite, it is given by its atoms
`γ^N{(φ_1, …, φ_N)} = ∫ ∏_j ρ₁({φ_j} | m) ρ₂(dm)`. -/
noncomputable def gammaN {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (ρ₂ : Measure (Flow T X)) (ρ₁ : Kernel (Flow T X) (Strat T X G)) (N : ℕ) :
    Measure (Fin N → Strat T X G) :=
  Measure.sum (fun φs : Fin N → Strat T X G => (∫⁻ m, ∏ j, ρ₁ m {φs j} ∂ρ₂) • Measure.dirac φs)

/-- A suggestion law on `ℛ^N` pushed into `𝒫(ℛ̂_N^N)` through the inclusion `ℛ ⊂ ℛ̂_N`. -/
noncomputable def liftSugg {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G] {N : ℕ}
    (γ : Measure (Fin N → Strat T X G)) : Measure (Fin N → ProgN T X G (N - 1)) :=
  γ.map (fun φs j => embN (φs j))

end ProgCorrMFG.Approx


