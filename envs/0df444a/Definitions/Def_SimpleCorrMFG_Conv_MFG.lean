-- Prove2me | Definitions.Def_SimpleCorrMFG_Conv_MFG
-- name    : SimpleCorrMFG_Conv_MFG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:25.046359+00:00
-- url     : https://prove2.me/theorems/cbeea84c-cc85-4b7a-9f31-cf386eee59f5
-- title:
--   §4, Definition 4.1, pp. 8–10 — the correlated mean field game: canonical realization, cost $J$, correlated solutions
-- statement:
--   This file defines the mean field game with a mediator and its correlated solutions.
--
--   **Realizations.** Fix $\mathfrak m_0\in\mathcal P(\mathcal X)$, a correlated flow $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ and a strategy modification $u$. A realization of $(\mathfrak m_0,\rho,u)$ carries a recommendation $\Phi$, states $X(0),\dots,X(T)$, a flow $\mu(0),\dots,\mu(T)$ and noises $\xi(1),\dots,\xi(T)$ with $X(0)\sim\mathfrak m_0$, $(\Phi,\mu)\sim\rho$, i.i.d. $\nu$ noises, $\xi(\cdot)$, $X(0)$ and $(\Phi,\mu)$ independent, and
--   $$X(t+1)=\Psi\big(t,X(t),\mu(t),u\circ\Phi(t,X(t)),\xi(t+1)\big).\tag{4.1}$$
--   The canonical realization lives on $\mathcal X\times(\mathcal R\times\mathcal P(\mathcal X)^{T+1})\times\mathcal Z^T$ with the product law $\mathfrak m_0\otimes\rho\otimes\nu^{\otimes T}$. Note that $\Phi$ and $\mu$ need not be independent.
--
--   **Cost.** $J(\mathfrak m_0,\rho,u)=\mathbb E\big[\sum_{t=0}^{T-1}f(t,X(t),\mu(t),u\circ\Phi(t,X(t)))+F(X(T),\mu(T))\big]$.
--
--   **Correlated solutions (Definition 4.1).** $\rho$ is a correlated solution of the mean field game in restricted strategies with initial distribution $\mathfrak m_0$ if
--   1. (optimality) $J(\mathfrak m_0;\rho,\mathrm{Id})\le J(\mathfrak m_0;\rho,u)$ for every strategy modification $u$;
--   2. (consistency) in a realization of $(\mathfrak m_0,\rho,\mathrm{Id})$, for every $t\in\{0,\dots,T\}$, $\mu(t)$ is a regular conditional distribution of $X(t)$ given $\mathcal F^\mu=\sigma(\mu(0),\dots,\mu(T))$:
--   $$\mu(t)(\cdot)=\mathbb P\big(X(t)\in\cdot\mid\mathcal F^\mu\big).$$
--
--   **Formalization Note** The paper computes $J$ in any realization and notes that the value does not depend on the choice (p. 9); the canonical law is used. Since $\mu(t)$ is a function of $\mu$ and $\mathcal X$ is finite, consistency is stated as the identity $\mathbb P(X(t)=x,\ \mu\in B)=\mathbb E[\mathbf 1_B(\mu)\,\mu(t)(\{x\})]$ for every $t$, $x\in\mathcal X$ and Borel $B\subseteq\mathcal P(\mathcal X)^{T+1}$, with the right side computed as an integral against $\rho$. The conditioning is on the whole flow, as in the paper.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 8–10 (§4, realizations, (4.1), cost J, Definition 4.1)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval

variable {T : ℕ} {X Γ : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace Γ]

/-- The canonical sample space of the mean field game (§4, p. 8): the initial state `X(0) ∈ X`,
the pair `(Φ, μ) ∈ R × P(X)^{T+1}` and the noises `ξ(t+1) ∈ Z = [0,1]` (index `t : Fin T`). -/
abbrev MOmega (T : ℕ) (X Γ : Type) [Fintype X] : Type :=
  X × (Strat T X Γ × Flow T X) × (Fin T → I)

/-- The law on `MOmega` prescribed by conditions (i)–(iv) of a realization of `(m₀, ρ, u)`
(pp. 8–9): `X(0) ∼ m₀`, `(Φ, μ) ∼ ρ`, i.i.d. uniform noises, and `ξ(·)`, `X(0)`, `(Φ, μ)`
independent: the product `m₀ ⊗ ρ ⊗ ν^{⊗T}`. -/
noncomputable def mfgLaw (m₀ : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) :
    Measure (MOmega T X Γ) :=
  ((m₀.toPM : ProbabilityMeasure X) : Measure X).prod
    ((ρ : Measure (Strat T X Γ × Flow T X)).prod (Measure.pi fun _ : Fin T => (volume : Measure I)))

instance (m₀ : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) :
    IsProbabilityMeasure (mfgLaw m₀ ρ) := by
  unfold mfgLaw; infer_instance

/-- The state sequence `X(0), …, X(T)` of a realization of `(m₀, ρ, u)`, computed on the canonical
sample space by (4.1) (p. 9): `X(t+1) = Ψ(t, X(t), μ(t), u ∘ Φ(t, X(t)), ξ(t+1))`. -/
def mfgPath (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) (ω : MOmega T X Γ) :
    Fin (T + 1) → X :=
  iterFin ω.1 (fun t x => M.Ψ t x (ω.2.1.2 t.castSucc) (u ω.2.1.1 t x) (ω.2.2 t))

/-- The cost (p. 9)
`J(m₀, ρ, u) = E[∑_{t=0}^{T−1} f(t, X(t), μ(t), u ∘ Φ(t, X(t))) + F(X(T), μ(T))]`,
the expectation under the canonical law. -/
noncomputable def costMFG (M : Model T X Γ) (m₀ : Meas X)
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) (u : Strat T X Γ → Strat T X Γ) : ℝ :=
  ∫ ω, ((∑ t : Fin T, M.f t (mfgPath M u ω t.castSucc) (ω.2.1.2 t.castSucc)
        (u ω.2.1.1 t (mfgPath M u ω t.castSucc))) +
      M.F (mfgPath M u ω (Fin.last T)) (ω.2.1.2 (Fin.last T))) ∂(mfgLaw m₀ ρ)

/-- Definition 4.1 (i), optimality (p. 9): `J(m₀; ρ, Id) ≤ J(m₀; ρ, u)` for every strategy
modification `u : R → R`. -/
def IsOptimal (M : Model T X Γ) (m₀ : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) :
    Prop :=
  ∀ u : Strat T X Γ → Strat T X Γ, costMFG M m₀ ρ id ≤ costMFG M m₀ ρ u

/-- Definition 4.1 (ii), consistency (pp. 9–10): in a realization of `(m₀, ρ, Id)`, `μ(t)` is a
regular conditional distribution of `X(t)` given `F^μ = σ(μ(0), …, μ(T))`, for every `t`. As `μ(t)`
is a function of `μ` and `X` is finite, this is the identity
`P(X(t) = x, μ ∈ B) = E[1_B(μ) μ(t)({x})]` for every `t`, `x ∈ X` and Borel `B ⊆ P(X)^{T+1}`. -/
def IsConsistent (M : Model T X Γ) (m₀ : Meas X)
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) : Prop :=
  ∀ (t : Fin (T + 1)) (x : X) (B : Set (Flow T X)), MeasurableSet B →
    (mfgLaw m₀ ρ).real {ω | mfgPath M id ω t = x ∧ ω.2.1.2 ∈ B} =
      ∫ p, B.indicator (fun m : Flow T X => ((m t : Meas X) : X → ℝ) x) p.2
        ∂(ρ : Measure (Strat T X Γ × Flow T X))

/-- Definition 4.1 (pp. 9–10): `ρ ∈ P(R × P(X)^{T+1})` is a correlated solution of the mean field
game in restricted strategies with initial distribution `m₀` if it satisfies optimality and
consistency. -/
def IsCorrelatedSolution (M : Model T X Γ) (m₀ : Meas X)
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) : Prop :=
  IsOptimal M m₀ ρ ∧ IsConsistent M m₀ ρ

end SimpleCorrMFG.Conv


