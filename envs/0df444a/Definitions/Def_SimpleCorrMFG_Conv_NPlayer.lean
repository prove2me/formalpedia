-- Prove2me | Definitions.Def_SimpleCorrMFG_Conv_NPlayer
-- name    : SimpleCorrMFG_Conv_NPlayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:28.087202+00:00
-- url     : https://prove2.me/theorems/9fa376e4-dc58-4d99-ae4e-ad5aaae424fd
-- title:
--   §3, Definition 3.1, p. 19 — the $N$-player game: canonical realization, costs $J^N_i$, symmetric $\varepsilon$-correlated equilibria, $\rho^N$
-- statement:
--   This file defines the $N$-player game with a mediator and the measures $\rho^N$ of Theorem 6.1.
--
--   **Realizations.** Fix an initial law $\mathfrak m^N\in\mathcal P(\mathcal X^N)$, a correlated profile $\gamma^N\in\mathcal P(\mathcal R^N)$, a player $i$ and a strategy modification $u$. A realization carries recommendations $\Phi_1,\dots,\Phi_N$, states $X_j(t)$ and noises $\xi_j(t)$ such that $(X_1(0),\dots,X_N(0))\sim\mathfrak m^N$, $(\Phi_1,\dots,\Phi_N)\sim\gamma^N$, the noises are i.i.d. $\nu$, the three vectors are independent, and
--   $$X_i(t+1)=\Psi\big(t,X_i(t),\mu_i(t),u\circ\Phi_i(t,X_i(t)),\xi_i(t+1)\big),\qquad X_j(t+1)=\Psi\big(t,X_j(t),\mu_j(t),\Phi_j(t,X_j(t)),\xi_j(t+1)\big),\ j\ne i,$$
--   where $\mu_l(t)=(N-1)^{-1}\sum_{j\neq l}\delta_{X_j(t)}$. Here the realization is the canonical one: the sample space is $\mathcal X^N\times\mathcal R^N\times\mathcal Z^{TN}$ with the product law $\mathfrak m^N\otimes\gamma^N\otimes\nu^{\otimes TN}$, and the states are computed from the recursion.
--
--   **Cost and equilibrium (Definition 3.1).** The cost of player $i$ is
--   $$J^N_i(\mathfrak m^N,\gamma^N,u)=\mathbb E\Big[\sum_{t=0}^{T-1}f\big(t,X_i(t),\mu_i(t),u\circ\Phi_i(t,X_i(t))\big)+F\big(X_i(T),\mu_i(T)\big)\Big].$$
--   For $\varepsilon\ge0$, $\gamma^N$ is an $\varepsilon$-correlated equilibrium in restricted strategies with initial distribution $\mathfrak m^N$ if $J^N_i(\mathfrak m^N,\gamma^N,\mathrm{Id})\le J^N_i(\mathfrak m^N,\gamma^N,u)+\varepsilon$ for every player $i$ and every $u:\mathcal R\to\mathcal R$. It is symmetric if $\gamma^N$ is invariant under permutations of the $N$ components.
--
--   **The measures $\rho^N$ (p. 19).** For $N\ge2$, $\rho^N$ is the joint law of player 1's recommendation and the flow of empirical measures of the other players under a realization of $(\mathfrak m^N,\gamma^N,\mathrm{Id})$:
--   $$\rho^N=\mathbb P\circ\big(\Phi_1,\mu_1(0),\dots,\mu_1(T)\big)^{-1}\in\mathcal P\big(\mathcal R\times\mathcal P(\mathcal X)^{T+1}\big).$$
--   `rhoSeq` is the sequence $n\mapsto\rho^{n+2}$ for the initial laws $\mathfrak m^N=\otimes^N\mathfrak m_{0,N}$.
--
--   **Formalization Note** Players are `Fin N`; the paper's player 1 is index `0`. The paper defines the cost through any realization and notes it does not depend on the choice (p. 7); the canonical product law is used here. If the map defining $\rho^N$ is not measurable (impossible when $\Psi$ is measurable), `rhoN` returns a junk Dirac mass. For $N=1$ the empirical measure of the others is a junk value; every statement uses $N\ge2$.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 5–7 (§3, realizations, cost, Definition 3.1), p. 19 (ρ^N)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval

variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSpace Γ]

/-- The canonical sample space of the `N`-player game (§3, p. 6): initial states
`(X_1(0), …, X_N(0)) ∈ X^N`, recommendations `(Φ_1, …, Φ_N) ∈ R^N` and noises
`ξ_j(t+1) ∈ Z = [0,1]` (stored at index `t : Fin T`, player `j : Fin N`). -/
abbrev NOmega (T N : ℕ) (X Γ : Type) : Type :=
  (Fin N → X) × (Fin N → Strat T X Γ) × (Fin T → Fin N → I)

/-- The law on `NOmega` prescribed by conditions (i)–(iv) of a realization (p. 6): initial states
with law `m^N`, recommendations with law `γ^N`, i.i.d. uniform noises `ν^{⊗NT}`, the three
independent. -/
noncomputable def nLaw {N : ℕ} (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) : Measure (NOmega T N X Γ) :=
  (mN : Measure (Fin N → X)).prod ((γ : Measure (Fin N → Strat T X Γ)).prod
    (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)))

instance {N : ℕ} (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    IsProbabilityMeasure (nLaw mN γ) := by
  unfold nLaw; infer_instance

/-- The strategy played by player `j` when player `i` applies the strategy modification `u` to
its recommendation and every other player follows its recommendation. -/
def played {N : ℕ} (i : Fin N) (u : Strat T X Γ → Strat T X Γ) (φ : Fin N → Strat T X Γ)
    (j : Fin N) : Strat T X Γ :=
  if j = i then u (φ j) else φ j

/-- The state vectors `(X_1^N(t), …, X_N^N(t))`, `t ∈ {0, …, T}`, of a realization of
`(m^N, γ^N, u)` for player `i` (condition (v), p. 6), computed on the canonical sample space:
`X_i(t+1) = Ψ(t, X_i(t), μ_i(t), u ∘ Φ_i(t, X_i(t)), ξ_i(t+1))` and
`X_j(t+1) = Ψ(t, X_j(t), μ_j(t), Φ_j(t, X_j(t)), ξ_j(t+1))` for `j ≠ i`. -/
noncomputable def nPath (M : Model T X Γ) {N : ℕ} (i : Fin N) (u : Strat T X Γ → Strat T X Γ)
    (ω : NOmega T N X Γ) : Fin (T + 1) → Fin N → X :=
  iterFin ω.1 (fun t x j => M.Ψ t (x j) (empOthers x j) (played i u ω.2.1 j t (x j)) (ω.2.2 t j))

/-- The cost of player `i` (p. 7),
`J_i^N(m^N, γ^N, u) = E[∑_{t=0}^{T−1} f(t, X_i(t), μ_i(t), u ∘ Φ_i(t, X_i(t))) + F(X_i(T), μ_i(T))]`,
the expectation under the canonical law. -/
noncomputable def costN (M : Model T X Γ) {N : ℕ} (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (i : Fin N) (u : Strat T X Γ → Strat T X Γ) :
    ℝ :=
  ∫ ω, ((∑ t : Fin T, M.f t (nPath M i u ω t.castSucc i) (empOthers (nPath M i u ω t.castSucc) i)
        (u (ω.2.1 i) t (nPath M i u ω t.castSucc i))) +
      M.F (nPath M i u ω (Fin.last T) i) (empOthers (nPath M i u ω (Fin.last T)) i)) ∂(nLaw mN γ)

/-- Definition 3.1 (p. 7): `γ^N` is an `ε`-correlated equilibrium in restricted strategies with
initial distribution `m^N` if `J_i^N(m^N, γ^N, Id) ≤ J_i^N(m^N, γ^N, u) + ε` for every player `i` and
every strategy modification `u : R → R`. -/
def IsEpsCE (M : Model T X Γ) {N : ℕ} (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (ε : ℝ) : Prop :=
  ∀ (i : Fin N) (u : Strat T X Γ → Strat T X Γ), costN M mN γ i id ≤ costN M mN γ i u + ε

/-- Definition 3.1 (p. 7): a correlated profile is symmetric if it is invariant under permutations
of the components. -/
def IsSymmetric {N : ℕ} (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) : Prop :=
  ∀ π : Equiv.Perm (Fin N),
    (γ : Measure (Fin N → Strat T X Γ)).map (fun φ => φ ∘ π) = (γ : Measure (Fin N → Strat T X Γ))

/-- The map `ω ↦ (Φ_1, μ_1(0), …, μ_1(T))` on the canonical sample space, `u = Id`; the paper's
player 1 is index `0`. -/
noncomputable def rhoMap (M : Model T X Γ) {N : ℕ} [NeZero N] (ω : NOmega T N X Γ) :
    Strat T X Γ × Flow T X :=
  (ω.2.1 0, fun t => empOthers (nPath M 0 id ω t) 0)

open Classical in
/-- `ρ^N = P_N ∘ (Φ_1^N, μ_1^N(0), …, μ_1^N(T))⁻¹` (p. 19), the law under a realization of
`(m^N, γ^N, Id)`. If the map is not measurable (impossible under `Model.Standing`), a junk Dirac
mass is returned. -/
noncomputable def rhoN [Nonempty Γ] (M : Model T X Γ) {N : ℕ} [NeZero N]
    (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    ProbabilityMeasure (Strat T X Γ × Flow T X) :=
  if h : AEMeasurable (rhoMap M) (nLaw mN γ) then
    ⟨(nLaw mN γ).map (rhoMap M), Measure.isProbabilityMeasure_map h⟩
  else
    ⟨Measure.dirac (fun _ _ => Classical.arbitrary Γ,
      fun _ => ⟨Pi.single (Classical.arbitrary X) 1, single_mem_stdSimplex ℝ _⟩), inferInstance⟩

/-- The sequence `(ρ^N)_{N ≥ 2}` of Theorem 6.1 (p. 19), for the initial laws `m^N = ⊗^N m_{0,N}`
of (A5) and the profiles `γ^N`; the `n`-th term is `ρ^{n+2}`. -/
noncomputable def rhoSeq [Nonempty Γ] (M : Model T X Γ) (m0N : ℕ → Meas X)
    (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ)) (n : ℕ) :
    ProbabilityMeasure (Strat T X Γ × Flow T X) :=
  rhoN M (prodInit (n + 2) (m0N (n + 2))) (γ (n + 2))

end SimpleCorrMFG.Conv


