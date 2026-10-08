-- Prove2me | Definitions.Def_KellyReversibility_MarkovFields_GeneralSpatialProcess
-- name    : KellyReversibility_MarkovFields_GeneralSpatialProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:48.962082+00:00
-- url     : https://prove2.me/theorems/dbf92b8e-1f30-4b7c-8f7e-df6d1fd4533c
-- title:
--   The general spatial process: transition rates (9.15) and the distribution (9.17)
-- statement:
--   Let sites $j$ in a finite set carry attributes from finite sets $\mathcal N_j$, with states $\mathbf n\in\mathcal S=\prod_j\mathcal N_j$ and $T_j^m\mathbf n$ the state $\mathbf n$ with the attribute of site $j$ changed to $m$. Let $\Phi(\mathbf n)$ be a function of the state, let $\Phi_{G-j}(\mathbf n_{G-j})$, for each site $j$, be a function of the attributes of the sites other than $j$, and let $\lambda_j(n,m)$, $n,m\in\mathcal N_j$, be given numbers.
--
--   1. The **general spatial process** has transition rates
--   $$q(\mathbf n, T_j^m\mathbf n) = \lambda_j(n_j,m)\,\frac{\Phi(\mathbf n)}{\Phi_{G-j}(\mathbf n_{G-j})}, \qquad (9.15)$$
--   for $T_j^m\mathbf n\neq\mathbf n$; all other rates (to states differing in two or more sites, and from a state to itself) are zero.
--   2. Given functions $\alpha_j$ on $\mathcal N_j$, the **weight** of a state is $\prod_{j}\alpha_j(n_j)/\Phi(\mathbf n)$, and the **distribution (9.17)** is
--   $$\pi(\mathbf n) = B\,\frac{\prod_{j}\alpha_j(n_j)}{\Phi(\mathbf n)},$$
--   where $B$ is the reciprocal of the sum of the weights over $\mathcal S$.
--
--   $\lambda_j(n_j,m)$ is the innate tendency of site $j$ to change its attribute from $n_j$ to $m$; the factor $\Phi(\mathbf n)/\Phi_{G-j}(\mathbf n_{G-j})$ measures how this tendency is affected by the attributes of the other sites. This process contains the closed migration process as a special case (Kelly §9.3).
--
--   **Formalization Note** $\Phi_{G-j}$ is a function of the restriction of $\mathbf n$ to the subtype of sites different from $j$, so it cannot depend on $n_j$. The rate function is written as a sum over sites $j$ of the term for "$\mathbf n'\neq\mathbf n$ differs from $\mathbf n$ only at $j$"; at most one term is nonzero. Positivity of $\Phi$, $\Phi_{G-j}$ and $\alpha_j$ is not part of the definition; the theorems assume it.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 193 (PDF 196), §9.3, Eq. (9.15) and Eq. (9.17)

import Mathlib

namespace KellyReversibility.MarkovFields

/-! Kelly, *Reversibility and Stochastic Networks* (1979), §9.3, p. 193: a general spatial
process.

States are `n : (j : V) → N j`; `T_j^m n = Function.update n j m`. The data are a positive
function `Φ(n)` of the state, for each site `j` a positive function `Φ_{G-j}(n_{G-j})` of the
attributes of the other sites (here `Φm j`, taking the restriction of `n` to the subtype
`{k // k ≠ j}`), and for each site `j` the rates `λ_j(a, m)` (here `lam j a m`). -/

/-- **The transition rates (9.15)** of the general spatial process:
`q(n, T_j^m n) = λ_j(n_j, m) Φ(n) / Φ_{G-j}(n_{G-j})` whenever `T_j^m n ≠ n`, and
`q(n, n') = 0` when `n'` differs from `n` in two or more sites or `n' = n`. Since a state
`n' ≠ n` that differs from `n` only at site `j` determines `j`, at most one summand is nonzero. -/
noncomputable def generalSpatialRates {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, DecidableEq (N j)]
    (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) :
    ((j : V) → N j) → ((j : V) → N j) → ℝ :=
  fun n n' => ∑ j : V,
    if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k then
      lam j (n j) (n' j) * Φ n / Φm j (fun k => n k.1)
    else 0

/-- **The unnormalized equilibrium weight of (9.17)**: `∏_{j} α_j(n_j) / Φ(n)`. -/
noncomputable def generalSpatialWeight {V : Type*} [Fintype V] {N : V → Type*}
    (α : (j : V) → N j → ℝ) (Φ : ((j : V) → N j) → ℝ) (n : (j : V) → N j) : ℝ :=
  (∏ j, α j (n j)) / Φ n

/-- **The distribution (9.17)**: `π(n) = B ∏_{j} α_j(n_j) / Φ(n)`, where the normalizing
constant `B` is the reciprocal of the sum of the weights over the (finite) state space. -/
noncomputable def generalSpatialPi {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (α : (j : V) → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (n : (j : V) → N j) : ℝ :=
  (∑ n' : (j : V) → N j, generalSpatialWeight α Φ n')⁻¹ * generalSpatialWeight α Φ n

end KellyReversibility.MarkovFields


