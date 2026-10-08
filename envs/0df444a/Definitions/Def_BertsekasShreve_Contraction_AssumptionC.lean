-- Prove2me | Definitions.Def_BertsekasShreve_Contraction_AssumptionC
-- name    : BertsekasShreve_Contraction_AssumptionC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:49:47.800766+00:00
-- url     : https://prove2.me/theorems/653ce649-a437-498e-b3b0-745fc5ba37b8
-- title:
--   Assumption C (Contraction Assumption) with scalars $m$, $\rho$, $\alpha$
-- statement:
--   Fix a model as in Sections 2.1–2.2 (the definition `BertsekasShreve.Contraction.Model`), a subset $\bar B$ of the space $B$ of bounded real functions on $S$, a positive integer $m$ and real scalars $\rho,\alpha$. **Assumption C** holds with these data when:
--
--   1. $\bar B$ is closed in $B$ (supremum-norm topology);
--   2. $J_0\in\bar B$, and for all $J\in\bar B$ and $\mu\in M$ the functions $T(J)$ and $T_\mu(J)$ belong to $\bar B$;
--   3. for every $\pi=(\mu_0,\mu_1,\dots)\in\Pi$ and every $x\in S$ the limit $\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x)$ exists and is a real number;
--   4. $m\ge1$, $0<\rho<1$ and $0<\alpha$;
--   5. for all $\mu\in M$ and all $J,J'\in B$,
--   $$\|T_\mu(J)-T_\mu(J')\|\le\alpha\|J-J'\|;$$
--   6. for all $\mu_0,\dots,\mu_{m-1}\in M$ and all $J,J'\in\bar B$,
--   $$\|(T_{\mu_0}\cdots T_{\mu_{m-1}})(J)-(T_{\mu_0}\cdots T_{\mu_{m-1}})(J')\|\le\rho\|J-J'\|.$$
--
--   Condition 5 is required on all of $B$, a possibly larger set than the one in condition 6. The book's assumption reads "there exist $m$, $\rho$, $\alpha$"; here they are named parameters, so that results stated with these constants (such as Proposition 4.5) can refer to them.
--
--   **Formalization Note** Conditions 5 and 6 use `SupDistLe` from the model file: the bound includes the requirement that $T_\mu(J)(x)$ is real at every $x$, which is what the book's sup-norm bound means under its convention $\infty-\infty=\infty$. In condition 6 the tuple $\mu_0,\dots,\mu_{m-1}$ is the first $m$ entries of a policy $\pi$; every tuple arises this way.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 52–53, Assumption C, Eqs. (1)–(3) of Chapter 4

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Assumption C (Contraction Assumption), pp. 52–53, with the scalars `m`, `ρ`, `α` it
introduces made explicit parameters.

* `Bbar` is a closed subset of `B` (sup-norm topology of `ℓ^∞(S, ℝ)`);
* `J₀ ∈ B̄`, and `T(J)`, `T_μ(J)` lie in `B̄` for every `J ∈ B̄`, `μ ∈ M`;
* for every policy the limit (1) exists and is a real number at every `x`;
* `m` is a positive integer, `0 < ρ < 1`, `0 < α`;
* (2): `‖T_μ(J) − T_μ(J')‖ ≤ α ‖J − J'‖` for all `μ ∈ M` and all `J, J' ∈ B` (not only `B̄`);
* (3): `‖(T_{μ₀} ⋯ T_{μ_{m−1}})(J) − (T_{μ₀} ⋯ T_{μ_{m−1}})(J')‖ ≤ ρ ‖J − J'‖` for all
  `μ₀, …, μ_{m−1} ∈ M` and `J, J' ∈ B̄`; the tuple `μ₀, …, μ_{m−1}` is the first `m` entries of a
  policy `π`. -/
structure AssumptionC {S C : Type*} (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ) :
    Prop where
  isClosed : IsClosed Bbar
  J0_mem : ∃ J ∈ Bbar, P.J0 = toF J
  T_mem : ∀ J ∈ Bbar, ∃ J' ∈ Bbar, P.T (toF J) = toF J'
  Tmu_mem : ∀ μ : P.Selector, ∀ J ∈ Bbar, ∃ J' ∈ Bbar, P.Tmu μ (toF J) = toF J'
  limit_real : ∀ (π : P.Policy) (x : S), ∃ r : ℝ,
    Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (r : EReal))
  m_pos : 0 < m
  ρ_pos : 0 < ρ
  ρ_lt_one : ρ < 1
  α_pos : 0 < α
  lipschitz : ∀ (μ : P.Selector) (J J' : BFun S),
    SupDistLe (P.Tmu μ (toF J)) (P.Tmu μ (toF J')) (α * ‖J - J'‖)
  contraction : ∀ (π : P.Policy), ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
    SupDistLe (P.comp π m (toF J)) (P.comp π m (toF J')) (ρ * ‖J - J'‖)

end BertsekasShreve.Contraction


