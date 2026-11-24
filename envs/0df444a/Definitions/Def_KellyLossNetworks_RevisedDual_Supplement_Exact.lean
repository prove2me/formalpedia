-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
-- name    : KellyLossNetworks_RevisedDual_Supplement_Exact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:54:39.983458+00:00
-- url     : https://prove2.me/theorems/48bf19fd-9710-4c7b-8dd9-2dd2d30f5e4d
-- title:
--   Exact stationary quantities of a loss network: 𝒮(c), G(c), 𝔼^π, 1 − L_r, W^π, c_r^π, cov^π
-- statement:
--   Consider a loss network with links $j \in \{1,\dots,J\}$ and routes $r \in \mathcal R = \{1,\dots,R\}$, where a call on route $r$ uses $A_{jr}\in\mathbb Z_+$ circuits of link $j$, calls on route $r$ arrive at rate $\nu_r$, and link $j$ has capacity $c_j$. For an integer capacity vector $c$ let
--   $$\mathcal S(c)=\{n\in\mathbb Z_+^{\mathcal R}: An\le c\},\qquad G(c)=\sum_{n\in\mathcal S(c)}\prod_r\frac{\nu_r^{n_r}}{n_r!}.$$
--   The stationary distribution (1.2) is $\pi(n)=G(c)^{-1}\prod_r \nu_r^{n_r}/n_r!$ on $\mathcal S(c)$, and $\mathbb E^\pi$ denotes expectation under it. This file defines:
--
--   1. the acceptance probability $1-L_r = G(C-Ae_r)/G(C)$ of (1.5), where $Ae_r$ is the $r$-th column of $A$;
--   2. the rate of return $W^\pi(\nu;C)=\mathbb E^\pi\big(\sum_r w_r n_r\big)$ of §6.1 for real revenues $w_r$;
--   3. the implied cost $c_r^\pi = W^\pi(\nu;C)-W^\pi(\nu;C-Ae_r)$ of (6.3);
--   4. the covariance $\operatorname{cov}^\pi(n_r,n_{r'})=\mathbb E^\pi(n_rn_{r'})-\mathbb E^\pi n_r\,\mathbb E^\pi n_{r'}$.
--
--   These are the exact quantities of §§1.2 and 6.1 on which Theorems 6.1 and 6.4 and the limit theorems of §§2.4 and 3.2 are stated.
--
--   **Formalization Note** Nonnegative capacities use the published countable `LossLimits.partition` and `occupancyLaw`, including routes which use no link. Expectations are integrals against that law. Integer capacities extend the definitions to reduced capacities: if any capacity is negative, the partition and expectation are explicitly zero. The acceptance prefactor then vanishes. Polynomial observables are integrable by the product-Poisson tails.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 321, (1.2)–(1.4); p. 322, (1.5); p. 368, §6.1 and (6.3); p. 369, Theorem 6.4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **The state space** `𝒮(c) = {n ∈ ℤ₊^ℛ : An ≤ c}` of (1.2)–(1.4), for an *integer* capacity
vector `c`, so that the reduced capacities `C − Ae_r` of (1.5) and (6.3) are admissible.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 321, (1.2)–(1.4).

**Formalization Note.** Routes are `Fin R`, links `Fin J`, the incidence matrix `A` is
`ℕ`-valued (the general case `A_jr ∈ ℤ₊`). For `c ≥ 0` this is the published
`KellyStochasticNetworks.lossStates A c`; when some `c j < 0` the set is empty. A route whose
column of `A` is zero leaves `n_r` unbounded, so the set may be infinite. -/
def stateSpace {J R : ℕ} (A : Fin J → Fin R → ℕ) (c : Fin J → ℤ) : Set (Fin R → ℕ) :=
  {n | ∀ j, ((∑ r, A j r * n r : ℕ) : ℤ) ≤ c j}

/-- **The normalizing constant** `G(c) = Σ_{n ∈ 𝒮(c)} ∏_r ν_r^{n_r}/n_r!` of (1.4), with the
published product-form weight `KellyStochasticNetworks.lossWeight`.

Kelly (1991), p. 321, (1.4).

**Formalization Note.** The published `LossLimits.partition`, a `tsum` over the countable state space (the sum is finite unless some
route uses no link, and then it converges for every `ν`). `G(c) = 0` exactly when `𝒮(c)` is
empty, i.e. when some `c j < 0`. -/
noncomputable def partitionFn {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) : ℝ :=
  if ∀ j, 0 ≤ c j then
    KellyStochasticNetworks.LossLimits.partition A ν (fun j => (c j).toNat)
  else 0

/-- **Expectation under the stationary distribution** (1.2):
`𝔼^π f(n) = G(c)⁻¹ Σ_{n ∈ 𝒮(c)} f(n) ∏_r ν_r^{n_r}/n_r!`.

Kelly (1991), p. 321, (1.2).

**Formalization Note.** For nonnegative capacities this integrates against the published
`LossLimits.occupancyLaw`. For negative capacities there is no distribution and the
explicit extension is zero. All polynomial observables in these theorems are integrable
under the countable product-Poisson law. -/
noncomputable def expect {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) (f : (Fin R → ℕ) → ℝ) : ℝ :=
  if ∀ j, 0 ≤ c j then
    ∫ n, f n ∂KellyStochasticNetworks.LossLimits.occupancyLaw A ν (fun j => (c j).toNat)
  else 0

/-- The capacity vector `C ∈ ℤ₊^J` as an integer vector. -/
def capInt {J : ℕ} (C : Fin J → ℕ) : Fin J → ℤ := fun j => (C j : ℤ)

/-- **The reduced capacity** `c − Ae_r`: one call on route `r` removed, i.e. the whole column
`(A_jr)_j` of `A` subtracted. Kelly (1991), p. 322, (1.5), and p. 368, (6.3). -/
def reduceCap {J R : ℕ} (A : Fin J → Fin R → ℕ) (c : Fin J → ℤ) (r : Fin R) : Fin J → ℤ :=
  fun j => c j - (A j r : ℤ)

/-- **The acceptance probability** `1 − L_r = G(C)⁻¹ G(C − Ae_r)` of route `r` (1.5).

Kelly (1991), p. 322, (1.5).

**Formalization Note.** This is the exact acceptance probability of the stationary network
with capacities `c`. When `C − Ae_r` has a negative entry, `G(C − Ae_r) = 0` and the value is
`0` (a call on route `r` can never be accepted). -/
noncomputable def acceptance {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) (r : Fin R) : ℝ :=
  partitionFn A ν (reduceCap A c r) / partitionFn A ν c

/-- **The exact rate of return** `W^π(ν; c) = 𝔼^π(Σ_r w_r n_r)` of §6.1.

Kelly (1991), p. 368, §6.1.

**Formalization Note.** `w : Fin R → ℝ` are arbitrary real revenues. When `𝒮(c) = ∅` the value
is `0` (see `expect`). -/
noncomputable def revenue {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) (w : Fin R → ℝ) : ℝ :=
  expect A ν c (fun n => ∑ r, w r * (n r : ℝ))

/-- **The implied cost** `c_r^π = W^π(ν; C) − W^π(ν; C − Ae_r)` of (6.3).

Kelly (1991), p. 368, (6.3).

**Formalization Note.** When `C − Ae_r` has a negative entry, `W^π(ν; C − Ae_r)` is the junk
value `0`; in (6.2) the factor `1 − L_r^π = 0` then multiplies it, and in the cross-multiplied
form of Theorem 6.4 so does `𝔼^π n_r = 0`. -/
noncomputable def impliedCost {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) (w : Fin R → ℝ) (r : Fin R) : ℝ :=
  revenue A ν c w - revenue A ν (reduceCap A c r) w

/-- **The stationary covariance** `cov^π(n_r, n_{r'}) = 𝔼^π(n_r n_{r'}) − 𝔼^π n_r 𝔼^π n_{r'}`.

Kelly (1991), p. 369, Theorem 6.4. -/
noncomputable def covariance {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (c : Fin J → ℤ) (r r' : Fin R) : ℝ :=
  expect A ν c (fun n => (n r : ℝ) * (n r' : ℝ)) -
    expect A ν c (fun n => (n r : ℝ)) * expect A ν c (fun n => (n r' : ℝ))

end KellyLossNetworks.RevisedDual.Supplement


