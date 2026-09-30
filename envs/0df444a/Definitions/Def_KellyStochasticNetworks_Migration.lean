-- Prove2me | Definitions.Def_KellyStochasticNetworks_Migration
-- name    : KellyStochasticNetworks_Migration
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T15:24:16.294544+00:00
-- url     : https://prove2.me/theorems/89400c25-c461-4460-b872-e16610fffac7
-- title:
--   Migration processes: operators, rates, traffic equations and product form
-- statement:
--   The model of Chapter 2 of Kelly and Yudovina, *Stochastic Networks*: migration processes and
--   the objects their equilibrium analysis needs.
--
--   A state is a vector $n = (n_1, \dots, n_J)$ of non-negative integers, $n_j$ being the number of
--   individuals in **colony** $j$. Three operators move a single individual:
--   $$T^{jk}n \text{ moves one from } j \text{ to } k, \qquad T^{j\to}n \text{ removes one from } j,
--   \qquad T^{\to k}n \text{ adds one to } k.$$
--
--   A **closed migration process** has transitions only of the first kind, at rate
--   $q(n, T^{jk}n) = \lambda_{jk}\varphi_j(n_j)$, where $\varphi_j(0) = 0$. An **open migration
--   process** adds departures $q(n, T^{j\to}n) = \mu_j \varphi_j(n_j)$ and Poisson immigration
--   $q(n, T^{\to k}n) = \nu_k$.
--
--   The **traffic equations** determine $(\alpha_j)$ from the rates. For a closed process they are
--   $$\alpha_j > 0, \quad \sum_j \alpha_j = 1, \quad
--     \alpha_j \sum_k \lambda_{jk} = \sum_k \alpha_k \lambda_{kj},$$
--   equation (2.1); for an open process
--   $$\alpha_j\Bigl(\mu_j + \sum_k \lambda_{jk}\Bigr) = \nu_j + \sum_k \alpha_k \lambda_{kj},$$
--   equation (2.2).
--
--   The **product form** is built from $\Phi_j(m) = \prod_{r=1}^{m} \varphi_j(r)$, empty and equal
--   to $1$ at $m = 0$: the colony marginal is $\pi_j(m) = g_j^{-1}\alpha_j^{m}/\Phi_j(m)$ and the
--   joint distribution is $\pi(n) = \prod_j \pi_j(n_j)$.
--
--   Two auxiliary objects complete the chapter. The **M/M/1 queue** has state the number of
--   customers and rates $q(j, j+1) = \lambda$, $q(j, j-1) = \mu$. The **occupancy function**
--   $n(s)$ of section 2.5 counts the customers present at time $s$, given arrival times $a_i$ and
--   departure times $d_i$ of finitely many customers.
--
--   **Formalization Note** The state space is the type of functions from a finite index type of
--   colonies to the natural numbers. A rate matrix is a single real-valued function of two states,
--   assembled as a sum of indicator terms over the possible transitions; this is what lets the
--   equilibrium equations be stated as a sum over actual states, so that a transition out of an
--   empty colony — which would leave the state space — is simply absent rather than silently
--   reinterpreted through truncated subtraction. Occupancy counts use truncated natural
--   subtraction, and every use is guarded either by $\varphi_j(0) = 0$ or by an explicit
--   hypothesis that the source colony is non-empty. Throughout, $\lambda_{jj} = 0$ is imposed as a
--   hypothesis rather than built into the definitions.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 2, pp. 22-37 (PDF pp. 30-45): the M/M/1 rates p. 22, the operator T^{jk} and the closed migration rates pp. 26-27, the traffic equations (2.1) p. 27, the operators T^{j->}, T^{->k} and the open migration rates p. 30, the traffic equations (2.2) and the constants g_j p. 31, and the function n(.) of section 2.5 p. 36. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib

namespace KellyStochasticNetworks

/-- `Tjk j k n` transfers one individual from colony `j` to colony `k`.
This is the operator `T^{jk}` of Kelly–Yudovina, *Stochastic Networks*, p. 26. -/
def Tjk {J : ℕ} (j k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else if i = k then n k + 1 else n i

/-- `Tout j n` is the operator `T^{j→}` of p. 30: an individual leaves the system from
colony `j`. -/
def Tout {J : ℕ} (j : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else n i

/-- `Tin k n` is the operator `T^{→k}` of p. 30: an individual enters colony `k` from the
outside world. -/
def Tin {J : ℕ} (k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = k then n k + 1 else n i

/-- `phiProd φ j m` is the product `∏_{r=1}^{m} φ_j(r)` appearing in the product-form
distributions of Theorems 2.4 and 2.8; it is `1` when `m = 0`. -/
def phiProd {J : ℕ} (φ : Fin J → ℕ → ℝ) (j : Fin J) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 1 m, φ j r

/-- The transition rates of a **closed migration process** (p. 27): the only transitions are
`n ↦ T^{jk} n`, at rate `λ_{jk} φ_j(n_j)`.  The rate from a state to itself is zero because
`φ_j(0) = 0` is assumed wherever these rates are used. -/
noncomputable def closedMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ : Fin J → ℕ → ℝ) :
    (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  ∑ j, ∑ k, if m = Tjk j k n then lam j k * φ j (n j) else 0

/-- The transition rates of an **open migration process** (p. 30): transfers between colonies at
rate `λ_{jk} φ_j(n_j)`, departures from colony `j` at rate `μ_j φ_j(n_j)`, and Poisson
immigration into colony `k` at rate `ν_k`. -/
noncomputable def openMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (φ : Fin J → ℕ → ℝ) : (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  closedMigrationRates lam φ n m
    + (∑ j, if m = Tout j n then mu j * φ j (n j) else 0)
    + (∑ k, if m = Tin k n then nu k else 0)

/-- The **traffic equations** (2.1) of a closed migration process. -/
def ClosedTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (α : Fin J → ℝ) : Prop :=
  (∀ j, 0 < α j) ∧ (∑ j, α j = 1) ∧ ∀ j, α j * ∑ k, lam j k = ∑ k, α k * lam k j

/-- The **traffic equations** (2.2) of an open migration process. -/
def OpenTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu α : Fin J → ℝ) : Prop :=
  ∀ j, α j * (mu j + ∑ k, lam j k) = nu j + ∑ k, α k * lam k j

/-- The single-colony marginal `π_j(m) = g_j⁻¹ α_j^m / ∏_{r=1}^m φ_j(r)` of Theorem 2.8. -/
noncomputable def migrationMarginal {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (j : Fin J) (m : ℕ) : ℝ := (g j)⁻¹ * (α j ^ m / phiProd φ j m)

/-- The product-form distribution `π(n) = ∏_j π_j(n_j)` of Theorem 2.8. -/
noncomputable def openMigrationPi {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (n : Fin J → ℕ) : ℝ := ∏ j, migrationMarginal α g φ j (n j)

/-- The transition rates of an M/M/1 queue with arrival rate `lam` and service rate `mu`
(p. 22): `q(j, j+1) = lam` and `q(j, j-1) = mu`. -/
noncomputable def mm1Rates (lam mu : ℝ) : ℕ → ℕ → ℝ := fun j k =>
  if k = j + 1 then lam else if j = k + 1 then mu else 0

/-- The number of customers in the system at time `s`, for `N` customers whose arrival and
departure times are `a i` and `d i`.  This is the function `n(·)` of section 2.5. -/
noncomputable def occupancy {N : ℕ} (a d : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ i, Set.indicator (Set.Ico (a i) (d i)) (fun _ => (1 : ℝ)) s

end KellyStochasticNetworks


