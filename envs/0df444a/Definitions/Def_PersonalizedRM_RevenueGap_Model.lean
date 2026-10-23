-- Prove2me | Definitions.Def_PersonalizedRM_RevenueGap_Model
-- name    : PersonalizedRM_RevenueGap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:15.59678+00:00
-- url     : https://prove2.me/theorems/4e48b1fd-b4ff-4c7e-806d-353ca8615106
-- title:
--   §3–§4, pp. 8–17, ec1 — personalized MNL (1), ℓ1-constrained MLE, revenue f_z, oracle decisions, Assumptions 1–2
-- statement:
--   This file sets up the personalized multinomial-logit (MNL) model of Chen, Owen, Pixton and Simchi-Levi and every object their revenue-gap analysis uses.
--
--   **Products, features and prices (p. 8).** There are $J$ products and a no-purchase option $0$. A customer has a feature vector $z \in \mathbb R^d$ with $\|z\|_\infty \le 1$. Prices lie in $[p_{\min}, 1]$ with $0 < p_{\min} \le 1$, and $\mathcal P = [p_{\min}, 1]^J$ is the price box. For product $j$ at price $p_j$ the feature–price vector is $x = (z, p_j) \in \mathbb R^{d+1}$.
--
--   **Parameter and logit model (pp. 8, 12).** The parameter is $\theta = (\gamma_1^\top, \beta_1, \dots, \gamma_J^\top, \beta_J)^\top \in \mathbb R^{J(d+1)}$, with the Euclidean norm $\|\theta\|_2$ and the $\ell_1$ norm $\|\theta\|_1 = \sum_{j,k} |\theta_{jk}|$. The mean utility of product $j$ is $V_j = \langle \gamma_j, z\rangle + \beta_j p_j$. Offered an assortment $S \subseteq [J]$ at prices $p$, the customer chooses $j \in S$ with probability
--
--   $$\mathbb P_z(j; S, p, \theta) = \frac{e^{V_j}}{1 + \sum_{l \in S} e^{V_l}}, \qquad \mathbb P_z(0; S, p, \theta) = \frac{1}{1 + \sum_{l \in S} e^{V_l}}, \tag{1}$$
--
--   and a product outside $S$ with probability $0$.
--
--   **Revenue and oracle decisions (p. 16).** The expected revenue is $f_z(S, p; \theta) = \sum_{j \in S} p_j \mathbb P_z(j; S, p, \theta)$. Given a family $\mathcal S$ of feasible assortments, $(S, p)$ is an oracle decision under $\theta$ at $z$ when $S \in \mathcal S$, $p \in \mathcal P$ and $(S, p)$ maximizes $f_z(\cdot, \cdot; \theta)$ over $\mathcal S \times \mathcal P$.
--
--   **Data and estimator (pp. 9–10).** The sample consists of $n$ transactions $(z_i, S_i, p_i, y_i)$, with outcome $y_i \in \{0, 1, \dots, J\}$. The negative log-likelihood is
--
--   $$\ell_n(\theta) = -\frac1n \sum_{i=1}^n \log \mathbb P_{z_i}(y_i; S_i, p_i, \theta),$$
--
--   and $\hat\theta$ is an $\ell_1$-constrained maximum likelihood estimate: $\|\hat\theta\|_1 \le R$ and $\hat\theta$ minimizes $\ell_n$ over the ball $\|\theta\|_1 \le R$.
--
--   **Sub-Gaussian vectors (p. ec1).** A random vector $X \in \mathbb R^m$ is sub-Gaussian with norm at most $\psi$ when $(\mathbb E|\langle X, w\rangle|^q)^{1/q} \le \psi \sqrt q$ for every $w$ with $\|w\|_2 \le 1$ and every $q \ge 1$.
--
--   **Assumption 1 (p. 12).** The data are measurable, $\|z_i\|_\infty \le 1$ and $p_i \in \mathcal P$. (b) For each product $j$ the vectors $x_{ij} = (z_i, p_{ij})$ are independent across $i$, each sub-Gaussian with norm at most $\psi$. (a) Given the features and prices, the outcomes are independent, and $y_i$ follows the logit model (1) at the true parameter $\theta^*$ (well-specification).
--
--   **Assumption 2 (p. 13).** Let $\mathcal I_j = \{i : j \in S_i\}$ and $n_j = |\mathcal I_j|$. (a) $n_j \ge \nu n$ for every $j$, with $\nu > 0$. (b) The matrix $\Sigma_{\mathcal I_j} = \frac1{n_j} \sum_{i \in \mathcal I_j} \mathbb E(x_{ij} x_{ij}^\top)$ satisfies $\lambda_{\min}(\Sigma_{\mathcal I_j}) \ge \rho > 0$ for every $j$.
--
--   **Constants (p. 16, p. ec4).**
--
--   $$c = \frac{e^{-R}}{[1 + e^{-R} + (J-1) e^R]^2}, \qquad \eta = \frac{e^{-R} \nu \rho}{2[1 + e^{-R} + (J-1)e^R]^2} = \frac{\nu\rho c}{2}. \tag{6}$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $\theta$ lives in `EuclideanSpace ℝ (Fin J × Fin (d+1))`, so `‖θ‖` is the Euclidean norm; coordinate $(j, k)$ is $\gamma_{jk}$ for $k < d$ and $\beta_j$ for $k = d$, and $x = (z, p_j)$ is `Fin.snoc z p_j`. Outcomes are `Option (Fin J)`, with `none` the no-purchase option. The historical assortments $S_i$ are deterministic, as Assumption 2 treats them. Assumption 1(a) and well-specification are encoded by realizing each outcome as an inverse-CDF draw from the MNL law at $\theta^*$, driven by a uniform variable $u_i$ on $[0,1]$; the $u_i$ are independent of each other and of all features and prices. Any data distribution satisfying (a) has such a realization on an enlarged probability space. $\lambda_{\min}(\Sigma_{\mathcal I_j}) \ge \rho$ is written as the quadratic-form bound $v^\top \Sigma_{\mathcal I_j} v \ge \rho \|v\|_2^2$. $\nu$ is any positive constant with $n_j \ge \nu n$, not necessarily $\min_j n_j/n$. Two printed requirements are dropped, which makes every statement stronger: $\nu \le 1/J$ (false when assortments overlap), and the unused clause $\max_{i,j} \lambda_{\min}(\mathbb E\, x_{ij}x_{ij}^\top) > 0$ of Assumption 2(b).
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), pp. 8–17 and ec1, (1), (6), Assumptions 1–2, EC.1

import Mathlib

namespace PersonalizedRM.RevenueGap

open MeasureTheory ProbabilityTheory

/-- The parameter `θ = (γ₁ᵀ, β₁, …, γ_Jᵀ, β_J)ᵀ` (p. 12): coordinate `(j, k)` is `γ_{jk}` for
`k < d` and `β_j` for `k = Fin.last d`. It lives in `EuclideanSpace`, so `‖θ‖` is the paper's
ℓ2 norm `‖θ‖₂`. -/
abbrev Param (J d : ℕ) := EuclideanSpace ℝ (Fin J × Fin (d + 1))

/-- The feature–price vector `x = (z, p_j) ∈ ℝ^{d+1}`; its last coordinate is the price. -/
def featPrice {d : ℕ} (z : Fin d → ℝ) (pj : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc z pj

/-- The mean utility `V_j = ⟨γ_j, z⟩ + β_j p_j` of product `j` (p. 8). -/
def utility {J d : ℕ} (θ : Param J d) (z : Fin d → ℝ) (p : Fin J → ℝ) (j : Fin J) : ℝ :=
  ∑ k, θ (j, k) * featPrice z (p j) k

/-- The ℓ1 norm `‖θ‖₁ = Σ |θ_{jk}|` (p. 10). -/
def l1norm {J d : ℕ} (θ : Param J d) : ℝ :=
  ∑ jk, |θ jk|

/-- The MNL choice probabilities (1), p. 8. `none` is the no-purchase option `0`; a product
outside the offered assortment `S` is chosen with probability `0`. -/
noncomputable def choiceProb {J d : ℕ} (θ : Param J d) (z : Fin d → ℝ) (S : Finset (Fin J))
    (p : Fin J → ℝ) : Option (Fin J) → ℝ
  | none => 1 / (1 + ∑ l ∈ S, Real.exp (utility θ z p l))
  | some j =>
      if j ∈ S then Real.exp (utility θ z p j) / (1 + ∑ l ∈ S, Real.exp (utility θ z p l))
      else 0

/-- The expected revenue `f_z(S, p; θ) = Σ_{j∈S} p_j P_z(j; S, p, θ)` (p. 16). -/
noncomputable def revenue {J d : ℕ} (θ : Param J d) (z : Fin d → ℝ) (S : Finset (Fin J))
    (p : Fin J → ℝ) : ℝ :=
  ∑ j ∈ S, p j * choiceProb θ z S p (some j)

/-- The price box `P = [p_min, 1]^J` (p. 8, with `p_max = 1`). -/
def priceBox (J : ℕ) (pmin : ℝ) : Set (Fin J → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc pmin 1)

/-- `(S, p) ∈ argmax_{S'∈𝒮, p'∈P} f_z(S', p'; θ)` (p. 16): an optimal assortment and pricing
decision for the feature vector `z` under the parameter `θ`. -/
def IsOracleDecision {J d : ℕ} (𝒮 : Set (Finset (Fin J))) (pmin : ℝ) (θ : Param J d)
    (z : Fin d → ℝ) (S : Finset (Fin J)) (p : Fin J → ℝ) : Prop :=
  S ∈ 𝒮 ∧ p ∈ priceBox J pmin ∧
    ∀ S' ∈ 𝒮, ∀ p' ∈ priceBox J pmin, revenue θ z S' p' ≤ revenue θ z S p

/-- The negative log-likelihood `ℓ_n(θ) = −(1/n) Σ_i log P_{z_i}(y_i; S_i, p_i, θ)` (p. 10) of
the sample `T = {(z_i, S_i, p_i, y_i)}_{i=1}^n`. -/
noncomputable def negLogLik {n J d : ℕ} (S : Fin n → Finset (Fin J)) (z : Fin n → Fin d → ℝ)
    (p : Fin n → Fin J → ℝ) (y : Fin n → Option (Fin J)) (θ : Param J d) : ℝ :=
  -(1 / (n : ℝ)) * ∑ i, Real.log (choiceProb θ (z i) (S i) (p i) (y i))

/-- `θhat` is an ℓ1-constrained maximum likelihood estimate (p. 10): it minimizes `ℓ` over the
ℓ1 ball `‖θ‖₁ ≤ R`. -/
def IsConstrainedMLE {J d : ℕ} (R : ℝ) (ℓ : Param J d → ℝ) (θhat : Param J d) : Prop :=
  l1norm θhat ≤ R ∧ ∀ θ, l1norm θ ≤ R → ℓ θhat ≤ ℓ θ

/-- Inverse-CDF draw from the probabilities `q` on `S ∪ {none}`: the first `j ∈ S` (in the order
of `Fin J`) with `u < Σ_{l∈S, l≤j} q(some l)`, and `none` if there is no such `j`. When `u` is
uniform on `[0, 1]`, the draw equals `some j` with probability `q (some j)` for `j ∈ S`, and
`none` with probability `1 − Σ_{j∈S} q (some j)`. -/
noncomputable def mnlDraw {J : ℕ} (q : Option (Fin J) → ℝ) (S : Finset (Fin J)) (u : ℝ) :
    Option (Fin J) :=
  let T := S.filter (fun j => u < ∑ l ∈ S.filter (· ≤ j), q (some l))
  if h : T.Nonempty then some (T.min' h) else none

/-- The random vector `X` is sub-Gaussian with sub-Gaussian norm at most `ψ`, in the moment form of
EC.1 (p. ec1): for every `w` in the Euclidean unit ball and every `q ≥ 1`,
`(E|⟨X, w⟩|^q)^{1/q} ≤ ψ √q`. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (X : Ω → Fin m → ℝ) (ψ : ℝ) : Prop :=
  ∀ w : Fin m → ℝ, ∑ k, w k ^ 2 ≤ 1 → ∀ q : ℝ, 1 ≤ q →
    (∫ ω, |∑ k, w k * X ω k| ^ q ∂P) ^ (1 / q) ≤ ψ * Real.sqrt q

/-- `I_j = {i : j ∈ S_i}`, the transactions that offer product `j` (Assumption 2(a), p. 13). -/
def offered {n J : ℕ} (S : Fin n → Finset (Fin J)) (j : Fin J) : Finset (Fin n) :=
  Finset.univ.filter (fun i => j ∈ S i)

/-- Assumption 1 (p. 12) together with the standing data conventions of pp. 8–12.

The historical assortments `S i` are deterministic; the features `z i`, the prices `price i` and
the outcomes `y i` are random. Assumption 1(a) and well-specification (p. 12: the outcomes follow
the logit model at the true parameter `θstar`) are encoded by realizing every outcome as the
inverse-CDF draw `mnlDraw` of the MNL law at `θstar` from a uniform variable `u i`, the `u i`
being independent of each other and of all features and prices. Assumption 1(b): for each product
`j` the vectors `x_ij = (z_i, p_ij)` are independent across `i`, each sub-Gaussian with norm at
most `ψ`. -/
structure Assumption1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n J d : ℕ}
    (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ) (price : Fin n → Ω → Fin J → ℝ)
    (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J)) (θstar : Param J d) (pmin ψ : ℝ) :
    Prop where
  /-- `p_min > 0` (p. 8) -/
  pmin_pos : 0 < pmin
  /-- `p_min ≤ p_max = 1` (p. 8) -/
  pmin_le_one : pmin ≤ 1
  measurable_z : ∀ i, Measurable (z i)
  measurable_price : ∀ i, Measurable (price i)
  measurable_u : ∀ i, Measurable (u i)
  /-- `‖z‖∞ ≤ 1` (p. 8) -/
  z_bdd : ∀ i ω k, |z i ω k| ≤ 1
  /-- `p_i ∈ P = [p_min, 1]^J` (p. 8) -/
  price_mem : ∀ i ω, price i ω ∈ priceBox J pmin
  /-- Assumption 1(b): for each `j`, the `x_ij` are independent across `i` -/
  indep_x : ∀ j, iIndepFun (fun i ω => featPrice (z i ω) (price i ω j)) P
  /-- Assumption 1(b): uniform sub-Gaussian norm `ψ` -/
  subGaussian : ∀ i j, IsSubGaussianVec P (fun ω => featPrice (z i ω) (price i ω j)) ψ
  u_uniform : ∀ i, P.map (u i) = volume.restrict (Set.Icc (0 : ℝ) 1)
  u_iIndep : iIndepFun u P
  u_indep_x : IndepFun (fun ω i => u i ω) (fun ω => (fun i => z i ω, fun i => price i ω)) P
  /-- Assumption 1(a) and well-specification: `y_i` is drawn from the MNL law (1) at `θstar` -/
  y_eq : ∀ i ω, y i ω = mnlDraw (choiceProb θstar (z i ω) (S i) (price i ω)) (S i) (u i ω)

/-- Assumption 2 (p. 13). (a) Every product is offered in at least `ν n` transactions, `ν > 0`.
(b) `λ_min(Σ_{I_j}) ≥ ρ > 0` for `Σ_{I_j} = (1/n_j) Σ_{i∈I_j} E(x_ij x_ijᵀ)`, written as the
quadratic-form bound `vᵀ Σ_{I_j} v ≥ ρ ‖v‖₂²`. -/
structure Assumption2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n J d : ℕ}
    (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ) (price : Fin n → Ω → Fin J → ℝ)
    (ν ρ : ℝ) : Prop where
  nu_pos : 0 < ν
  /-- Assumption 2(a): `n_j ≥ ν n` -/
  offered_ge : ∀ j, ν * n ≤ ((offered S j).card : ℝ)
  rho_pos : 0 < ρ
  /-- Assumption 2(b): `λ_min(Σ_{I_j}) ≥ ρ` -/
  min_eig : ∀ j (v : Fin (d + 1) → ℝ), ρ * ∑ k, v k ^ 2 ≤
    (1 / ((offered S j).card : ℝ)) * ∑ i ∈ offered S j,
      ∫ ω, (∑ k, v k * featPrice (z i ω) (price i ω j) k) ^ 2 ∂P

/-- `c = exp(−R) / [1 + exp(−R) + (J − 1) exp(R)]²` (p. ec4). -/
noncomputable def cMin (J : ℕ) (R : ℝ) : ℝ :=
  Real.exp (-R) / (1 + Real.exp (-R) + ((J : ℝ) - 1) * Real.exp R) ^ 2

/-- The strong convexity parameter `η = exp(−R) ν ρ / (2[1 + exp(−R) + (J − 1) exp(R)]²)` of (6),
p. 16, i.e. `η = ν ρ c / 2`. -/
noncomputable def etaSC (J : ℕ) (R ν ρ : ℝ) : ℝ :=
  ν * ρ * cMin J R / 2

end PersonalizedRM.RevenueGap


