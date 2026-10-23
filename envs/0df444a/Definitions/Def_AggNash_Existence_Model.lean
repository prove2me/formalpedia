-- Prove2me | Definitions.Def_AggNash_Existence_Model
-- name    : AggNash_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:18.179974+00:00
-- url     : https://prove2.me/theorems/f6fe6d77-f57d-4294-bf1e-18f577e6b1df
-- title:
--   (2.1), Definitions 2.1, 2.2, 2.5, Assumption 1, pp. 4–6 — sum-aggregative game, ε-PNE, convexified cost, generators, η-stability
-- statement:
--   This file sets up the non-convex sum-aggregative game $\Gamma$ of Liu, Oudjane and Wan and its convexification $\tilde\Gamma$.
--
--   **The game.** There are $n$ players $N=\{1,\dots,n\}$. Player $i$ chooses an action $x_i$ in a set $\mathcal X_i\subset\mathbb R^d$ that is compact but not necessarily convex; $\tilde{\mathcal X}_i:=\operatorname{conv}\mathcal X_i$ is its convex hull. For $q\times d$ matrices $A_1,\dots,A_n$ and functions $\theta_i$, the cost of player $i$ at a profile $x=(x_1,\dots,x_n)$ is
--
--   $$
--   f_i(x_i,x_{-i}) = \theta_i\Big(x_i,\ \frac1n\sum_{j\in N}A_jx_j\Big). \tag{2.1}
--   $$
--
--   The aggregate $\frac1n\sum_j A_jx_j$ runs over all players, including player $i$.
--
--   **Standing assumptions** (p. 4). Every $\mathcal X_i$ is compact and nonempty, with diameter at most $\Delta>0$. Every $A_i$ has spectral norm $\|A_i\|_2\le M$, with $M>0$. The functions $\theta_i$ are defined on $\mathcal X_i\times\Omega$, where $\Omega\subset\mathbb R^q$ is a neighbourhood of the aggregate set $\{\frac1n\sum_j A_jy_j \mid y_j\in\tilde{\mathcal X}_j\}$.
--
--   **Assumption 1** (p. 5). (1) For every $i$ and $y\in\Omega$, $x_i\mapsto\theta_i(x_i,y)$ is lower semicontinuous on $\mathcal X_i$. (2) There are constants $H>0$, $\gamma>0$ such that for every $i$ and $x_i\in\mathcal X_i$, $|\theta_i(x_i,y')-\theta_i(x_i,y)|\le H\|y'-y\|^\gamma$ for all $y,y'\in\Omega$.
--
--   **$\epsilon$-PNE** (Definition 2.1). For $\epsilon\ge0$, a profile $x^\epsilon$ in the product of the action sets is an $\epsilon$-pure Nash equilibrium if, for every player $i$, $f_i(x^\epsilon_i,x^\epsilon_{-i})\le f_i(x_i,x^\epsilon_{-i})+\epsilon$ for every feasible $x_i$. The same definition, with action sets $\tilde{\mathcal X}_i$ and costs $\tilde f_i$, gives the $\epsilon$-PNE of $\tilde\Gamma$.
--
--   **Convexified game** (Definition 2.2). With $\mathcal S_d$ the probability simplex in $\mathbb R^{d+1}$, the cost of player $i$ in $\tilde\Gamma$ is
--
--   $$
--   \tilde f_i(x_i,x_{-i}) = \inf\Big\{\sum_{k=1}^{d+1}\alpha^kf_i(z^k,x_{-i}) \ \Big|\ \alpha\in\mathcal S_d,\ z^1,\dots,z^{d+1}\in\mathcal X_i,\ x_i=\sum_{k=1}^{d+1}\alpha^kz^k\Big\}. \tag{2.2}
--   $$
--
--   A **generator** $Z(i,x)$ is the set of points $z^k$ with positive weight $\alpha^k>0$ in a minimizer $(\alpha,z)$ of (2.2).
--
--   **Stability** (Definition 2.5). For $\eta\ge0$, $\tilde x$ satisfies the $\eta$-stability condition with respect to a generator profile $(Z(i,\tilde x))_i$ if $\tilde f_i(x_i,\tilde x_{-i})\le\tilde f_i(\tilde x_i,\tilde x_{-i})+\eta$ for every $i$ and every $x_i\in Z(i,\tilde x)$.
--
--   These objects are shared by every statement of the mission: the existence of an approximate equilibrium of $\Gamma$ is obtained by disaggregating an equilibrium of $\tilde\Gamma$ over its generators.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and players are `Fin n`. A $q\times d$ matrix is a continuous linear map `E d →L[ℝ] E q`; its operator norm between Euclidean spaces is the spectral norm $\|A\|_2$. A deviation $(y_i,x_{-i})$ is `Function.update x i y`, so $\tilde f_i$ evaluates $f_i(z^k,x_{-i})$ at the profile in which player $i$ plays $z^k$. The functions $\theta_i$ are total in Lean, but every hypothesis on them is restricted to $\mathcal X_i\times\Omega$. The infimum in (2.2) is a real `sInf`, which would be $0$ on an empty or unbounded-below set; under the standing assumptions and Assumption 1 the set is nonempty and bounded below at every profile in $\tilde{\mathcal X}$, which is where the theorems use it. Two choices differ from the printed text. (i) Nonempty action sets are added: with an empty $\mathcal X_i$ there is no profile at all. (ii) The paper calls the set of all $d+1$ components of $z$ the generator; this mission takes only the components with positive weight, as the paper's own Lemma 5.7 does ($Z(i,\tilde x)=\{x_i^1,\dots,x_i^{l_i}\}$ with weights in $\mathcal S_{l_i-1}$). With zero-weight components kept, Lemma 5.6, Theorem 2.7 and Proposition 2.4 fail. Hölder's power $\|y'-y\|^\gamma$ is `Real.rpow`; no bound $\gamma\le1$ is imposed.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, pp. 3–6, Notation (p. 3), (2.1), (2.2), Definitions 2.1, 2.2, 2.5, Assumption 1; generator support as in Lemma 5.7, p. 20

import Mathlib

namespace AggNash.Existence

/-- The Euclidean space `ℝᵈ` with the `ℓ²` norm (Notation, p. 3). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The aggregate `(1/n) ∑_{j ∈ N} Aⱼ xⱼ` of a profile `x` (p. 4, (2.1)). The matrices `Aⱼ` are
continuous linear maps `ℝᵈ → ℝ^q`, whose operator norm is the spectral norm `‖Aⱼ‖₂`. -/
noncomputable def aggregate {n d q : ℕ} (A : Fin n → (E d →L[ℝ] E q)) (x : Fin n → E d) : E q :=
  (n : ℝ)⁻¹ • ∑ j, A j (x j)

/-- The set `{(1/n) ∑_{j ∈ N} Aⱼ yⱼ | yⱼ ∈ 𝒳̃ⱼ, ∀ j ∈ N}` of aggregates of profiles of the
convexified action sets `𝒳̃ⱼ = conv 𝒳ⱼ` (p. 4). -/
def aggSet {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q)) : Set (E q) :=
  {v | ∃ y : Fin n → E d, (∀ j, y j ∈ convexHull ℝ (X j)) ∧ v = aggregate A y}

/-- The cost `fᵢ(xᵢ, x₋ᵢ) = θᵢ(xᵢ, (1/n) ∑ⱼ Aⱼ xⱼ)` of player `i` at the profile `x` (2.1).
The cost `fᵢ(yᵢ, x₋ᵢ)` of a unilateral deviation is `cost θ A i (Function.update x i yᵢ)`. -/
noncomputable def cost {n d q : ℕ} (θ : Fin n → E d → E q → ℝ) (A : Fin n → (E d →L[ℝ] E q))
    (i : Fin n) (x : Fin n → E d) : ℝ :=
  θ i (x i) (aggregate A x)

/-- Definition 2.1 (p. 4): `x` is an `ε`-pure Nash equilibrium of the game with action sets `S`
and costs `c`: `x ∈ ∏ᵢ Sᵢ`, and for each player `i`, `cᵢ(xᵢ, x₋ᵢ) ≤ cᵢ(yᵢ, x₋ᵢ) + ε` for all
`yᵢ ∈ Sᵢ`. With `S = X`, `c = cost θ A` this is the game `Γ`; with `S = conv X`,
`c = convCost X θ A` it is the convexified game `Γ̃` (p. 5). `ε = 0` is a pure Nash equilibrium. -/
def IsEpsPNE {n d : ℕ} (S : Fin n → Set (E d)) (c : Fin n → (Fin n → E d) → ℝ) (ε : ℝ)
    (x : Fin n → E d) : Prop :=
  (∀ i, x i ∈ S i) ∧ ∀ i, ∀ y ∈ S i, c i x ≤ c i (Function.update x i y) + ε

/-- The convexified cost (2.2) (Definition 2.2, p. 4):
`f̃ᵢ(xᵢ, x₋ᵢ) = inf { ∑_{k=1}^{d+1} αᵏ fᵢ(zᵏ, x₋ᵢ) | α ∈ 𝒮_d, zᵏ ∈ 𝒳ᵢ, xᵢ = ∑ₖ αᵏ zᵏ }`,
where `𝒮_d` is the probability simplex in `ℝ^{d+1}`. Each `fᵢ(zᵏ, x₋ᵢ)` is evaluated at the
profile in which player `i` plays `zᵏ` (so the aggregate contains `Aᵢ zᵏ`). -/
noncomputable def convCost {n d q : ℕ} (X : Fin n → Set (E d)) (θ : Fin n → E d → E q → ℝ)
    (A : Fin n → (E d →L[ℝ] E q)) (i : Fin n) (x : Fin n → E d) : ℝ :=
  sInf {v | ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ z : Fin (d + 1) → E d, (∀ k, z k ∈ X i) ∧
    ∑ k, α k • z k = x i ∧ v = ∑ k, α k * cost θ A i (Function.update x i (z k))}

/-- Generators (Definition 2.2, p. 5): `Z` is a generator for `(i, x)` if there is a minimizer
`(α, z) ∈ 𝒮_d × 𝒳ᵢ^{d+1}` of (2.2) at `x` and `Z` is the set of the components `zᵏ` that carry
positive weight `αᵏ > 0`. -/
def IsGenerator {n d q : ℕ} (X : Fin n → Set (E d)) (θ : Fin n → E d → E q → ℝ)
    (A : Fin n → (E d →L[ℝ] E q)) (i : Fin n) (x : Fin n → E d) (Z : Set (E d)) : Prop :=
  ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ z : Fin (d + 1) → E d, (∀ k, z k ∈ X i) ∧
    ∑ k, α k • z k = x i ∧
    ∑ k, α k * cost θ A i (Function.update x i (z k)) = convCost X θ A i x ∧
    Z = {y | ∃ k, 0 < α k ∧ z k = y}

/-- Definition 2.5 (p. 6): `x̃` satisfies the `η`-stability condition with respect to the
generator profile `Z = (Z(i, x̃))ᵢ` if `f̃ᵢ(xᵢ, x̃₋ᵢ) ≤ f̃ᵢ(x̃ᵢ, x̃₋ᵢ) + η` for every player `i`
and every `xᵢ ∈ Z(i, x̃)`. -/
def IsStable {n d q : ℕ} (X : Fin n → Set (E d)) (θ : Fin n → E d → E q → ℝ)
    (A : Fin n → (E d →L[ℝ] E q)) (η : ℝ) (x : Fin n → E d) (Z : Fin n → Set (E d)) : Prop :=
  ∀ i, ∀ y ∈ Z i, convCost X θ A i (Function.update x i y) ≤ convCost X θ A i x + η

/-- Assumption 1 (p. 5): (1) for every player `i` and `y ∈ Ω`, `xᵢ ↦ θᵢ(xᵢ, y)` is lower
semicontinuous on `𝒳ᵢ`; (2) there are `H > 0`, `γ > 0` such that for every `i` and `xᵢ ∈ 𝒳ᵢ`,
`y ↦ θᵢ(xᵢ, y)` is `(H, γ)`-Hölder on `Ω`: `|θᵢ(xᵢ, y') − θᵢ(xᵢ, y)| ≤ H ‖y' − y‖^γ` (2.3). -/
def Assumption1 {n d q : ℕ} (X : Fin n → Set (E d)) (Ω : Set (E q))
    (θ : Fin n → E d → E q → ℝ) (H γ : ℝ) : Prop :=
  (∀ i, ∀ y ∈ Ω, LowerSemicontinuousOn (fun z => θ i z y) (X i)) ∧ 0 < H ∧ 0 < γ ∧
    ∀ i, ∀ z ∈ X i, ∀ y ∈ Ω, ∀ y' ∈ Ω, |θ i z y' - θ i z y| ≤ H * ‖y' - y‖ ^ γ

/-- The standing assumptions of §2.1 (p. 4): every action set `𝒳ᵢ` is compact (closed and
bounded in `ℝᵈ`) and nonempty, with diameter at most `Δ > 0`; every matrix satisfies
`‖Aᵢ‖₂ ≤ M` with `M > 0`; and `Ω` is a neighbourhood of the aggregate set `aggSet X A`. -/
def StandingHyp {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (Ω : Set (E q)) (Δ M : ℝ) : Prop :=
  (∀ i, IsCompact (X i)) ∧ (∀ i, (X i).Nonempty) ∧ 0 < Δ ∧ (∀ i, Metric.diam (X i) ≤ Δ) ∧
    0 < M ∧ (∀ i, ‖A i‖ ≤ M) ∧ Ω ∈ nhdsSet (aggSet X A)

end AggNash.Existence


