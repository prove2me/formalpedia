-- Prove2me | Definitions.Def_LinearZeroSumMG_IsApproxCCE
-- name    : LinearZeroSumMG_IsApproxCCE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:09.846999+00:00
-- url     : https://prove2.me/theorems/a2b4ff1c-657e-4b7a-b56f-029e5275d09b
-- title:
--   (Approximate) coarse correlated equilibrium of a matrix game, (1a)–(1b), and CCE rules
-- statement:
--   Consider a two-player general-sum matrix game with payoff matrices $u_1,u_2:\mathcal A\times\mathcal A\to\mathbb R$, where P1 maximizes $u_1$ and P2 minimizes $u_2$. A joint distribution $\sigma\in\Delta(\mathcal A\times\mathcal A)$ with marginals $\mathcal P_1\sigma,\mathcal P_2\sigma$ is an **$\eta$-approximate coarse correlated equilibrium** if
--   $$
--   \mathbb E_{(a,b)\sim\sigma}[u_1(a,b)]\ge\mathbb E_{b\sim\mathcal P_2\sigma}[u_1(a',b)]-\eta\quad\forall a'\in\mathcal A,\qquad
--   \mathbb E_{(a,b)\sim\sigma}[u_2(a,b)]\le\mathbb E_{a\sim\mathcal P_1\sigma}[u_2(a,b')]+\eta\quad\forall b'\in\mathcal A .
--   $$
--   A **coarse correlated equilibrium (CCE)** is the case $\eta=0$, which is (1a)–(1b) of the paper; a $2\varepsilon$-CCE is the case $\eta=2\varepsilon$. A **CCE rule** is a Borel-measurable map that assigns to every pair $(u_1,u_2)$ one of its CCEs.
--
--   No unilateral, unconditional deviation from $\sigma$ gains a player more than $\eta$. A CCE always exists and can be computed by linear programming; Algorithm 2 plays the CCE of a rounded game.
--
--   **Formalization Note** The argument $x$ printed inside (1) plays no role and is dropped. The CCE rule is fixed in advance and depends only on the two payoff matrices, as Lemma 2's proof requires; measurability excludes only rules for which the analysis's expectations are undefined.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.1, (1a)–(1b), p.5; §3.2.1, p.12; Algorithm 2, line 3, p.11

import Mathlib

namespace LinearZeroSumMG

variable {A : Type*} [Fintype A]

/-- The marginal `𝒫₁σ ∈ Δ(𝒜)` of P1's action under a joint distribution `σ ∈ Δ(𝒜 × 𝒜)`. -/
def marg1 (σ : A × A → ℝ) (a : A) : ℝ := ∑ b, σ (a, b)

/-- The marginal `𝒫₂σ ∈ Δ(𝒜)` of P2's action under a joint distribution `σ ∈ Δ(𝒜 × 𝒜)`. -/
def marg2 (σ : A × A → ℝ) (b : A) : ℝ := ∑ a, σ (a, b)

/-- **(Approximate) coarse correlated equilibrium of a two-player general-sum matrix game.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.1, (1a)–(1b), p.5: "We sometimes
need to consider a general-sum matrix (or normal form) game with payoff matrices
`u_i ∈ ℝ^{|𝒜|×|𝒜|}, i ∈ {1, 2}` for two players denoted by P1 and P2. If P1 and P2 take actions `a`
and `b`, respectively, then P`i` receives a payoff `u_i(a, b)`. We use the convention that P1 tries to
maximize the payoff and P2 tries to minimize. A joint distribution `σ ∈ Δ(𝒜 × 𝒜)` of both players'
actions is called a Coarse Correlated Equilibrium … if it satisfies
`𝔼_{(a,b)∼σ}[u₁(x, a, b)] ≥ 𝔼_{b∼𝒫₂σ}[u₁(x, a', b)], ∀a' ∈ 𝒜` (1a),
`𝔼_{(a,b)∼σ}[u₂(x, a, b)] ≤ 𝔼_{a∼𝒫₁σ}[u₂(x, a, b')], ∀b' ∈ 𝒜` (1b),
where for `i ∈ {1, 2}`, `𝒫_iσ ∈ Δ(𝒜)` denotes the `i`-th marginal of `σ`." And §3.2.1, p.12:
"Here a `2ε`-approximate CCE policy is one that satisfies the definition (1) of CCE with an additive
`2ε` error on the RHS."

`IsApproxCCE η u₁ u₂ σ` says that `σ ∈ Δ(A × A)` and
`∑_{(a,b)} σ(a, b) u₁(a, b) ≥ ∑_b 𝒫₂σ(b) u₁(a', b) − η` for every `a'`, and
`∑_{(a,b)} σ(a, b) u₂(a, b) ≤ ∑_a 𝒫₁σ(a) u₂(a, b') + η` for every `b'`.
A CCE is the case `η = 0` (`IsCCE`), and a `2ε`-CCE the case `η = 2ε`.

**Formalization Note** The argument `x` printed inside (1) plays no role and is dropped; payoff
matrices are functions `A → A → ℝ` and distributions are elements of `stdSimplex ℝ (A × A)`. -/
def IsApproxCCE (η : ℝ) (u₁ u₂ : A → A → ℝ) (σ : A × A → ℝ) : Prop :=
  σ ∈ stdSimplex ℝ (A × A) ∧
  (∀ a' : A, ∑ ab : A × A, σ ab * u₁ ab.1 ab.2 ≥ ∑ b, marg2 σ b * u₁ a' b - η) ∧
  (∀ b' : A, ∑ ab : A × A, σ ab * u₂ ab.1 ab.2 ≤ ∑ a, marg1 σ a * u₂ a b' + η)

/-- A coarse correlated equilibrium ((1a)–(1b), arXiv:2002.07066v3, p.5): the case `η = 0`. -/
def IsCCE (u₁ u₂ : A → A → ℝ) (σ : A × A → ℝ) : Prop := IsApproxCCE 0 u₁ u₂ σ

/-- **A CCE rule** (Algorithm 2, line 3, arXiv:2002.07066v3, p.11: "let `σ̃(x)` be the CCE … of the
matrix game with payoff matrices `Q̃(x, ·, ·)` for P1 and `Q̰(x, ·, ·)` for P2"): a map that assigns to
every pair of payoff matrices `(u₁, u₂)` one of its coarse correlated equilibria, Borel-measurably in
`(u₁, u₂)`.

**Formalization Note** "The CCE" is read as a rule fixed in advance (a function of the two payoff
matrices only), as Lemma 2's proof requires. Measurability excludes only rules for which the
expectations of the analysis are undefined. -/
def IsCCERule [MeasurableSpace A] (cce : (A → A → ℝ) → (A → A → ℝ) → (A × A → ℝ)) : Prop :=
  Measurable (fun u : (A → A → ℝ) × (A → A → ℝ) => cce u.1 u.2) ∧
  ∀ u₁ u₂, IsCCE u₁ u₂ (cce u₁ u₂)

end LinearZeroSumMG


