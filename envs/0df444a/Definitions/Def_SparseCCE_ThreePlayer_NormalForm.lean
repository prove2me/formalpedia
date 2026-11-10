-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_NormalForm
-- name    : SparseCCE_ThreePlayer_NormalForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:04:23.875449+00:00
-- url     : https://prove2.me/theorems/f6b3c9e0-9d54-4c3a-8bb1-a973d16a0d26
-- title:
--   Normal-form games: distributions, CCE gap and $\varepsilon$-CCE, $T$-sparse mixtures, two-player marginals
-- statement:
--   For a finite set $S$, $p:S\to\mathbb R$ is a **distribution** ($p\in\Delta(S)$) if $p\ge 0$ and $\sum_s p(s)=1$.
--
--   A normal-form game has a finite set of players $j$, finite action sets $B_j$ and utilities $U_j:B\to\mathbb R$, $B=\prod_j B_j$. For a law $\mu$ on $B$:
--   - $U_j(\mu)=\sum_b \mu(b)U_j(b)$;
--   - $U_j(D,\mu_{-j})=\sum_b\mu(b)\sum_{a}D(a)\,U_j(b_{j\leftarrow a})$, the utility of $j$ when it plays an action drawn from $D\in\Delta(B_j)$ independently of $b_{-j}\sim\mu_{-j}$;
--   - $\mu$ is an **$\varepsilon$-approximate coarse correlated equilibrium** ($\varepsilon$-CCE), for $\varepsilon\ge0$, if $\mu\in\Delta(B)$ and $U_j(D,\mu_{-j})-U_j(\mu)\le\varepsilon$ for every player $j$ and every $D\in\Delta(B_j)$, i.e. $\mathrm{CCEGap}_j(\mu)=\max_{D}U_j(D,\mu_{-j})-U_j(\mu)\le\varepsilon$.
--
--   The **mixture** of weights $w\in\mathbb R^T$ and components $p^{(t)}_j$ is $\mu(b)=\sum_{t=1}^T w_t\prod_j p^{(t)}_j(b_j)$; $\mu$ is **$T$-sparse** if it is such a mixture with $w\in\Delta([T])$ and every $p^{(t)}_j\in\Delta(B_j)$ (weights may be zero).
--
--   $\mu_{ik}$ is the joint law of $(b_i,b_k)$ under $\mu$, as a real matrix with rows indexed by $B_i$ and columns by $B_k$.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §2.1–2.2, Definitions 2.1–2.2, pp. 12–13.

import Mathlib

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- `p` is a probability distribution on the finite set `S`: nonnegative weights summing to one
(`Δ(S)`, §2.1, p. 12). -/
def IsDist {S : Type*} [Fintype S] (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ j, Fintype (B j)]
  [∀ j, DecidableEq (B j)]

/-- Expected utility `U_j(μ) = E_{b∼μ}[U_j(b)]` of player `j` under a law `μ` of action profiles
(§2.2, p. 12). -/
def expUtil (U : ι → ((j : ι) → B j) → ℝ) (j : ι) (μ : ((j : ι) → B j) → ℝ) : ℝ :=
  ∑ b, μ b * U j b

/-- `U_j(D_j, μ_{-j})`: the expected utility of `j` when it plays an action drawn from `D`,
independently of the opponents' actions `b_{-j} ∼ μ_{-j}` (Definition 2.1, p. 12). -/
def devUtil (U : ι → ((j : ι) → B j) → ℝ) (j : ι) (μ : ((j : ι) → B j) → ℝ) (D : B j → ℝ) : ℝ :=
  ∑ b, μ b * ∑ a, D a * U j (Function.update b j a)

/-- `μ` is an `ε`-approximate coarse correlated equilibrium (Definition 2.1, pp. 12–13): `μ` is a
law of action profiles, `ε ≥ 0`, and, for every player `j`, `CCEGap_j(μ) = max_{D_j ∈ Δ(B_j)} U_j(D_j, μ_{-j})
− U_j(μ) ≤ ε`, written as: every mixed deviation `D_j` gains at most `ε`. -/
def IsEpsCCE (U : ι → ((j : ι) → B j) → ℝ) (μ : ((j : ι) → B j) → ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ IsDist μ ∧ ∀ j (D : B j → ℝ), IsDist D → devUtil U j μ D - expUtil U j μ ≤ ε

/-- The law `∑_t w_t ⊗_j p^{(t)}_j` of a mixture of `T` product distributions (eq. (1), p. 13). -/
def mixture {T : ℕ} (w : Fin T → ℝ) (p : Fin T → (j : ι) → B j → ℝ) :
    ((j : ι) → B j) → ℝ :=
  fun b => ∑ t, w t * ∏ j, p t j (b j)

/-- `μ` is `T`-sparse (Definition 2.2, p. 13): a mixture of `T` product distributions,
`μ = ∑_{t=1}^T w_t ⊗_j p^{(t)}_j` with `w ∈ Δ([T])` and `p^{(t)}_j ∈ Δ(B_j)`; weights may be zero. -/
def IsTSparse (T : ℕ) (μ : ((j : ι) → B j) → ℝ) : Prop :=
  ∃ (w : Fin T → ℝ) (p : Fin T → (j : ι) → B j → ℝ),
    IsDist w ∧ (∀ t j, IsDist (p t j)) ∧ μ = mixture w p

/-- `μ_{ik}`: the joint law of `(b_i, b_k)` under `μ`, viewed as a matrix with rows indexed by
`B_i` and columns by `B_k` (§2.2, p. 12). -/
def pairMarginal (μ : ((j : ι) → B j) → ℝ) (i k : ι) : Matrix (B i) (B k) ℝ :=
  fun a c => ∑ b, if b i = a ∧ b k = c then μ b else 0

end SparseCCE.ThreePlayer


