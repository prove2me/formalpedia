-- Prove2me | Definitions.Def_WassTwoStage_Copositive_Setting
-- name    : WassTwoStage_Copositive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:28.131255+00:00
-- url     : https://prove2.me/theorems/7669a821-da27-46df-b0cc-358f4dca3be3
-- title:
--   Two-stage DRO data, recourse value $Z(x,\xi)$, worst-case expectation $\mathcal Z(x)$ over the 2-Wasserstein ball, and the extended data (11)
-- statement:
--   Fix dimensions $K, J, M, N_1, N_2, I \in \mathbb N$. The data of the two-stage distributionally robust linear program are:
--
--   1. $Q \in \mathbb R^{N_2 \times K}$ and $q \in \mathbb R^{N_2}$, giving the uncertain second-stage cost vector $Q\xi + q$;
--   2. matrix- and vector-valued **affine** functions $T : \mathbb R^{N_1} \to \mathbb R^{M\times K}$ and $h : \mathbb R^{N_1} \to \mathbb R^M$ of the first-stage decision $x$, and a recourse matrix $W \in \mathbb R^{M \times N_2}$;
--   3. $S \in \mathbb R^{J\times K}$ and $t \in \mathbb R^J$, describing the support set
--   $$\Xi = \{\xi \in \mathbb R^K_+ : S\xi \le t\} \qquad (8);$$
--   4. samples $\hat\xi_1, \dots, \hat\xi_I \in \mathbb R^K$ and a radius $\epsilon$.
--
--   The **recourse function** (3) is the optimal value of a linear program,
--   $$Z(x,\xi) = \inf\{(Q\xi + q)^\top y : y \in \mathbb R^{N_2},\ T(x)\xi + h(x) \le Wy\} \in [-\infty, +\infty],$$
--   equal to $+\infty$ if the program is infeasible and $-\infty$ if it is unbounded. The problem has **complete recourse** (Definition 1) if some $y^+$ satisfies $Wy^+ > 0$ componentwise, and **sufficiently expensive recourse** (Definition 2) if for every $\xi \in \Xi$ the dual recourse problem (4) is feasible, i.e. there is $p \in \mathbb R^M_+$ with $Q\xi + q = W^\top p$.
--
--   The **worst-case expectation** (2) is
--   $$\mathcal Z(x) = \sup_{\mathbb P \in \mathcal B^2_\epsilon(\hat{\mathbb P}_I)} \mathbb E_{\mathbb P}[Z(x,\tilde\xi)],$$
--   where $\hat{\mathbb P}_I = \frac1I\sum_{i\in[I]}\delta_{\hat\xi_i}$ is the empirical distribution and $\mathcal B^2_\epsilon(\hat{\mathbb P}_I)$ is the set of probability distributions supported on $\Xi$ whose 2-Wasserstein distance to $\hat{\mathbb P}_I$, with Euclidean transport cost $\|\xi_1 - \xi_2\|_2$, is at most $\epsilon$.
--
--   Finally, the **extended recourse data** (11) are
--   $$\mathcal Q = \begin{bmatrix} Q \\ S\end{bmatrix},\quad \boldsymbol q = \begin{bmatrix} q \\ -t\end{bmatrix},\quad \mathcal T(x) = \begin{bmatrix} T(x) \\ 0\end{bmatrix},\quad \boldsymbol h(x) = \begin{bmatrix} h(x)\\ 0\end{bmatrix},\quad \mathcal W = \begin{bmatrix} W & 0\\ 0 & -\mathbb I\end{bmatrix},$$
--   of sizes $(N_2+J)\times K$, $N_2+J$, $(M+J)\times K$, $M+J$ and $(M+J)\times(N_2+J)$; they merge the recourse data with the support constraints.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Uncertain parameters live in `EuclideanSpace ℝ (Fin K)` with its Borel $\sigma$-algebra, and matrices act on the coordinate vector. All values are extended reals (`EReal`). The expectation of the extended-real recourse value is the reused platform convention: $+\infty$ when the positive part has infinite integral, otherwise $\int Z^+ - \int Z^-$. The ball is the reused platform ambiguity set with $p = 2$ (probability measures $\mathbb P$ with $\mathbb P(\Xi^c) = 0$ and $W_2(\mathbb P, \hat{\mathbb P}_I) \le \epsilon$); the finite-second-moment requirement of $\mathcal M^2(\Xi)$ in Definition 3 follows from $W_2(\mathbb P, \hat{\mathbb P}_I) < \infty$ because $\hat{\mathbb P}_I$ has finite support. Stacked blocks are indexed by sum types (`Fin N₂ ⊕ Fin J`, `Fin M ⊕ Fin J`), with the original rows first. In the paper $\boldsymbol q$ and $\boldsymbol h$ are script letters.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, pp. 5–8, (1)–(4), Definitions 1–3, (8), (11)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory Matrix

namespace WassTwoStage.Copositive

/-- The data of the two-stage distributionally robust linear program (1)–(3) of Hanasusanto–Kuhn,
*Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over
Wasserstein Balls*, arXiv:1609.07505v3, pp. 5–7, under the standing setting of §3 (p. 7).

* `Q ∈ ℝ^{N₂×K}`, `q ∈ ℝ^{N₂}`: the uncertain second-stage cost `(Qξ + q)ᵀ y` of (3);
* `T(x) ∈ ℝ^{M×K}`, `h(x) ∈ ℝ^M`: matrix- and vector-valued **affine** functions of the
  first-stage decision `x ∈ ℝ^{N₁}` (p. 6), and `W ∈ ℝ^{M×N₂}` the recourse matrix;
* `S ∈ ℝ^{J×K}`, `t ∈ ℝ^J`: the support `Ξ = {ξ ∈ ℝ^K_+ : Sξ ≤ t}` of (8);
* `ξhat i ∈ ℝ^K`, `i ∈ [I]`: the samples defining the empirical distribution `ℙ̂_I`;
* `ε`: the radius of the Wasserstein ball.

Uncertain parameters live in `EuclideanSpace ℝ (Fin K)` (with its Borel σ-algebra and the
2-norm); matrices act on the underlying coordinate vector `WithLp.ofLp ξ : Fin K → ℝ`. -/
structure Data (K J M N₁ N₂ I : ℕ) where
  Q : Matrix (Fin N₂) (Fin K) ℝ
  q : Fin N₂ → ℝ
  T : (Fin N₁ → ℝ) →ᵃ[ℝ] Matrix (Fin M) (Fin K) ℝ
  h : (Fin N₁ → ℝ) →ᵃ[ℝ] (Fin M → ℝ)
  W : Matrix (Fin M) (Fin N₂) ℝ
  S : Matrix (Fin J) (Fin K) ℝ
  t : Fin J → ℝ
  ξhat : Fin I → EuclideanSpace ℝ (Fin K)
  ε : ℝ

variable {K J M N₁ N₂ I : ℕ}

/-- The support set (8), p. 7: `Ξ = {ξ ∈ ℝ^K_+ : Sξ ≤ t}`. -/
def Data.Xi (d : Data K J M N₁ N₂ I) : Set (EuclideanSpace ℝ (Fin K)) :=
  {ξ | 0 ≤ WithLp.ofLp ξ ∧ d.S *ᵥ WithLp.ofLp ξ ≤ d.t}

/-- The recourse function (3), p. 5:
`Z(x, ξ) = inf {(Qξ + q)ᵀ y : y ∈ ℝ^{N₂}, T(x)ξ + h(x) ≤ Wy}`,
an extended real number: `+∞` when the recourse problem is infeasible and `−∞` when it is
unbounded below. -/
noncomputable def Data.recourse (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ)
    (ξ : EuclideanSpace ℝ (Fin K)) : EReal :=
  ⨅ (y : Fin N₂ → ℝ) (_ : d.T x *ᵥ WithLp.ofLp ξ + d.h x ≤ d.W *ᵥ y),
    (((d.Q *ᵥ WithLp.ofLp ξ + d.q) ⬝ᵥ y : ℝ) : EReal)

/-- Definition 1 (complete recourse), p. 6: there is `y⁺ ∈ ℝ^{N₂}` with `Wy⁺ > 0`
componentwise. -/
def Data.CompleteRecourse (d : Data K J M N₁ N₂ I) : Prop :=
  ∃ y : Fin N₂ → ℝ, ∀ m, 0 < (d.W *ᵥ y) m

/-- Definition 2 (sufficiently expensive recourse), p. 6: for every `ξ ∈ Ξ` the dual recourse
problem (4), `sup {(T(x)ξ + h(x))ᵀ p : p ∈ ℝ^M_+, Qξ + q = Wᵀp}`, is feasible. -/
def Data.SufficientlyExpensiveRecourse (d : Data K J M N₁ N₂ I) : Prop :=
  ∀ ξ ∈ d.Xi, ∃ p : Fin M → ℝ, 0 ≤ p ∧ d.Q *ᵥ WithLp.ofLp ξ + d.q = d.Wᵀ *ᵥ p

/-- The worst-case expectation (2), p. 5, over the 2-Wasserstein ball of Definition 3 (p. 6)
with the Euclidean reference distance of §3 (p. 7):
`𝒵(x) = sup_{ℙ ∈ B²_ε(ℙ̂_I)} E_ℙ[Z(x, ξ̃)]`, where `ℙ̂_I = (1/I) Σ_i δ_{ξ̂_i}` and the ball
consists of the probability measures supported on `Ξ` whose 2-Wasserstein distance to `ℙ̂_I` is
at most `ε`. The expectation of the extended-real recourse value is `+∞` whenever its positive
part has infinite integral. -/
noncomputable def Data.worstCase (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨆ (P : Measure (EuclideanSpace ℝ (Fin K)))
    (_ : P ∈ WassersteinDRO.Duality.ambiguitySet d.ε 2 d.Xi
      (WassersteinDRO.Duality.empiricalDistribution d.ξhat)),
    WassersteinDRO.Duality.erealExpectation P (fun ξ => d.recourse x ξ)

/-- Extended recourse data (11), p. 8: `𝒬 = [Q; S] ∈ ℝ^{(N₂+J)×K}`. -/
def Data.bQ (d : Data K J M N₁ N₂ I) : Matrix (Fin N₂ ⊕ Fin J) (Fin K) ℝ :=
  Matrix.fromRows d.Q d.S

/-- Extended recourse data (11), p. 8: `𝓆 = [q; −t] ∈ ℝ^{N₂+J}`. -/
def Data.bq (d : Data K J M N₁ N₂ I) : Fin N₂ ⊕ Fin J → ℝ :=
  Sum.elim d.q (-d.t)

/-- Extended recourse data (11), p. 8: `𝒯(x) = [T(x); 0] ∈ ℝ^{(M+J)×K}`. -/
def Data.bT (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) : Matrix (Fin M ⊕ Fin J) (Fin K) ℝ :=
  Matrix.fromRows (d.T x) 0

/-- Extended recourse data (11), p. 8: `𝒽(x) = [h(x); 0] ∈ ℝ^{M+J}`. -/
def Data.bh (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) : Fin M ⊕ Fin J → ℝ :=
  Sum.elim (d.h x) 0

/-- Extended recourse data (11), p. 8: `𝒲 = [[W, 0], [0, −𝕀]] ∈ ℝ^{(M+J)×(N₂+J)}`. -/
def Data.bW (d : Data K J M N₁ N₂ I) : Matrix (Fin M ⊕ Fin J) (Fin N₂ ⊕ Fin J) ℝ :=
  Matrix.fromBlocks d.W 0 0 (-1)

end WassTwoStage.Copositive


