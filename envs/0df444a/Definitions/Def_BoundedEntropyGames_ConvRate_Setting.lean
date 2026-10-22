-- Prove2me | Definitions.Def_BoundedEntropyGames_ConvRate_Setting
-- name    : BoundedEntropyGames_ConvRate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:51.593354+00:00
-- url     : https://prove2.me/theorems/84f140a5-0f87-4ff7-8253-53fd43f39887
-- title:
--   §2–§3.1, pp. 8–14 — pmfs, TV, Shannon and Rényi entropies, the n-stage game with leaked randomness source, payoff (7), U (8), J (9), J_cav
-- statement:
--   All alphabets $\mathcal A,\mathcal B,\mathcal X,\mathcal Y$ are finite sets. A **pmf** on a finite set $T$ is a function $p:T\to\mathbb R$ with $p(t)\ge 0$ and $\sum_t p(t)=1$. For a joint pmf $p_{XY}$ on $\mathcal X\times\mathcal Y$ the marginals are $p_X(x)=\sum_y p_{XY}(x,y)$ and $p_Y(y)=\sum_x p_{XY}(x,y)$. All logarithms are in base two, with $0\log 0=0$.
--
--   1. **Total variation distance:** $\|p-q\|_{TV}=\tfrac12\sum_t|p(t)-q(t)|$.
--   2. **Shannon entropy and conditional entropy:** $H(p)=\sum_t -p(t)\log p(t)$ and $H(X|Y)=\sum_{(x,y)}-p_{XY}(x,y)\log p_{X|Y}(x|y)$, where $p_{X|Y}(x|y)=p_{XY}(x,y)/p_Y(y)$.
--   3. **Rényi entropy** of order $\alpha>0$, $\alpha\ne1$: $H_\alpha(p)=\frac{\alpha}{1-\alpha}\log\big(\sum_t p(t)^\alpha\big)^{1/\alpha}$, and the **conditional Rényi entropy** $H_\alpha(X|Y)=\frac{\alpha}{1-\alpha}\log\big(\sum_y p_Y(y)\|p_{X|Y=y}\|_\alpha\big)$ with $\|q\|_\alpha=(\sum_x q(x)^\alpha)^{1/\alpha}$.
--   4. **The repeated game with leaked randomness source** (§3.1). At each stage $t=1,\dots,n$ a pair $(X_t,Y_t)$ is drawn from $p_{XY}$, independently of the past; Alice observes $X_t$ and Bob observes $Y_t$. Alice's strategy $\sigma^n=(\sigma_1,\dots,\sigma_n)$ consists of deterministic maps $\sigma_t:(\mathcal A\times\mathcal B)^{t-1}\times\mathcal X^t\to\mathcal A$, and Bob's strategy $\tau^n$ of deterministic maps $\tau_t:(\mathcal A\times\mathcal B)^{t-1}\times\mathcal Y^t\to\mathcal B$. The actions are $A_t=\sigma_t(A_1,B_1,\dots,A_{t-1},B_{t-1},X_1,\dots,X_t)$ and $B_t=\tau_t(A_1,B_1,\dots,A_{t-1},B_{t-1},Y_1,\dots,Y_t)$, and Alice's expected average payoff is
--   $$
--   \lambda(\sigma^n,\tau^n)=\sum_{x^n,y^n}\prod_{t=1}^n p_{XY}(x_t,y_t)\cdot\frac1n\sum_{t=1}^n u_{A_tB_t}.
--   $$
--   5. **Security level and entropy-constrained value** (Definition 4): $U^{(A)}(p_A)=\min_{b\in\mathcal B}\sum_a p_A(a)u_{ab}$ and $J^{(A)}(h)=\max\{U^{(A)}(p_A):p_A\in\Delta(\mathcal A),\ H(p_A)\le h\}$ for $h\ge0$.
--   6. **Upper concave envelope:** $J^{(A)}_{cav}(h)$ is the infimum of $g(h)$ over all functions $g$ that are concave on $[0,\infty)$ and satisfy $g\ge J^{(A)}$ on $[0,\infty)$.
--   7. $M=\max_{a,b}|u_{ab}|$.
--
--   These are the objects of Theorem 6 and of every milestone of the mission.
--
--   **Formalization Note** Stages are indexed $0,\dots,n-1$ (`Fin n`); stage $t$ of the paper is index $t-1$. The play is built by recursion on the number of stages played, so Alice's action at a stage reads only the past action pairs and her own sources up to that stage, and Bob's likewise. The payoff is a finite sum over $(x^n,y^n)$ weighted by the i.i.d. product of $p_{XY}$. $J^{(A)}$ is written as a supremum (`sSup`) of the security levels over the entropy-constrained simplex; for $h\ge0$ the set is nonempty (point masses) and bounded, so the supremum is the paper's maximum, attained. For $h<0$ the value is a junk value and is never used: $J^{(A)}_{cav}$ quantifies over $h\ge0$ only. The Rényi formulas give junk values at $\alpha=1$ (Lean's $x/0=0$); every statement that uses them either excludes $\alpha=1$ or multiplies them by $1-1/\alpha=0$.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, pp. 8–14, §2.1–§2.3, §3.1, (7), Definition 4 (8)–(9), Theorem 5 (J_cav), p. 24 (M)

import Mathlib

namespace BoundedEntropyGames.ConvRate

/-! Valizadeh–Gohari, *Playing Games with Bounded Entropy: Convergence Rate and Approximate
Equilibria*, arXiv:1902.03676v1, §2 (pp. 8–11) and §3.1 (pp. 12–14).

Conventions: alphabets are finite types; a pmf is a nonnegative real function summing to 1;
all logarithms are in base 2 (`Real.logb 2`, with `Real.logb 2 0 = 0`, i.e. `0 log 0 = 0`);
stages `t = 1, …, n` of the repeated game are indexed by `Fin n` (stage `t` is index `t - 1`). -/

/-- A probability mass function on a finite type. -/
def IsPMF {T : Type*} [Fintype T] (p : T → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ ∑ t, p t = 1

/-- The marginal `p_X` of a joint pmf `p_XY`. -/
def marginalX {𝒳 𝒴 : Type*} [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ) (x : 𝒳) : ℝ :=
  ∑ y, pXY (x, y)

/-- The marginal `p_Y` of a joint pmf `p_XY`. -/
def marginalY {𝒳 𝒴 : Type*} [Fintype 𝒳] (pXY : 𝒳 × 𝒴 → ℝ) (y : 𝒴) : ℝ :=
  ∑ x, pXY (x, y)

/-- Total variation distance `‖p - q‖_TV = ½ ∑ |p(x) - q(x)|` (p. 9). -/
noncomputable def tv {T : Type*} [Fintype T] (p q : T → ℝ) : ℝ :=
  (1 / 2) * ∑ t, |p t - q t|

/-- Shannon entropy in bits, `H(p) = ∑ -p(x) log p(x)` (p. 9). -/
noncomputable def shannon {T : Type*} [Fintype T] (p : T → ℝ) : ℝ :=
  ∑ t, -(p t) * Real.logb 2 (p t)

/-- Conditional Shannon entropy `H(X|Y) = ∑_{(x,y)} -p_XY(x,y) log p_{X|Y}(x|y)` (p. 9). -/
noncomputable def condEntropy {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ) : ℝ :=
  ∑ xy : 𝒳 × 𝒴, -(pXY xy) * Real.logb 2 (pXY xy / marginalY pXY xy.2)

/-- Rényi entropy of order `α`, `H_α(p) = α/(1-α) · log (∑ p(x)^α)^{1/α}` (p. 10).
Meaningful for `α > 0`, `α ≠ 1`. -/
noncomputable def renyi {T : Type*} [Fintype T] (α : ℝ) (p : T → ℝ) : ℝ :=
  α / (1 - α) * Real.logb 2 ((∑ t, p t ^ α) ^ (1 / α))

/-- Conditional Rényi entropy `H_α(X|Y) = α/(1-α) · log ∑_y p_Y(y) ‖p_{X|Y=y}‖_α` (p. 10).
Meaningful for `α > 0`, `α ≠ 1`. -/
noncomputable def condRenyi {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (α : ℝ)
    (pXY : 𝒳 × 𝒴 → ℝ) : ℝ :=
  α / (1 - α) * Real.logb 2
    (∑ y, marginalY pXY y * (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α))

/-- Alice's deterministic `n`-stage strategy (§3.1, p. 12): at stage `t` (0-based index), a map
`σ_t : (𝒜 × ℬ)^{t-1} × 𝒳^t → 𝒜` from the past action pairs and her sources `x_1, …, x_t`. -/
def AliceStrategy (𝒜 ℬ 𝒳 : Type*) (n : ℕ) : Type _ :=
  (t : Fin n) → (Fin t → 𝒜 × ℬ) → (Fin (t + 1) → 𝒳) → 𝒜

/-- Bob's deterministic `n`-stage strategy (§3.1, p. 12): at stage `t`, a map
`τ_t : (𝒜 × ℬ)^{t-1} × 𝒴^t → ℬ` from the past action pairs and his sources `y_1, …, y_t`. -/
def BobStrategy (𝒜 ℬ 𝒴 : Type*) (n : ℕ) : Type _ :=
  (t : Fin n) → (Fin t → 𝒜 × ℬ) → (Fin (t + 1) → 𝒴) → ℬ

/-- The action pairs of the first `k` stages when `σ` and `τ` are played on the source
sequences `xs`, `ys`. Stage `k` feeds Alice the past pairs and `xs 0, …, xs k`, and Bob the past
pairs and `ys 0, …, ys k`. -/
def history {𝒜 ℬ 𝒳 𝒴 : Type*} {n : ℕ} (σ : AliceStrategy 𝒜 ℬ 𝒳 n) (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (xs : Fin n → 𝒳) (ys : Fin n → 𝒴) : (k : ℕ) → k ≤ n → (Fin k → 𝒜 × ℬ)
  | 0, _ => Fin.elim0
  | k + 1, hk =>
    Fin.snoc (α := fun _ => 𝒜 × ℬ) (history σ τ xs ys k (Nat.le_of_succ_le hk))
      (σ ⟨k, hk⟩ (history σ τ xs ys k (Nat.le_of_succ_le hk))
          (fun j => xs ⟨j.1, lt_of_lt_of_le j.2 hk⟩),
        τ ⟨k, hk⟩ (history σ τ xs ys k (Nat.le_of_succ_le hk))
          (fun j => ys ⟨j.1, lt_of_lt_of_le j.2 hk⟩))

/-- The action pair `(A_t, B_t)` played at stage `t`. -/
def play {𝒜 ℬ 𝒳 𝒴 : Type*} {n : ℕ} (σ : AliceStrategy 𝒜 ℬ 𝒳 n) (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (xs : Fin n → 𝒳) (ys : Fin n → 𝒴) (t : Fin n) : 𝒜 × ℬ :=
  history σ τ xs ys (t + 1) t.2 (Fin.last t)

/-- The expected average payoff `λ(σ^n, τ^n) = E[(1/n) ∑_t u_{A_t B_t}]` (7), the expectation
over `n` i.i.d. draws `(X_t, Y_t)` from `p_XY`. -/
noncomputable def payoff {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] {n : ℕ}
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (σ : AliceStrategy 𝒜 ℬ 𝒳 n)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n) : ℝ :=
  ∑ xs : Fin n → 𝒳, ∑ ys : Fin n → 𝒴,
    (∏ t, pXY (xs t, ys t)) *
      ((1 / (n : ℝ)) * ∑ t, u (play σ τ xs ys t).1 (play σ τ xs ys t).2)

/-- Security level `U^(A)(p_A) = min_b ∑_a p_A(a) u_{ab}` (8). -/
noncomputable def U {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (p : 𝒜 → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun b => ∑ a, p a * u a b)

/-- `J^(A)(h) = max {U^(A)(p_A) : p_A ∈ Δ(𝒜), H(p_A) ≤ h}` (9). Used for `h ≥ 0`. -/
noncomputable def J {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (h : ℝ) : ℝ :=
  sSup ((U u) '' {p | p ∈ stdSimplex ℝ 𝒜 ∧ shannon p ≤ h})

/-- `J^(A)_cav`, the upper concave envelope of `J^(A)` on `[0, ∞)` (Theorem 5, p. 14): the
pointwise least concave function on `[0, ∞)` majorizing `J^(A)` there. -/
noncomputable def Jcav {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (h : ℝ) : ℝ :=
  sInf {c | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Set.Ici 0) g ∧ (∀ h' ≥ 0, J u h' ≤ g h') ∧ c = g h}

/-- `M = max_{a,b} |u_{ab}|` (p. 24). -/
noncomputable def maxAbsPayoff {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty 𝒜] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ab : 𝒜 × ℬ => |u ab.1 ab.2|)

end BoundedEntropyGames.ConvRate


