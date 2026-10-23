-- Prove2me | Definitions.Def_SwitchCostGames_Stationary_Model
-- name    : SwitchCostGames_Stationary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:31.131982+00:00
-- url     : https://prove2.me/theorems/6a7bfede-4351-4548-8724-12c11a9e8748
-- title:
--   §2 and §3.1, pp. 2–3 — repeated zero-sum game with switching costs: histories, behavior and stationary strategies, liminf payoff, value; the parametric one-shot game Γ(x)
-- statement:
--   This file sets up the model of Tsodikovich, Venel and Zseleva, §2, together with the parametric one-shot game of §3.1.
--
--   **The game.** A *zero-sum game with switching costs* is a triple $\Gamma = (A, S, c)$, where $A = (a_{ij})$ is a real $m \times n$ matrix with $m, n \ge 1$, $S = (s_{kj})$ is a real $n \times n$ matrix with nonnegative entries and zero diagonal ($s_{jj} = 0$: keeping the same column is costless), and $c \ge 0$ is the switching-cost weight. At every stage $t = 1, 2, \dots$ player 1 (the maximizer) chooses a row $i(t)$ and player 2 (the minimizer) chooses a column $j(t)$; player 2 pays player 1 the stage payoff
--   $$
--   a_{i(t)j(t)} + c\, s_{j(t-1)j(t)},
--   $$
--   with the convention $j(0) = 1$ (the first column).
--
--   **Strategies.** A *history* of length $t$ is the sequence of action pairs of the first $t$ stages. A *behavior strategy* of player 1 assigns to every finite history a mixed action, i.e. a probability vector on the rows; a behavior strategy of player 2 assigns a probability vector on the columns. In particular both players observe $j(t-1)$ before stage $t$. Under a pair $(\sigma,\tau)$ a history $h$ of length $T$ has probability
--   $$
--   \mathbb P_{\sigma,\tau}(h) = \prod_{t=1}^{T} \sigma(h_{<t})(i(t))\,\tau(h_{<t})(j(t)),
--   $$
--   where $h_{<t}$ is the history of the first $t-1$ stages.
--
--   **Payoff.** The payoff of $(\sigma,\tau)$ is the lower limit of the expected average stage payoff,
--   $$
--   \gamma_c(\sigma,\tau) = \liminf_{T\to\infty} \mathbb E_{\sigma,\tau}\Big(\frac1T\sum_{t=1}^{T} a_{i(t)j(t)} + c\, s_{j(t-1)j(t)}\Big).
--   $$
--
--   **Stationary strategies (Definition 1).** A strategy is *stationary* if its mixed action after any history depends only on the previous column $j(t-1)$, so it is a vector of $n$ mixed actions. A *pure stationary* strategy of player 1 is a map $f : [n] \to [m]$ (play row $f(k)$ after column $k$); of player 2 a map $g : [n] \to [n]$.
--
--   **Value in stationary strategies.** The game has *value* $v$ in stationary strategies if there are stationary strategies $\sigma^*$ of player 1 and $\tau^*$ of player 2 with $\gamma_c(\sigma^*,\tau') \ge v$ for every behavior strategy $\tau'$ of player 2 and $\gamma_c(\sigma',\tau^*) \le v$ for every behavior strategy $\sigma'$ of player 1. Such a $v$ is unique.
--
--   **One-shot games.** A finite zero-sum one-shot game with payoff $M(i,j)$ to the row player has *value* $v$ if it has a mixed saddle point $(p,q)$ (a Nash equilibrium of the zero-sum game) with $\sum_{i,j} p_i q_j M(i,j) = v$; by von Neumann's minimax theorem every game with nonempty finite strategy sets has one. Given an $m\times n$ matrix $A$, nonnegative constants $b_1,\dots,b_n$ and $x = (x_1,\dots,x_n)$, the game $\Gamma(x)$ of §3.1 has payoff matrix $a_{ij} + b_j x_j$.
--
--   **Piecewise linear functions.** A function $f:\mathbb R\to\mathbb R$ is piecewise linear on a set $s$ if there is a finite set $B$ of breakpoints such that $f$ is affine on every closed interval contained in $s$ whose interior contains no point of $B$.
--
--   These objects carry every statement of the mission: Lemma 1, the existence of the value in stationary strategies, the Filar–Raghavan reduction, and Theorem 1.
--
--   **Formalization Note** Rows are `Fin m`, columns `Fin n`; the paper's $j(0) = 1$ is column `0`. Stages are numbered from $0$ in Lean: stage `s : Fin T` is the paper's $t = s+1$, and its switching cost uses the previous column of the history of the first `s` stages. There is no measure theory: all action sets are finite, so the expectation over the first $T$ stages is a finite sum over the histories `Fin T → Fin m × Fin n`. Mixed actions and the one-shot value use the published finite zero-sum game `BlottoLP.Flow.ZeroSum` (`IsMixed`, `pureMixed`, `IsNashEq`, `expPay`), instantiated on arbitrary finite index types so that the one-shot game on pure stationary strategies is covered. The `liminf` is a genuine lower limit and not a junk value: since the history probabilities sum to $1$, $|\mathbb E(\cdot)/T| \le \max|a_{ij}| + |c|\max s_{kj}$, so the sequence is bounded. Optimality in the value is against all behavior strategies, not only stationary ones. The weight $c$ is a separate argument, not a field of the game.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, pp. 2–3 (PDF 4–5), §2, Definition 1, §3.1

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum

namespace SwitchCostGames.Stationary

open Finset

/-- A zero-sum game with switching costs (§2, p. 2): an `m × n` payoff matrix `A` and an `n × n`
switching-cost matrix `S` with nonnegative entries and zero diagonal (`s_jj = 0`: keeping the same
column is costless). The weight `c ≥ 0` is a separate argument everywhere. -/
structure Game (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  S : Matrix (Fin n) (Fin n) ℝ
  S_nonneg : ∀ k j, 0 ≤ S k j
  S_diag : ∀ j, S j j = 0

/-- A history after `t` stages: the action pairs `(i, j)` of stages `0, …, t − 1` (the paper's
stages `1, …, t`). -/
abbrev History (m n t : ℕ) := Fin t → Fin m × Fin n

/-- The first `s` stages of a history of length `t ≥ s`. -/
def History.take {m n t : ℕ} (h : History m n t) (s : ℕ) (hs : s ≤ t) : History m n s :=
  fun r => h (Fin.castLE hs r)

/-- A behavior strategy of player 1 (rows, the maximizer): a mixed action on `Fin m` after every
finite history. -/
structure Strategy1 (m n : ℕ) where
  act : (t : ℕ) → History m n t → Fin m → ℝ
  act_mem : ∀ t h, BlottoLP.Flow.IsMixed (act t h)

/-- A behavior strategy of player 2 (columns, the minimizer): a mixed action on `Fin n` after
every finite history. -/
structure Strategy2 (m n : ℕ) where
  act : (t : ℕ) → History m n t → Fin n → ℝ
  act_mem : ∀ t h, BlottoLP.Flow.IsMixed (act t h)

/-- The previous column `j(t−1)` after a history of length `t`; the paper's `j(0) = 1` is the
first column `0`. -/
def prevAction {m n : ℕ} [NeZero n] : {t : ℕ} → History m n t → Fin n
  | 0, _ => 0
  | t + 1, h => (h (Fin.last t)).2

/-- The probability of a history of length `T` under `(σ, τ)`: at each stage `s` both players mix
independently, according to their mixed actions after the history of the first `s` stages. -/
def histProb {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) {T : ℕ} (h : History m n T) : ℝ :=
  ∏ s : Fin T, σ.act s (h.take s s.isLt.le) (h s).1 * τ.act s (h.take s s.isLt.le) (h s).2

/-- `E_{σ,τ} Σ_{t=1}^{T} (a_{i(t)j(t)} + c s_{j(t−1)j(t)})`, a finite sum over the histories of
length `T`. Stage `s : Fin T` is the paper's `t = s + 1`. -/
def expectedTotal {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (T : ℕ) : ℝ :=
  ∑ h : History m n T, histProb σ τ h *
    ∑ s : Fin T, (G.A (h s).1 (h s).2 + c * G.S (prevAction (h.take s s.isLt.le)) (h s).2)

/-- The payoff `γ(σ, τ) = liminf_{T→∞} E_{σ,τ}((1/T) Σ_{t=1}^{T} a_{i(t)j(t)} + c s_{j(t−1)j(t)})`
that player 2 pays player 1. -/
noncomputable def payoff {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) : ℝ :=
  Filter.liminf (fun T : ℕ => expectedTotal G c σ τ T / T) Filter.atTop

/-- Definition 1 for player 1: the mixed action after a history depends only on the previous
column `j(t−1)`, i.e. the strategy is a vector of `n` mixed actions. -/
def IsStationary1 {m n : ℕ} [NeZero n] (σ : Strategy1 m n) : Prop :=
  ∃ x : Fin n → Fin m → ℝ, ∀ t (h : History m n t), σ.act t h = x (prevAction h)

/-- Definition 1 for player 2: the mixed action after a history depends only on the previous
column `j(t−1)`. -/
def IsStationary2 {m n : ℕ} [NeZero n] (τ : Strategy2 m n) : Prop :=
  ∃ y : Fin n → Fin n → ℝ, ∀ t (h : History m n t), τ.act t h = y (prevAction h)

/-- `σ` is the pure stationary strategy `f`: after previous column `k` it plays row `f k`. -/
def IsPureStationary1 {m n : ℕ} [NeZero n] (σ : Strategy1 m n) (f : Fin n → Fin m) : Prop :=
  ∀ t (h : History m n t), σ.act t h = BlottoLP.Flow.pureMixed (f (prevAction h))

/-- `τ` is the pure stationary strategy `g`: after previous column `k` it plays column `g k`. -/
def IsPureStationary2 {m n : ℕ} [NeZero n] (τ : Strategy2 m n) (g : Fin n → Fin n) : Prop :=
  ∀ t (h : History m n t), τ.act t h = BlottoLP.Flow.pureMixed (g (prevAction h))

/-- The game `(A, S, c)` has the value `v` in stationary strategies: there are stationary
strategies `σ, τ` such that `σ` guarantees player 1 at least `v` against every behavior strategy
of player 2, and `τ` holds player 1 to at most `v` against every behavior strategy of player 1. -/
def IsValue {m n : ℕ} [NeZero n] (G : Game m n) (c v : ℝ) : Prop :=
  ∃ σ : Strategy1 m n, ∃ τ : Strategy2 m n, IsStationary1 σ ∧ IsStationary2 τ ∧
    (∀ τ' : Strategy2 m n, v ≤ payoff G c σ τ') ∧ (∀ σ' : Strategy1 m n, payoff G c σ' τ ≤ v)

/-- The one-shot zero-sum game with payoff `M i j` to the row player (the maximizer) has the value
`v`: it has a mixed saddle point (Nash equilibrium) whose expected payoff is `v`. -/
def IsSaddleValue {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ) (v : ℝ) : Prop :=
  ∃ p : ι → ℝ, ∃ q : κ → ℝ, BlottoLP.Flow.IsNashEq M p q ∧ BlottoLP.Flow.expPay M p q = v

/-- The parametric one-shot game `Γ(x)` of §3.1: payoff `a_ij + b_j x_j`. -/
def paramGame {ι κ : Type*} (A : ι → κ → ℝ) (b x : κ → ℝ) : ι → κ → ℝ :=
  fun i j => A i j + b j * x j

/-- `f` is piecewise linear (affine) on `s` with finitely many pieces: there is a finite set `B`
of breakpoints such that `f` is affine on every closed interval contained in `s` whose interior
contains no breakpoint. -/
def IsPiecewiseAffineOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ B : Finset ℝ, ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ s → (∀ x ∈ B, x ∉ Set.Ioo a b) →
    ∃ α β : ℝ, ∀ x ∈ Set.Icc a b, f x = α + β * x

end SwitchCostGames.Stationary


