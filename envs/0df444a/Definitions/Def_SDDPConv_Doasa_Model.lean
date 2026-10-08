-- Prove2me | Definitions.Def_SDDPConv_Doasa_Model
-- name    : SDDPConv_Doasa_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:49:34.469981+00:00
-- url     : https://prove2.me/theorems/7ce300f5-3f41-42d9-aa12-6a290734893d
-- title:
--   (A1)–(A4), [LP1]/[LPt] and the value functions 𝒬_t — stagewise multistage stochastic LP (§2, pp. 2–3)
-- statement:
--   This file fixes the multistage stochastic linear program of Philpott and Guan (§2, pp. 2–3).
--
--   There are $T\ge 2$ stages, numbered $1,\dots,T$. Stage $t$ has a decision vector $x_t\in\mathbb R^{n_t}$, a cost vector $c_t$, a constraint matrix $A_t\in\mathbb R^{m_t\times n_t}$ and, for $t\le T-1$, a matrix $B_t\in\mathbb R^{m_{t+1}\times n_t}$ coupling $x_t$ to the next stage. Stage $1$ has the deterministic right-hand side $b_1$. For $2\le t\le T$ the random right-hand side $\omega_t$ takes the values $\omega_{t1},\dots,\omega_{tq_t}$ with probabilities $p_{ti}>0$, $\sum_i p_{ti}=1$ (assumption (A2)). The outcome law of each stage is fixed and independent of earlier stages (A3), and only right-hand sides are random (A1).
--
--   The **expected cost-to-go** functions are defined backwards from $\mathcal Q_{T+1}\equiv 0$:
--
--   $$Q_t(x_{t-1},\omega_{ti})=\min\{c_t^\top x_t+\mathcal Q_{t+1}(x_t)\;:\;A_tx_t=\omega_{ti}-B_{t-1}x_{t-1},\ x_t\ge 0\},\qquad \mathcal Q_t(x_{t-1})=\sum_{i=1}^{q_t}p_{ti}\,Q_t(x_{t-1},\omega_{ti}),$$
--
--   and the problem [LP1] is $Q_1=\min\{c_1^\top x_1+\mathcal Q_2(x_1): A_1x_1=b_1,\ x_1\ge0\}$.
--
--   A stage-$t$ decision is **reachable** if it is feasible for [LP1] ($t=1$) or for some [LP$_t(x_{t-1},\omega_{ti})$] with $x_{t-1}$ reachable. Assumption **(A4)**, "the feasible region of the linear program in each stage is non-empty and bounded", is read on reachable states: the feasible region of [LP1] is nonempty and bounded, and for $1\le t\le T-1$, every reachable $x_t$ and every outcome $\omega_{t+1,i}$, the feasible region of [LP$_{t+1}(x_t,\omega_{t+1,i})$] is nonempty and bounded.
--
--   Finally, $y$ **solves** [LP$_{t+1}(x_t,\omega_{t+1,i})$] if it is feasible and minimizes $c_{t+1}^\top y+\mathcal Q_{t+2}(y)$ over the feasible region; "solves [LP1]" is analogous.
--
--   These objects are the reference against which every cutting-plane approximation of the mission is measured.
--
--   **Formalization Note** (A1) and (A3) are built into the encoding: the data are deterministic except for the stagewise right-hand sides, whose law does not depend on the past. The paper's $B_{t-1}$ in stage $t$ is `B (t-1)`: matrices are indexed by the stage of the decision they multiply. `V t x` is $\mathcal Q_{t+1}(x_t)$ (so `V T ≡ 0`), `Qo t x i` is $Q_{t+1}(x_t,\omega_{t+1,i})$ and `Q₁` is $Q_1$; they are real infima (`sInf`), which are genuine minima on reachable states under (A4) and junk elsewhere, so every statement of the mission uses them only on reachable states. The paper states (A4) for "the linear program in each stage"; requiring it for every $x_t\ge0$ would be a stronger hypothesis, so it is stated on reachable states only. Optimality ("solves") is relational, not an equation with `sInf`.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), pp. 2–3, (A1)–(A4), [LP1], [LPt]

import Mathlib

open Matrix

namespace SDDPConv.Doasa

/-- A stagewise-independent multistage stochastic linear program with random right-hand sides
(Philpott & Guan, pp. 2–3, (A1)–(A3), [LP1], [LPt]). Stages are numbered `1, …, T` as in the
paper, with `2 ≤ T`. Stage `t` has `n t` decision variables, `m t` equality constraints and
`q t` outcomes. `B t` is the paper's `B_t`: it multiplies the stage-`t` decision `x_t` in the
stage-`(t+1)` constraint `A_{t+1} x_{t+1} = ω_{t+1} − B_t x_t`. The outcomes `ω t i` and their
probabilities `p t i` are only meaningful for `2 ≤ t ≤ T`; there they are positive (A2) and sum
to one. Equal outcome vectors are allowed. -/
structure Instance where
  T : ℕ
  hT : 2 ≤ T
  n : ℕ → ℕ
  m : ℕ → ℕ
  q : ℕ → ℕ
  c : (t : ℕ) → Fin (n t) → ℝ
  A : (t : ℕ) → Matrix (Fin (m t)) (Fin (n t)) ℝ
  B : (t : ℕ) → Matrix (Fin (m (t + 1))) (Fin (n t)) ℝ
  b₁ : Fin (m 1) → ℝ
  ω : (t : ℕ) → Fin (q t) → Fin (m t) → ℝ
  p : (t : ℕ) → Fin (q t) → ℝ
  hp_pos : ∀ t, 2 ≤ t → t ≤ T → ∀ i, 0 < p t i
  hp_sum : ∀ t, 2 ≤ t → t ≤ T → ∑ i, p t i = 1

variable (I : Instance)

/-- The feasible region `{y | y ≥ 0, A_t y = h}` of a stage-`t` problem with right-hand side `h`. -/
def Feas (t : ℕ) (h : Fin (I.m t) → ℝ) : Set (Fin (I.n t) → ℝ) :=
  {y | 0 ≤ y ∧ I.A t *ᵥ y = h}

/-- The stage-`(t+1)` right-hand side `ω_{t+1,i} − B_t x_t` after decision `x_t` and outcome `i`. -/
def rhs (t : ℕ) (x : Fin (I.n t) → ℝ) (i : Fin (I.q (t + 1))) : Fin (I.m (t + 1)) → ℝ :=
  I.ω (t + 1) i - I.B t *ᵥ x

/-- The reachable stage-`t` decisions: `Reach 1` is the feasible set of [LP1], and `Reach (t+1)`
collects every feasible stage-`(t+1)` decision for some reachable `x_t` and some outcome. -/
def Reach : (t : ℕ) → Set (Fin (I.n t) → ℝ)
  | 0 => ∅
  | 1 => Feas I 1 I.b₁
  | t + 2 => {y | ∃ x ∈ Reach (t + 1), ∃ i, y ∈ Feas I (t + 2) (rhs I (t + 1) x i)}

/-- Assumption (A4), p. 3, read on reachable states: the feasible region of [LP1] is nonempty and
bounded, and for every stage `1 ≤ t ≤ T − 1`, every reachable `x_t` and every outcome `i` of stage
`t + 1`, the feasible region of [LP_{t+1}(x_t, ω_{t+1,i})] is nonempty and bounded. -/
def A4 : Prop :=
  (Feas I 1 I.b₁).Nonempty ∧ Bornology.IsBounded (Feas I 1 I.b₁) ∧
    ∀ t, 1 ≤ t → t + 1 ≤ I.T → ∀ x ∈ Reach I t, ∀ i : Fin (I.q (t + 1)),
      (Feas I (t + 1) (rhs I t x i)).Nonempty ∧ Bornology.IsBounded (Feas I (t + 1) (rhs I t x i))

/-- Auxiliary recursion on the number `r` of remaining stages: `Vrem r t x` is the expected
cost-to-go after decision `x_t` when `r` further stages follow. -/
noncomputable def Vrem : ℕ → (t : ℕ) → (Fin (I.n t) → ℝ) → ℝ
  | 0, _, _ => 0
  | r + 1, t, x => ∑ i, I.p (t + 1) i *
      sInf ((fun y => I.c (t + 1) ⬝ᵥ y + Vrem r (t + 1) y) '' Feas I (t + 1) (rhs I t x i))

/-- `V t x` is the paper's expected cost-to-go `𝒬_{t+1}(x_t)`; `V T ≡ 0` (`𝒬_{T+1} ≡ 0`). -/
noncomputable def V (t : ℕ) (x : Fin (I.n t) → ℝ) : ℝ :=
  Vrem I (I.T - t) t x

/-- `Qo t x i` is the paper's `Q_{t+1}(x_t, ω_{t+1,i})`, the optimal value of
[LP_{t+1}(x_t, ω_{t+1,i})]: `min c_{t+1}ᵀ y + 𝒬_{t+2}(y)` over `y ≥ 0`,
`A_{t+1} y = ω_{t+1,i} − B_t x_t`. -/
noncomputable def Qo (t : ℕ) (x : Fin (I.n t) → ℝ) (i : Fin (I.q (t + 1))) : ℝ :=
  sInf ((fun y => I.c (t + 1) ⬝ᵥ y + V I (t + 1) y) '' Feas I (t + 1) (rhs I t x i))

/-- `Q₁`, the optimal value of [LP1]: `min c_1ᵀ x + 𝒬_2(x)` over `x ≥ 0`, `A_1 x = b_1`. -/
noncomputable def Q₁ : ℝ :=
  sInf ((fun x => I.c 1 ⬝ᵥ x + V I 1 x) '' Feas I 1 I.b₁)

/-- `y` solves [LP_{t+1}(x_t, ω_{t+1,i})]: it is feasible and minimizes `c_{t+1}ᵀ y + 𝒬_{t+2}(y)`
over the feasible region. -/
def SolvesLP (t : ℕ) (x : Fin (I.n t) → ℝ) (i : Fin (I.q (t + 1))) (y : Fin (I.n (t + 1)) → ℝ) :
    Prop :=
  y ∈ Feas I (t + 1) (rhs I t x i) ∧
    ∀ z ∈ Feas I (t + 1) (rhs I t x i),
      I.c (t + 1) ⬝ᵥ y + V I (t + 1) y ≤ I.c (t + 1) ⬝ᵥ z + V I (t + 1) z

/-- `x` solves [LP1]. -/
def SolvesLP1 (x : Fin (I.n 1) → ℝ) : Prop :=
  x ∈ Feas I 1 I.b₁ ∧ ∀ z ∈ Feas I 1 I.b₁, I.c 1 ⬝ᵥ x + V I 1 x ≤ I.c 1 ⬝ᵥ z + V I 1 z

end SDDPConv.Doasa


