-- Prove2me | Definitions.Def_OffGridStorage_TechChoice_Model
-- name    : OffGridStorage_TechChoice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:14.47056+00:00
-- url     : https://prove2.me/theorems/fee3b576-ad3c-48a4-b4dd-4a9785f0e59b
-- title:
--   §3.1–§3.2.2, pp. 6–13 — off-grid solar + storage: charge recursion, tracking and full-discharge profits, optimal plans, Γ and Definition 1
-- statement:
--   An off-grid utility serves $T$ periods, each consisting of a day with deterministic demand $D_H>0$ and a night with deterministic demand $D_L>0$. It installs solar capacity $Q\ge 0$ at per-period unit cost $c_Q$ and storage of discharge capacity $K\ge 0$ at per-period unit cost $c_K/e$, where $0<e\le 1$ is the cycle efficiency. Day generation in period $t$ is $q_t$, with $q_1,\dots,q_T$ i.i.d. uniform on $[0,Q]$; there is no generation at night. Demand not met by solar or storage is served by a fossil backup with marginal cost $g$, so every unit of renewable energy served is worth $g$. Write $(a)^+=\max[0,a]$.
--
--   **Charge recursion (eq. (1)).** Storage starts empty, $x_0=0$, and
--
--   $$x_t=\Bigl(\min\bigl[\bigl(x_{t-1}+e(q_t-D_H)^+-(D_H-q_t)^+\bigr)^+,\,K\bigr]-D_L\Bigr)^+ .$$
--
--   **Tracking model (eq. (4)).**
--
--   $$\Pi_{TR}(Q,K)=g\,E\Bigl[\sum_{t=1}^{T}\Bigl(\min[x_{t-1}+q_t,D_H]+\min\bigl[\bigl(x_{t-1}+e(q_t-D_H)^+-(D_H-q_t)^+\bigr)^+,K,D_L\bigr]\Bigr)\Bigr]-T\frac{c_K}{e}K-Tc_QQ .$$
--
--   **Full-discharge model (eq. (5)).** With $q\sim U[0,Q]$,
--
--   $$\Pi_F(Q,K)=T\Bigl(g\,E\bigl[\min[q,D_H]+\min[e(q-D_H)^+,K]\bigr]-\frac{c_K}{e}K-c_QQ\Bigr).$$
--
--   The closed form (20), multiplied by $T$, is $T\bigl(\tfrac{g}{Q}[-\tfrac{D_H^2}{2}-\tfrac{K^2}{2e}-KD_H]+g(D_H+K)-\tfrac{c_K}{e}K-c_QQ\bigr)$. The thresholds are
--
--   $$g_0=c_Q+\frac{c_K}{e}+\sqrt{c_Q^2+\frac{2c_Qc_K}{e}},\qquad Q_0=D_H\sqrt{\frac{g}{2c_Q}} .$$
--
--   A plan $(Q,K)$ with $Q,K\ge 0$ is optimal for a model if it maximizes that model's profit over all plans with $Q',K'\ge 0$. "Optimal storage is positive" ($K^*_{TR}>0$) means that an optimal tracking plan exists and every optimal tracking plan has $K>0$.
--
--   **Definition 1.** For a technology $j=(e^j,c_K^j)$ and a fixed $T$, $\Gamma^j$ is the set of tuples $(c_Q,D_H,D_L,g)$ with $c_Q>0$, $D_H>0$, $D_L>0$, $2c_Q<g$ for which optimal tracking storage is positive. Technology $A$ is preferred to $B$ iff $\Gamma^A\supsetneq\Gamma^B$.
--
--   These are the objects of the paper's comparison of storage technologies (Lemma 1, Theorem 2) and of the full-discharge approximation (Theorems 3–4).
--
--   **Formalization Note** The standing assumptions are bundled in `Standing`: $D_H,D_L>0$, $0<e\le1$, $2c_Q<g$ from the paper, plus $c_Q>0$, $c_K\ge0$ and $T\ge1$, which the paper uses tacitly. Generation is $q_t=Qu_t$ with $u$ uniform on the unit cube $[0,1]^T$ (Lebesgue measure restricted to the cube, a probability measure), so $Q=0$ is allowed. Periods are indexed from $0$ in Lean; `charge p K q n` is the paper's $x_n$. The integrands are continuous and bounded, so the Bochner integrals are genuine expectations. Definition 1's $\supset$ is read as a proper superset, and $K^*_{TR}>0$ includes existence of an optimum, so that it cannot hold vacuously.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), pp. 6–13, §3.1, §3.2.1, §3.2.2, eqs. (1), (4), (5), Definition 1 (p. 11), Lemma 1 (p. 12), eqs. (20) (p. 37), (25) (p. 39); footnote 3 (p. 15)

import Mathlib

open MeasureTheory

noncomputable section

namespace OffGridStorage.TechChoice

/-- The parameters of the off-grid model (§3.1, pp. 6–8): day demand `DH`, night demand `DL`,
cycle efficiency `e`, per-period unit storage cost `cK` (before the `1/e` adjustment), per-period
unit generation-capacity cost `cQ`, marginal cost `g` of the fossil backup, and the number of
periods `T`. -/
structure Params where
  DH : ℝ
  DL : ℝ
  e : ℝ
  cK : ℝ
  cQ : ℝ
  g : ℝ
  T : ℕ

/-- Standing assumptions of §3.1: `0 < DH`, `0 < DL` (p. 6), `0 < e ≤ 1` (p. 7), `2 cQ < g`
(p. 7); added: `0 < cQ`, `0 ≤ cK` (unit costs) and `1 ≤ T`. -/
def Standing (p : Params) : Prop :=
  0 < p.DH ∧ 0 < p.DL ∧ 0 < p.e ∧ p.e ≤ 1 ∧ 0 < p.cQ ∧ 0 ≤ p.cK ∧ 2 * p.cQ < p.g ∧ 1 ≤ p.T

/-- The positive part `(a)^+ = max[0, a]`. -/
def pos (a : ℝ) : ℝ := max 0 a

/-- The charge after the day sub-period, before the capacity cap:
`(x_{t-1} + e (q_t - D_H)^+ - (D_H - q_t)^+)^+`. -/
def afterDay (p : Params) (x q : ℝ) : ℝ :=
  pos (x + p.e * pos (q - p.DH) - pos (p.DH - q))

/-- Equation (1), p. 9: the charge at the end of a period, from the charge `x` at its start and
its day generation `q`: `x_t = (min[afterDay, K] - D_L)^+`. -/
def nextCharge (p : Params) (K x q : ℝ) : ℝ :=
  pos (min (afterDay p x q) K - p.DL)

/-- The charge path of the tracking model for a generation path `q : Fin T → ℝ` (the paper's
period `n + 1` has index `n`). `charge p K q n` is the charge at the start of the period with
index `n`, i.e. the paper's `x_n`; storage starts empty, `x_0 = 0` (footnote 3, p. 15). -/
def charge (p : Params) (K : ℝ) (q : Fin p.T → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextCharge p K (charge p K q n) (if h : n < p.T then q ⟨n, h⟩ else 0)

/-- Revenue (before multiplying by `g`) of one period of the tracking model with starting charge
`x` and generation `q`: day term `min[x + q, D_H]` (eq. (2)) plus night term
`min[afterDay, K, D_L]` (eq. (3)). -/
def periodRevenueTR (p : Params) (K x q : ℝ) : ℝ :=
  min (x + q) p.DH + min (afterDay p x q) (min K p.DL)

/-- Energy served from renewables over the `T` periods along the generation path `q`. -/
def revenueTR (p : Params) (K : ℝ) (q : Fin p.T → ℝ) : ℝ :=
  ∑ t : Fin p.T, periodRevenueTR p K (charge p K q t.val) (q t)

/-- The unit cube `[0,1]^n`; Lebesgue measure restricted to it is the law of `n` i.i.d.
`U[0,1]` variables. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

/-- Equation (4), p. 10: the tracking model's expected profit. Generation is `q_t = Q u_t` with
`u` uniform on `[0,1]^T`, i.e. the `q_t` are i.i.d. `U[0, Q]`. -/
def profitTR (p : Params) (Q K : ℝ) : ℝ :=
  p.g * (∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t))
    - (p.T : ℝ) * (p.cK / p.e) * K - (p.T : ℝ) * p.cQ * Q

/-- Equation (5), p. 13: the full-discharge model's expected profit,
`T (g E[min[q, D_H] + min[e (q - D_H)^+, K]] - (c_K/e) K - c_Q Q)` with `q = Q v`, `v ∼ U[0,1]`. -/
def profitF (p : Params) (Q K : ℝ) : ℝ :=
  (p.T : ℝ) * (p.g * (∫ v in Set.Icc (0 : ℝ) 1,
      (min (Q * v) p.DH + min (p.e * pos (Q * v - p.DH)) K))
    - p.cK / p.e * K - p.cQ * Q)

/-- Equation (20), p. 37, times `T`: the closed form of the full-discharge profit, valid on the
region `D_H + K/e ≤ Q`. -/
def closedFormF (p : Params) (Q K : ℝ) : ℝ :=
  (p.T : ℝ) * (p.g / Q * (-p.DH ^ 2 / 2 - K ^ 2 / (2 * p.e) - K * p.DH) + p.g * (p.DH + K)
    - p.cK / p.e * K - p.cQ * Q)

/-- `(Q, K)` is an optimal plan of the tracking model: `Q, K ≥ 0` and `Π_TR(Q, K)` is the
maximum of `Π_TR` over all plans `Q', K' ≥ 0`. -/
def IsOptimalTR (p : Params) (Q K : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ K ∧ ∀ Q' K' : ℝ, 0 ≤ Q' → 0 ≤ K' → profitTR p Q' K' ≤ profitTR p Q K

/-- `(Q, K)` is an optimal plan of the full-discharge model. -/
def IsOptimalF (p : Params) (Q K : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ K ∧ ∀ Q' K' : ℝ, 0 ≤ Q' → 0 ≤ K' → profitF p Q' K' ≤ profitF p Q K

/-- "`K*_TR > 0`": an optimal tracking plan exists, and every optimal tracking plan has strictly
positive storage. -/
def OptimalStoragePos (p : Params) : Prop :=
  (∃ Q K : ℝ, IsOptimalTR p Q K) ∧ ∀ Q K : ℝ, IsOptimalTR p Q K → 0 < K

/-- The threshold as a function of `c_Q` and the cost-to-efficiency ratio `r = c_K/e`:
`c_Q + r + √(c_Q² + 2 c_Q r)`. -/
def g0ratio (cQ r : ℝ) : ℝ := cQ + r + Real.sqrt (cQ ^ 2 + 2 * cQ * r)

/-- Lemma 1 and Theorem 4, pp. 12–13: `g0 = c_Q + c_K/e + √(c_Q² + 2 c_Q c_K / e)`. -/
def g0 (p : Params) : ℝ := p.cQ + p.cK / p.e + Real.sqrt (p.cQ ^ 2 + 2 * p.cQ * p.cK / p.e)

/-- Equation (25), p. 39: the optimal generation capacity without storage,
`Q*_F(K = 0) = √((g/c_Q) D_H²/2)`, written `D_H √(g/(2 c_Q))` (equal since `D_H > 0`). -/
def Q0 (p : Params) : ℝ := p.DH * Real.sqrt (p.g / (2 * p.cQ))

/-- A storage technology `(e, c_K)`. -/
structure Tech where
  e : ℝ
  cK : ℝ

/-- An admissible technology: `0 < e ≤ 1`, `0 ≤ c_K`. -/
def ValidTech (j : Tech) : Prop := 0 < j.e ∧ j.e ≤ 1 ∧ 0 ≤ j.cK

/-- The market part of the standing assumptions for a non-storage tuple
`m = (c_Q, D_H, D_L, g)`: `0 < c_Q`, `0 < D_H`, `0 < D_L`, `2 c_Q < g`. -/
def MarketStanding (m : ℝ × ℝ × ℝ × ℝ) : Prop :=
  0 < m.1 ∧ 0 < m.2.1 ∧ 0 < m.2.2.1 ∧ 2 * m.1 < m.2.2.2

/-- The parameter set built from `T`, a technology `j` and a tuple `m = (c_Q, D_H, D_L, g)`. -/
def withMarket (T : ℕ) (j : Tech) (m : ℝ × ℝ × ℝ × ℝ) : Params where
  DH := m.2.1
  DL := m.2.2.1
  e := j.e
  cK := j.cK
  cQ := m.1
  g := m.2.2.2
  T := T

/-- Definition 1, p. 11: `Γ^j`, the set of non-storage parameters `(c_Q, D_H, D_L, g)` (within
the standing assumptions) for which it is optimal to invest in strictly positive storage under
technology `j`, for a fixed number of periods `T`. -/
def Gamma (T : ℕ) (j : Tech) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {m | MarketStanding m ∧ OptimalStoragePos (withMarket T j m)}

/-- Definition 1, p. 11: technology `A` is preferred to technology `B` iff `Γ^A ⊃ Γ^B`, read as
a proper superset. -/
def Preferred (T : ℕ) (A B : Tech) : Prop := Gamma T B ⊂ Gamma T A

end OffGridStorage.TechChoice


