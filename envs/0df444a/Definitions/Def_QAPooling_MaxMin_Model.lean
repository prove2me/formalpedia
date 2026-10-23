-- Prove2me | Definitions.Def_QAPooling_MaxMin_Model
-- name    : QAPooling_MaxMin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:53.039348+00:00
-- url     : https://prove2.me/theorems/b99ac4ac-502d-4eac-9265-cfa50175e709
-- title:
--   §3, pp. 9–12, Definitions 3.2 and 3.6 — scoring rules on the simplex, regularity, properness, forecast domain, expected reward, exposure function, Bregman divergence, QA pool, the agent's profit
-- statement:
--   This file fixes the objects of §3 and §4 of Neyman and Roughgarden. Throughout, $n$ is the number of outcomes, $\Delta^n=\{p\in\mathbb R^n : p_j\ge 0,\ \sum_j p_j=1\}$ is the standard simplex, and $\delta_j$ is the $j$-th standard basis vector.
--
--   1. A **scoring rule** is a function $s:\Delta^n\times[n]\to\mathbb R\cup\{-\infty\}$; $s(p;j)$ is the reward of an expert who reports $p$ when outcome $j$ happens. The **expected score** of the report $x$ under the belief $p$ is
--   $$\mathbb E_{j\leftarrow p}[s(x;j)]=\sum_{j=1}^n p_j\, s(x;j).$$
--   2. $s$ is **regular** if on $\Delta^n$ it never takes the value $+\infty$, and $s(p;j)=-\infty$ only when $p_j=0$.
--   3. $s$ is **proper** if for all $p,x\in\Delta^n$, $\mathbb E_{j\leftarrow p}[s(p;j)]\ge\mathbb E_{j\leftarrow p}[s(x;j)]$, with equality only when $x=p$ (properness is strict, as in the paper).
--   4. The **forecast domain** $\mathcal D$ is the set of $p\in\Delta^n$ with $s(p;j)$ real for every $j$.
--   5. The **expected reward function** is $G(p)=\mathbb E_{j\leftarrow p}[s(p;j)]=\sum_j p_j s(p;j)$.
--   6. A vector $v$ is a **subgradient** of $G$ at $x$ (relative to $\Delta^n$) if $G(y)\ge G(x)+\langle v,y-x\rangle$ for all $y\in\Delta^n$.
--   7. A map $g$ is an **exposure function** of $s$ if, for every $p\in\mathcal D$ and every outcome $j$,
--   $$s(p;j)=G(p)+\langle g(p),\delta_j-p\rangle \qquad\text{(Equation (2))}.$$
--   8. The **Bregman divergence** is $D_G(p\,\|\,q)=G(p)-G(q)-\langle g(q),p-q\rangle$.
--   9. Given forecasts $p_1,\dots,p_m$ and weights $w_1,\dots,w_m$, a point $p^*$ is a **quasi-arithmetic (QA) pool** if $p^*\in\Delta^n$ and $\sum_i w_i g(p_i)$ is a subgradient of $G$ at $p^*$ (Definition 3.6).
--   10. The agent's **profit** from reporting $q$ when outcome $j$ happens, after paying expert $i$ the amount $w_i s(p_i;j)$, is $u(q;j)=s(q;j)-\sum_i w_i s(p_i;j)$, and its worst case is $\min_j u(q;j)$.
--
--   These are the objects of Theorem 4.1, which says the QA pool is the unique report maximizing the worst-case profit.
--
--   **Formalization Note** Forecasts are functions `Fin n → ℝ` and $\Delta^n$ is Mathlib's `stdSimplex ℝ (Fin n)`; the scoring rule takes values in `EReal`, with only the values on $\Delta^n$ mattering, and $0\cdot(-\infty)=0$ in the expected score. Inner products are written as finite sums. $G$ is the real part (`toReal`) of the expected score and is only evaluated on $\Delta^n$, where it is finite for a regular rule. The paper's Definition 3.2 asks for a differentiable $G$ with gradient $g$; here the Bregman divergence uses an exposure function $g$ in the gradient's role, because the proof of Theorem 4.1 applies it at boundary forecasts where $G$ need not be differentiable. The exposure function is real-valued and constrained only on $\mathcal D$ (the paper's may be $-\infty$ off $\mathcal D$, where Theorem 4.1 never uses it); on $\mathcal D$ it is determined up to adding a multiple of the all-ones vector, which none of the statements depend on. "QA pool" is a predicate; Definition 3.6's uniqueness is the separate theorem `qaPool_existsUnique`. The profit is $-\infty$ when $s(q;j)=-\infty$; the experts' scores are taken as reals since their reports lie in $\mathcal D$. The minimum over outcomes is an infimum over `Fin n` in `EReal`.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, pp. 9–12, 14, §3.1 (scoring rule, proper, regular, footnotes 8, 10), p. 10 (forecast domain D, expected reward G, Proposition 3.1 Equation (2), exposure function), p. 11 Definition 3.2, p. 12 Definition 3.6, p. 14 Theorem 4.1 (u)

import Mathlib

namespace QAPooling.MaxMin

/-- A scoring rule `s : Δⁿ × [n] → ℝ ∪ {−∞}` (§3.1, p. 9), curried: `s p j` is the reward of an
expert who reports `p` when outcome `j` happens. Only the values on the simplex `Δⁿ` matter. -/
abbrev ScoringRule (n : ℕ) := (Fin n → ℝ) → Fin n → EReal

/-- `E_{j←p}[s(x; j)] = Σ_j p_j s(x; j)`: the expected score, under the belief `p`, of the report `x`.
Computed in `EReal`, where `0 * ⊥ = 0`. -/
noncomputable def expectedScore {n : ℕ} (s : ScoringRule n) (p x : Fin n → ℝ) : EReal :=
  ∑ j, (p j : EReal) * s x j

/-- Regularity (p. 9, [GR07, Definition 2]): on `Δⁿ`, `s(p; j)` is never `+∞`, and it is `−∞` only
if `p_j = 0`. -/
def IsRegular {n : ℕ} (s : ScoringRule n) : Prop :=
  ∀ p ∈ stdSimplex ℝ (Fin n), ∀ j, s p j ≠ ⊤ ∧ (s p j = ⊥ → p j = 0)

/-- Properness (p. 9), in the strict sense of footnote 8: for every belief `p ∈ Δⁿ` and every report
`x ∈ Δⁿ`, `E_{j←p}[s(p; j)] ≥ E_{j←p}[s(x; j)]`, with equality only when `x = p`. -/
def IsProper {n : ℕ} (s : ScoringRule n) : Prop :=
  ∀ p ∈ stdSimplex ℝ (Fin n), ∀ x ∈ stdSimplex ℝ (Fin n),
    expectedScore s p x ≤ expectedScore s p p ∧
      (expectedScore s p x = expectedScore s p p → x = p)

/-- The forecast domain `D` (p. 10): the forecasts `p ∈ Δⁿ` with `s(p; j)` real for every `j`. -/
def forecastDomain {n : ℕ} (s : ScoringRule n) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧ ∀ j, s p j ≠ ⊥ ∧ s p j ≠ ⊤}

/-- The expected reward function `G(p) = E_{j←p}[s(p; j)] = Σ_j p(j) s(p; j)` (p. 10). It is real on
`Δⁿ` when `s` is regular; it is only ever evaluated there. -/
noncomputable def expectedReward {n : ℕ} (s : ScoringRule n) (p : Fin n → ℝ) : ℝ :=
  (expectedScore s p p).toReal

/-- `v` is a subgradient of `G` at `x`, relative to the domain `Δⁿ` of `G` (footnote 10):
`G(y) ≥ G(x) + ⟨v, y − x⟩` for all `y ∈ Δⁿ`. -/
def IsSubgradientOn {n : ℕ} (G : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : Prop :=
  ∀ y ∈ stdSimplex ℝ (Fin n), G x + ∑ k, v k * (y k - x k) ≤ G y

/-- `g` is an exposure function of `s` (Proposition 3.1, Equation (2), and p. 10): on the forecast
domain `D`, `s(p; j) = G(p) + ⟨g(p), δ_j − p⟩` for every outcome `j`. -/
def IsExposure {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ p ∈ forecastDomain s, ∀ j,
    s p j = ((expectedReward s p + ∑ k, g p k * ((Pi.single j (1 : ℝ) : Fin n → ℝ) k - p k) : ℝ) : EReal)

/-- The Bregman divergence `D_G(p ∥ q) = G(p) − G(q) − ⟨g(q), p − q⟩` (Definition 3.2), with `G` the
expected reward of `s` and `g` an exposure function of `s` in the role of the gradient. -/
noncomputable def bregman {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (p q : Fin n → ℝ) : ℝ :=
  expectedReward s p - expectedReward s q - ∑ k, g q k * (p k - q k)

/-- Definition 3.6 as a predicate: `p*` is a quasi-arithmetic pool of the forecasts `p i` with
weights `w i` when `p* ∈ Δⁿ` and `Σ_i w_i g(p_i)` is a subgradient of `G` at `p*`. -/
def IsQAPool {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (w : Fin m → ℝ) (pstar : Fin n → ℝ) : Prop :=
  pstar ∈ stdSimplex ℝ (Fin n) ∧
    IsSubgradientOn (expectedReward s) (fun k => ∑ i, w i * g (p i) k) pstar

/-- The agent's profit `u(q; j) = s(q; j) − Σ_i w_i s(p_i; j)` (Theorem 4.1). The experts' reports
lie in `D`, so their scores are real; `u(q; j) = −∞` when `s(q; j) = −∞`. -/
noncomputable def profit {n m : ℕ} (s : ScoringRule n) (p : Fin m → Fin n → ℝ) (w : Fin m → ℝ)
    (q : Fin n → ℝ) (j : Fin n) : EReal :=
  s q j - ((∑ i, w i * (s (p i) j).toReal : ℝ) : EReal)

/-- The agent's worst-case profit `min_j u(q; j)` over the outcomes `j`. -/
noncomputable def minProfit {n m : ℕ} (s : ScoringRule n) (p : Fin m → Fin n → ℝ) (w : Fin m → ℝ)
    (q : Fin n → ℝ) : EReal :=
  ⨅ j, profit s p w q j

end QAPooling.MaxMin


