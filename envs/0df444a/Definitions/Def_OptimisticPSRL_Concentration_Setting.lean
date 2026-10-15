-- Prove2me | Definitions.Def_OptimisticPSRL_Concentration_Setting
-- name    : OptimisticPSRL_Concentration_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:47.080832+00:00
-- url     : https://prove2.me/theorems/2a09aa4c-29b3-4a4a-9f26-d4cc27dc7a57
-- title:
--   Proposition 5.2, p. 9 and Fact 1, p. 17 — stick-breaking scalars γᵢ, cᵢ, H_{i+1}, the multinoulli law and the empirical vector p̂
-- statement:
--   Fix a number of states $S$ and order the states $1,\dots,S$. A **probability vector** $p\in\Delta^S$ has $p_i\ge 0$ and $\sum_i p_i=1$. For $p\in\mathbb R^S$ and $h\in\mathbb R^S$ define the tail sums and the **stick-breaking quantities** of Agrawal and Jia (Proposition 5.2 and Fact 1):
--
--   $$
--   T_i=p_i+\cdots+p_S,\qquad T_{i}^{>}=p_{i+1}+\cdots+p_S,\qquad y_i=\frac{p_i}{T_i},
--   $$
--
--   $$
--   H_{i+1}=\frac{1}{\sum_{j=i+1}^S p_j}\sum_{j=i+1}^S h_jp_j,\qquad c_i=h_i-H_{i+1},\qquad \gamma_i=\frac{p_i\,(p_{i+1}+\cdots+p_S)}{p_i+\cdots+p_S}.
--   $$
--
--   A ratio whose denominator vanishes is read as $0$; then $\gamma_i=0$ and the corresponding terms drop out of every formula below.
--
--   The law of one **multinoulli trial** with parameter $p$ is the measure $\sum_i p_i\,\delta_i$ on the states, and $n$ independent trials have the $n$-fold product law on outcome sequences $\omega=(\omega_1,\dots,\omega_n)$. The **empirical probability vector** is the average of the one-hot outcomes,
--
--   $$
--   \hat p_i(\omega)=\frac{\#\{t:\omega_t=i\}}{n}.
--   $$
--
--   Finally, for one trial with outcome $x$, the coordinate used in the proof of Proposition 5.2 is
--
--   $$
--   Z_i(x)=c_i\,\mathbb 1(x=i)-c_i\,\frac{p_i}{p_i+\cdots+p_S}\,\mathbb 1(x\in\{i,\dots,S\}).
--   $$
--
--   These objects carry the variance-weighted concentration bound of Proposition 5.2: $\sum_{i<S}\gamma_ic_i^2$ is the variance of $h$ under $p$, written in stick-breaking form.
--
--   **Formalization Note** States are `Fin S` with its natural order (0-based: the paper's state $i$ is index $i-1$); the paper's range $i<S$ (all but the last state) is `belowLast S`. Division by zero returns $0$ (Lean's convention), which gives the values the identities need; no positivity of $p$ is assumed. `cat p` is $\sum_i \mathrm{ofReal}(p_i)\,\delta_i$; it is a probability measure when $p$ is a probability vector (the instance provided is finiteness). `phat` takes the sample sequence `ω : Fin n → Fin S`. `Zcoord p h i x` is the iid reading of $Z_{t,i}$, where the indicator $\mathbb 1(s_{t-1}=s,a_{t-1}=a)$ equals one.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 9, Proposition 5.2 (definitions of γ_i, c_i, H_{i+1}); p. 17, Fact 1 (ỹ_i, ȳ_i); p. 21, proof of Proposition 5.2 (Z_{t,i})

import Mathlib

namespace OptimisticPSRL.Concentration

open MeasureTheory

/-- `p` is a probability vector on the states `Fin S` (the paper's `Δ^S`): nonnegative entries
summing to one. The paper's states `1, …, S` are `Fin S` in their natural (0-based) order. -/
def IsProbVec {S : ℕ} (p : Fin S → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The tail sum `p_i + ⋯ + p_S` (indices `j ≥ i` in the order of `Fin S`). -/
noncomputable def tail {S : ℕ} (p : Fin S → ℝ) (i : Fin S) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i ≤ j), p j

/-- The strict tail sum `p_{i+1} + ⋯ + p_S` (indices `j > i`). -/
noncomputable def tailAfter {S : ℕ} (p : Fin S → ℝ) (i : Fin S) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i < j), p j

/-- The stick-breaking ratio `y_i = p_i / (p_i + ⋯ + p_S)` (Fact 1, p. 17); `0` when the tail
vanishes (Lean's `x / 0 = 0`). -/
noncomputable def yRatio {S : ℕ} (p : Fin S → ℝ) (i : Fin S) : ℝ :=
  p i / tail p i

/-- `H_{i+1} = (1 / ∑_{j=i+1}^S p_j) ∑_{j=i+1}^S h_j p_j` (Proposition 5.2, p. 9; Fact 1, p. 17);
`0` when the strict tail vanishes. -/
noncomputable def Hnext {S : ℕ} (p h : Fin S → ℝ) (i : Fin S) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => i < j), h j * p j) / tailAfter p i

/-- `c_i = h_i − H_{i+1}` (Proposition 5.2, p. 9). -/
noncomputable def cCoef {S : ℕ} (p h : Fin S → ℝ) (i : Fin S) : ℝ :=
  h i - Hnext p h i

/-- `γ_i = p_i (p_{i+1} + ⋯ + p_S) / (p_i + ⋯ + p_S)` (Proposition 5.2, p. 9); `0` when the tail
vanishes. -/
noncomputable def gammaCoef {S : ℕ} (p : Fin S → ℝ) (i : Fin S) : ℝ :=
  p i * tailAfter p i / tail p i

/-- The paper's index range `i < S` (1-based `i = 1, …, S − 1`): every state but the last. -/
def belowLast (S : ℕ) : Finset (Fin S) :=
  Finset.univ.filter (fun i : Fin S => (i : ℕ) + 1 < S)

/-- The law of one multinoulli (categorical) trial with parameter `p`:
`∑_i p_i δ_i` on `Fin S`. -/
noncomputable def cat {S : ℕ} (p : Fin S → ℝ) : Measure (Fin S) :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

instance {S : ℕ} (p : Fin S → ℝ) : IsFiniteMeasure (cat p) :=
  ⟨by
    simp only [cat, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top⟩

/-- The law of `n` independent multinoulli trials with parameter `p`: the `n`-fold product of
`cat p` on outcome sequences `ω : Fin n → Fin S`. -/
noncomputable def trialsLaw {S : ℕ} (n : ℕ) (p : Fin S → ℝ) : Measure (Fin n → Fin S) :=
  Measure.pi (fun _ : Fin n => cat p)

/-- The empirical probability vector `p̂`: the average of the `n` one-hot trial outcomes,
`p̂_i = #{t : ω_t = i} / n`. -/
noncomputable def phat {S n : ℕ} (ω : Fin n → Fin S) (i : Fin S) : ℝ :=
  ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) / n

/-- The martingale coordinate of the proof of Proposition 5.2 (p. 21) for one trial with outcome
`x`, in the iid reading (the indicator `1(s_{t−1} = s, a_{t−1} = a)` equals one):
`Z_i(x) = c_i 1(x = i) − c_i (p_i / (p_i + ⋯ + p_S)) 1(x ∈ {i, …, S})`. -/
noncomputable def Zcoord {S : ℕ} (p h : Fin S → ℝ) (i x : Fin S) : ℝ :=
  cCoef p h i * ((if x = i then 1 else 0) - yRatio p i * (if i ≤ x then 1 else 0))

end OptimisticPSRL.Concentration


