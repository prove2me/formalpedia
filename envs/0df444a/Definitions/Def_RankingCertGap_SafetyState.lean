-- Prove2me | Definitions.Def_RankingCertGap_SafetyState
-- name    : RankingCertGap_SafetyState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:20.568718+00:00
-- url     : https://prove2.me/theorems/80a536ef-40b8-4bbd-ad40-ea5471c274c5
-- title:
--   The constant $c$, $b_{\mathrm{sym}}$, safety states, $\mathcal S_2$, feasible budgets and the budget of Table 2
-- statement:
--   The constant of the degree-two analysis is $c:=1-\sum_{k\ge1}2^{-(2^k+k-1)}$, and $b_{\mathrm{sym}}(q):=q-\sum_{\ell\ge1}q^{2^\ell}/2^{2^\ell+\ell-1}$ for $q\in[0,1]$.
--
--   A **safety state** is a pair $\mathbf s=(m,q)$; a dead state is $\bot$ with $q(\bot)=0$. For two states, put $P(\mathbf s_1,\mathbf s_2)=q_1+q_2-q_1q_2$ and
--
--   $$
--   \mathbf s_1^+=\Bigl(m_1+m_2,\frac{m_1q_1q_2}{m_1+m_2}\Bigr),\qquad \mathbf s_2^+=\Bigl(m_1+m_2,\frac{m_2q_1q_2}{m_1+m_2}\Bigr).
--   $$
--
--   $\mathcal S_2$ is the smallest set containing $(1,1)$ and closed under these outputs. A **feasible budget** $b$ on $\mathcal S_2\cup\{\bot\}$ has $b(\bot)=0$, $b(1,1)=c$, $0\le b(\mathbf s)\le\min\{c,q(\mathbf s)\}$, and $b(\mathbf s_1)+b(\mathbf s_2)-b(\mathbf s_k^+)\le P(\mathbf s_1,\mathbf s_2)$ for every pair of positive states and $k\in\{1,2\}$.
--
--   The **explicit budget** gives a dyadic state $(2^k,2^{-(2^k-1)})$ the value $b_{\mathrm{sym}}(2^{-(2^k-1)})$, gives the seven non-dyadic states of Table 2 their tabulated values, and gives every other state and $\bot$ the value $0$.
--
--   **Formalization Note** Both series are shifted so that the summation index starts at $0$, which avoids natural-number subtraction in the exponents. Dyadic states take precedence; the four dyadic rows of Table 2 agree with $b_{\mathrm{sym}}$ by (74). The verification file proves that both series are summable on $[0,1]$. $\bot$ is $\texttt{none}$ in $\texttt{Option State}$, and states compare as pairs.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §6, p.24; §6.1, p.25; eq. (73), p.25; §6.2 and Table 2, p.26

import Mathlib

namespace RankingCertGap

/-- The constant `c := 1 − Σ_{k=1}^∞ 2^{−(2^k + k − 1)}`. Xu, arXiv:2610.17545 (held file sha256
75896dd9…), §6, p.24.

**Formalization Note.** The sum is shifted to `k + 1` for `k : ℕ`, so the exponent is
`2^(k+1) + (k+1) − 1 = 2^(k+1) + k`, with no natural-number subtraction. The series is summable (the
verification file proves it), so `tsum` does not take its junk value. -/
noncomputable def cStar : ℝ := 1 - ∑' k : ℕ, (1 / 2 : ℝ) ^ (2 ^ (k + 1) + k)

/-- `b_sym(q) := q − Σ_{ℓ=1}^∞ q^{2^ℓ} / 2^{2^ℓ + ℓ − 1}`, `q ∈ [0, 1]`. Eq. (73), p.25.

**Formalization Note.** Shifted as in `cStar`. The formula is read only on `q ∈ (0, 1]`. -/
noncomputable def bSym (q : ℝ) : ℝ := q - ∑' l : ℕ, q ^ (2 ^ (l + 1)) / 2 ^ (2 ^ (l + 1) + l)

/-- A safety state `s = (m, q)` (p.25). -/
abbrev State : Type := ℕ × ℝ

/-- `P(s₁, s₂) = q₁ + q₂ − q₁q₂`, eq. (71), p.25. -/
def stateP (s₁ s₂ : State) : ℝ := s₁.2 + s₂.2 - s₁.2 * s₂.2

/-- `s₁⁺ = (m₁ + m₂, m₁q₁q₂/(m₁ + m₂))`, eq. (71), p.25. -/
noncomputable def outLeft (s₁ s₂ : State) : State :=
  (s₁.1 + s₂.1, (s₁.1 : ℝ) * s₁.2 * s₂.2 / ((s₁.1 : ℝ) + s₂.1))

/-- `s₂⁺ = (m₁ + m₂, m₂q₁q₂/(m₁ + m₂))`, eq. (71), p.25. -/
noncomputable def outRight (s₁ s₂ : State) : State :=
  (s₁.1 + s₂.1, (s₂.1 : ℝ) * s₁.2 * s₂.2 / ((s₁.1 : ℝ) + s₂.1))

/-- `S₂`: "the smallest set containing `(1, 1)` and closed under the two outputs in (71)" (p.25). -/
inductive InS2 : State → Prop
  | fresh : InS2 (1, 1)
  | left {s₁ s₂ : State} : InS2 s₁ → InS2 s₂ → InS2 (outLeft s₁ s₂)
  | right {s₁ s₂ : State} : InS2 s₁ → InS2 s₂ → InS2 (outRight s₁ s₂)

/-- `q(s)`, with `q(⊥) = 0` (p.25). The dead state `⊥` is `none`. -/
def stateQ : Option State → ℝ
  | none => 0
  | some s => s.2

/-- The hypotheses of Lemma 10, p.25, on a budget `b` on `S₂ ∪ {⊥}`:
`b(⊥) = 0`, `b(1, 1) = c`, `0 ≤ b(s) ≤ min{c, q(s)}`, and for every pair of positive input states
`b(s₁) + b(s₂) − b(s_k⁺) ≤ P(s₁, s₂)`, `k ∈ {1, 2}` (eq. (72)).

**Formalization Note.** `b` is total on `Option State`, and only its values on `S₂ ∪ {⊥}` are read:
an output of two states of `S₂` lies in `S₂`. -/
structure IsFeasibleBudget (b : Option State → ℝ) : Prop where
  dead : b none = 0
  fresh : b (some (1, 1)) = cStar
  bounds : ∀ s : Option State, (s = none ∨ ∃ s', s = some s' ∧ InS2 s') →
    0 ≤ b s ∧ b s ≤ min cStar (stateQ s)
  pair : ∀ s₁ s₂ : State, InS2 s₁ → InS2 s₂ →
    b (some s₁) + b (some s₂) - b (some (outLeft s₁ s₂)) ≤ stateP s₁ s₂ ∧
      b (some s₁) + b (some s₂) - b (some (outRight s₁ s₂)) ≤ stateP s₁ s₂

open Classical in
/-- The budget of §6.2, p.26: a dyadic state `(2^k, 2^{−(2^k − 1)})` gets `b_sym(2^{−(2^k − 1)})`;
the seven non-dyadic states of Table 2 get their tabulated values; every other state, and `⊥`,
gets `0`.

**Formalization Note.** Dyadic states take precedence. The four dyadic rows of Table 2, namely
`(1, 1)`, `(2, 1/2)`, `(4, 1/8)`, `(8, 1/128)`, have the tabulated values `c`, `2c − 1`, `4c − 11/4`,
`8c − 367/64` by (74), p.25. States compare as pairs: a non-dyadic state whose `m` is a power of
two gets `0`. -/
noncomputable def budget : Option State → ℝ
  | none => 0
  | some s =>
    if ∃ k : ℕ, s = (2 ^ k, (1 / 2 : ℝ) ^ (2 ^ k - 1)) then bSym s.2
    else if s = (3, 1 / 6) ∨ s = (3, 1 / 3) then 3 * cStar - 2
    else if s = (5, 1 / 30) ∨ s = (5, 1 / 20) then 5 * cStar - 43 / 12
    else if s = (6, 1 / 72) then 6 * cStar - 155 / 36
    else if s = (7, 1 / 112) ∨ s = (7, 1 / 84) then 7 * cStar - 241 / 48
    else 0

end RankingCertGap


