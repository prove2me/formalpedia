-- Prove2me | Definitions.Def_ForwardRM_Cutoffs_ValueFunction
-- name    : ForwardRM_Cutoffs_ValueFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:16:13.80438+00:00
-- url     : https://prove2.me/theorems/bb2f9c42-dd1a-48dc-b7a8-3b0d4d82a755
-- title:
--   (4.1)–(4.3) — the seller's value Π^k_t, its pre-entry version Π̃^k_t, and optimal sell/wait choices
-- statement:
--   This file defines the seller's dynamic program of §4.1 by backward induction (the Bellman equation (4.3)).
--
--   The state at period $t$, after the period-$t$ entrants have arrived, is the number $k$ of units left and the finite multiset $S$ of values of the buyers present, listed in decreasing order as $y^1\ge y^2\ge\cdots$. Absent buyers are simply absent. Write $y^{-j}$ for the buyers left after the $j$ highest are served. The **pre-entry value** is
--
--   $$
--   \tilde\Pi^k_{t}(S)=E_t\big[\Pi^k_t(S\cup \mathbf v_t)\big],
--   $$
--
--   where $\mathbf v_t$ is the cohort of period-$t$ entrants: $N_t$ buyers with i.i.d. values of density $f$. The **value** $\Pi^k_t(S)$ is defined for $t\in\{1,\dots,T\}$ by
--
--   $$
--   \Pi^k_t(S)=\max_{0\le j\le \min(k,|S|)}\Big[\sum_{i=1}^{j}m(y^i)+\delta\,\tilde\Pi^{k-j}_{t+1}(y^{-j})\Big],
--   $$
--
--   with $\Pi^k_{T+1}\equiv 0$ (unsold units are worth zero). The bracket for a given $j$ is the profit from selling exactly $j$ units now, to the $j$ highest buyers, and continuing optimally.
--
--   Two predicates describe the optimal choice: **selling is optimal** at $(t,k,S)$ if some $j\ge 1$ attains the maximum, and **waiting is optimal** if $j=0$ attains it. A number $x$ is a **deterministic cutoff** for period $t$ with $k$ units if, for every highest buyer $y^1\in[\underline v,\bar v]$ and every multiset of lower buyers with values in $[\underline v,y^1]$, selling is optimal when $y^1\ge x$ and waiting is optimal when $y^1\le x$. Finally, the backward-induction hypothesis of Lemma 3 says that the **future cutoffs are deterministic and decreasing**: there are numbers $x^j_s$, for $s\in\{t+1,\dots,T\}$ and $j\in\{1,\dots,k\}$, each a deterministic cutoff for period $s$ with $j$ units, with $x^j_s\le x^{j-1}_s$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** The value is defined through the Bellman equation (4.3), which the paper says may be used in place of the sequence problem (4.1) (p. 12 and footnote 16); the sequence problem over adapted purchase times is not formalized. The expectation over a cohort is $\sum_n P(N_t=n)\int (\cdot)\,d(\mu\otimes\cdots\otimes\mu)$ computed as a lower Lebesgue integral of the positive part and converted to a real number. The value is nonnegative (selling nothing is always allowed) and bounded on the support, so neither the positive part nor the conversion changes anything; no measurability side condition is needed. The state is the full multiset of buyers present, not its top-$k$ truncation; the value only depends on the top $k$ buyers, which the paper notes on p. 12.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, pp. 12–13, §4.1, eqs. (4.1)–(4.3); p. 15, Lemma 3 hypothesis; p. 18, footnote 16

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model

namespace ForwardRM.Cutoffs

open MeasureTheory

/-- The buyers present, a finite multiset of values, listed from the highest value to the
lowest: `sortDesc S = [y¹, y², …]` with `yⁱ ≥ yⁱ⁺¹`. Absent buyers are simply absent. -/
noncomputable def sortDesc (S : Multiset ℝ) : List ℝ :=
  S.sort (· ≥ ·)

/-- The buyers left after the `j` highest are served: `y^{-j} = {y^{j+1}, …}`. -/
noncomputable def dropTop (j : ℕ) (S : Multiset ℝ) : Multiset ℝ :=
  ((sortDesc S).drop j : List ℝ)

/-- The entrants of one period, as a multiset of values: the cohort of `n` buyers with values
`x 0, …, x (n-1)`. -/
noncomputable def cohort {n : ℕ} (x : Fin n → ℝ) : Multiset ℝ :=
  (List.ofFn x : List ℝ)

namespace Model

variable (M : Model)

/-- Revenue `∑_{i=1}^{j} m(yⁱ)` from selling to the `j` highest buyers present. -/
noncomputable def sumTop (j : ℕ) (S : Multiset ℝ) : ℝ :=
  (((sortDesc S).take j).map M.m).sum

/-- The expectation, over the period-`s` entrants, of a nonnegative quantity `g` of the cohort:
`∑ₙ P(N_s = n) ∫ (ofReal ∘ g)(cohort x) d(μ ⊗ ⋯ ⊗ μ)(x)` as an extended nonnegative real
(the cohort has `n ~ arrivals s` buyers with i.i.d. values of law `μ`). As a lower Lebesgue
integral it needs no measurability or integrability side condition. -/
noncomputable def cohortLIntegral (s : ℕ) (g : Multiset ℝ → ℝ) : ENNReal :=
  ∑' n : ℕ, (M.arrivals s n) *
    ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (g (cohort x)) ∂(Measure.pi fun _ : Fin n => M.law)

/-- `E_s[g]` for a nonnegative, bounded quantity `g` of the period-`s` cohort (the real value of
`cohortLIntegral`). Every quantity it is applied to in this development is nonnegative and bounded
on the support, so neither the positive part nor the conversion from `ℝ≥0∞` truncates anything. -/
noncomputable def cohortExp (s : ℕ) (g : Multiset ℝ → ℝ) : ℝ :=
  (M.cohortLIntegral s g).toReal

/-- `E_s[max{a, X}]` for a real constant `a` and a quantity `X` of the period-`s` cohort,
written as `a + E_s[(X − a)⁺]`, which is the same number and only integrates a nonnegative
quantity. -/
noncomputable def expMaxWith (s : ℕ) (a : ℝ) (X : Multiset ℝ → ℝ) : ℝ :=
  a + M.cohortExp s (fun C => max (X C - a) 0)

/-- The seller's value by backward induction (Bellman equation (4.3), p. 13), indexed by the
number `r` of periods left including the current one: the current period is `t = T + 1 − r`.

* `r = 0` (after period `T`): unsold units are worth zero.
* `r + 1`: with `k` units and buyers `S` present (period-`t` entrants included), the seller chooses
  how many units `j ∈ {0, …, min(k, |S|)}` to sell now, to the `j` highest buyers, and gets
  `∑_{i ≤ j} m(yⁱ) + δ · E_{t+1}[value with k − j units and buyers y^{-j} ∪ (period-(t+1) entrants)]`. -/
noncomputable def valueAux : ℕ → ℕ → Multiset ℝ → ℝ
  | 0, _, _ => 0
  | r + 1, k, S =>
    (Finset.range (min k (Multiset.card S) + 1)).sup' Finset.nonempty_range_add_one
      (fun j => M.sumTop j S +
        M.δ * M.cohortExp (M.T + 1 - r) (fun C => valueAux r (k - j) (dropTop j S + C)))

/-- `Π^k_t(S)`: the seller's optimal continuation profit at the start of period `t` with `k` units,
after the period-`t` entrants have arrived, when the buyers present have values `S` ((4.1)/(4.3)). -/
noncomputable def piVal (t k : ℕ) (S : Multiset ℝ) : ℝ :=
  M.valueAux (M.T + 1 - t) k S

/-- `Π̃^k_t(S) = E_t[Π^k_t(S ∪ v_t)]` ((4.2)): the period-`t` continuation profit before the
period-`t` entrants `v_t` arrive. -/
noncomputable def piTilde (t k : ℕ) (S : Multiset ℝ) : ℝ :=
  M.cohortExp t (fun C => M.piVal t k (S + C))

/-- The bracket of the Bellman equation (4.3): the profit from selling exactly `j` units in
period `t` (to the `j` highest buyers) and continuing optimally,
`∑_{i=1}^{j} m(yⁱ) + δ Π̃^{k−j}_{t+1}(y^{-j})`. -/
noncomputable def bracket (t k : ℕ) (S : Multiset ℝ) (j : ℕ) : ℝ :=
  M.sumTop j S + M.δ * M.piTilde (t + 1) (k - j) (dropTop j S)

/-- Selling at least one unit in period `t` (hence to the highest buyer present) is optimal:
some `j ≥ 1` (with `j ≤ k` and `j ≤ |S|`) attains the maximum in (4.3). -/
def SellOptimal (t k : ℕ) (S : Multiset ℝ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ min k (Multiset.card S) ∧ M.bracket t k S j = M.piVal t k S

/-- Selling nothing in period `t` is optimal: `j = 0` attains the maximum in (4.3). -/
def WaitOptimal (t k : ℕ) (S : Multiset ℝ) : Prop :=
  M.bracket t k S 0 = M.piVal t k S

/-- The number `x` is a deterministic cutoff for the sale of the first unit in period `t` with `k`
units: for every highest buyer `y¹ ∈ [v̲, v̄]` and every configuration `y^{-1}` of lower buyers
(values in `[v̲, y¹]`), selling to `y¹` is optimal when `y¹ ≥ x`, and selling nothing is optimal
when `y¹ ≤ x`. -/
def CutoffRule (t k : ℕ) (x : ℝ) : Prop :=
  ∀ y1 ∈ Set.Icc M.vlo M.vhi, ∀ S : Multiset ℝ, (∀ s ∈ S, s ∈ Set.Icc M.vlo y1) →
    (x ≤ y1 → M.SellOptimal t k (y1 ::ₘ S)) ∧ (y1 ≤ x → M.WaitOptimal t k (y1 ::ₘ S))

/-- The backward-induction hypothesis of Lemma 3 (p. 15) and of the proof of Theorem 1 (p. 16):
the future cutoffs `{x^j_s}_{s ≥ t+1}`, `j ≤ k`, are deterministic (some number `x s j`, independent
of the lower buyers, is a cutoff in the sense of `CutoffRule` in every period `s ∈ {t+1, …, T}` and
for every `j ∈ {1, …, k}`) and decreasing in `j`. -/
def FutureCutoffsDecreasing (t k : ℕ) : Prop :=
  ∃ x : ℕ → ℕ → ℝ, ∀ s, t + 1 ≤ s → s ≤ M.T →
    (∀ j, 1 ≤ j → j ≤ k → M.CutoffRule s j (x s j)) ∧
    (∀ j, 2 ≤ j → j ≤ k → x s j ≤ x s (j - 1))

end Model

end ForwardRM.Cutoffs


