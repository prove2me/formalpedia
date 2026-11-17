-- Prove2me | Definitions.Def_SkipListConc_Supplement_IsTRule
-- name    : SkipListConc_Supplement_IsTRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:49:18.171372+00:00
-- url     : https://prove2.me/theorems/5dd6cc94-3712-4b67-affd-0de3eef4a784
-- title:
--   Promotion rule with properties (T1)–(T4) and non-decreasing heights
-- statement:
--   Fix $0<p<1$ and an integer $K\ge1$. A **promotion rule with properties (T1)–(T4) whose heights never decrease** is described by its height process: on a probability space, $H_y(j)$ is the height of item $y$ after its $j$-th operation ($j\ge1$), an integer $\ge1$, and
--
--   1. **(T1) upper tail:** there is a constant $C$ with $\Pr[H_y(j)\ge\ell]\le C\,j\,p^{\ell-K}$ for all items $y$, $j\ge1$, $\ell\ge1$;
--   2. **(T2) lower bound:** for each item $y$ there is a Morris chain $M_y$ (Definition 2.4) on the same space with $H_y(j)\ge M_y(j)$ for every $j\ge1$ and every outcome;
--   3. **(T3) conditional hazard:** at every operation $j$ at which $y$ has height at least $\ell$, its height is at least $\ell+1$ with probability at least $p$, given $y$'s own trajectory cut off at $\ell$;
--   4. **(T4) independence:** the trajectories $(H_y(j))_j$ of distinct items are independent;
--   5. $H_y(j)\le H_y(j+1)$ for all $j\ge1$.
--
--   Definition 1.1 has these properties (Lemmas 2.2, 2.5, 3.6), and so do the counter-based estimators (Corollary 1.3). Theorem D is stated for every such rule.
--
--   **Formalization Note** (T3) is stated for every horizon $N\ge j$ and every value $\tau$ of the cut-off trajectory $(\min(H_y(i),\ell))_{1\le i\le N}$ with $\tau_j=\ell$, in multiplied form $P(\text{cut}=\tau,\ H_y(j)\ge\ell+1)\ge p\,P(\text{cut}=\tau)$. The Morris chains of (T2) need not be independent across items. Heights are measurable; the value before the first operation is never read.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.6–7 ((T1)–(T4)); forms of Lemma 2.2 (p.14), Lemma 2.5 with Definition 2.4 (p.14), Lemma 3.6(iii) (p.18)

import Mathlib
import Definitions.Def_SkipListConc_Supplement_IsMorrisChain

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- A promotion rule with properties (T1) to (T4) whose heights never decrease
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.1, pp.6–7; the forms of (T1)–(T3) are those of Lemma 2.2, Lemma 2.5 with
Definition 2.4, and Lemma 3.6(iii), pp.14, 18), as a property of a height process
`H : α → ℕ → Ω → ℕ` on a probability space: `H y j` is the height of item `y` after its
`j`-th operation (`j ≥ 1`), an integer `≥ 1`.

* (T1) upper tail: `Pr[H_y(j) ≥ ℓ] ≤ C j p^{ℓ−K}` for a constant `C`, all `y`, `j ≥ 1`, `ℓ ≥ 1`;
* (T2) lower bound: for each item `y` a Morris chain `M_y` (Definition 2.4) on the same space
  with `H_y(j) ≥ M_y(j)` for every `j ≥ 1` and every outcome;
* (T3) conditional hazard: at every operation `j` at which `y` has height at least `ℓ`, its
  height is at least `ℓ + 1` with probability at least `p` given `y`'s own trajectory cut off
  at `ℓ`;
* (T4) the trajectories of distinct items are independent;
* heights never decrease.

**Formalization Note** (T3) is stated for every horizon `N ≥ j` and every value `τ` of the
cut-off trajectory `(min(H_y(i), ℓ))_{1 ≤ i ≤ N}` with `τ_j = ℓ` (i.e. `H_y(j) ≥ ℓ`), in
multiplied form `P(cut = τ, H_y(j) ≥ ℓ+1) ≥ p · P(cut = τ)`, which is the conditional bound on
values of positive probability. (T2) needs no independence of the chains across items. The value
`H y 0` is never read (the height before the first operation is `1` by convention, p.5). -/
structure IsTRule (p : ℝ) (K : ℕ) {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : α → ℕ → Ω → ℕ) : Prop where
  /-- `P` is a probability measure -/
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- every height is a random variable -/
  measurable : ∀ y j, Measurable (H y j)
  /-- heights are integers `≥ 1` -/
  one_le : ∀ y j, 1 ≤ j → ∀ ω, 1 ≤ H y j ω
  /-- heights never decrease -/
  mono : ∀ y j, 1 ≤ j → ∀ ω, H y j ω ≤ H y (j + 1) ω
  /-- (T1) upper tail -/
  T1 : ∃ C : ℝ, ∀ y (j ℓ : ℕ), 1 ≤ j → 1 ≤ ℓ →
    P {ω | ℓ ≤ H y j ω} ≤ ENNReal.ofReal (C * j * p ^ ((ℓ : ℤ) - K))
  /-- (T2) Morris lower bound -/
  T2 : ∀ y, ∃ M : ℕ → Ω → ℕ, IsMorrisChain p P M ∧ ∀ j, 1 ≤ j → ∀ ω, M j ω ≤ H y j ω
  /-- (T3) conditional hazard given the item's own trajectory cut off at `ℓ` -/
  T3 : ∀ y (ℓ N j : ℕ), 1 ≤ ℓ → 1 ≤ j → j ≤ N → ∀ τ : ℕ → ℕ, τ j = ℓ →
    ENNReal.ofReal p * P {ω | ∀ i, 1 ≤ i → i ≤ N → min (H y i ω) ℓ = τ i} ≤
      P {ω | (∀ i, 1 ≤ i → i ≤ N → min (H y i ω) ℓ = τ i) ∧ ℓ + 1 ≤ H y j ω}
  /-- (T4) independence of the trajectories of distinct items -/
  T4 : iIndepFun (fun y ω => fun j => H y j ω) P

end SkipListConc.Supplement


