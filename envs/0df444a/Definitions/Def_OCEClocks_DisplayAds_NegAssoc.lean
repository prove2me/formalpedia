-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_NegAssoc
-- name    : OCEClocks_DisplayAds_NegAssoc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:20:43.53774+00:00
-- url     : https://prove2.me/theorems/45deb94a-286a-4ced-91b1-2a7110d61534
-- title:
--   Negative association of random variables with values in an ordered space (Definition 1)
-- statement:
--   Let $(\Omega,P)$ be a probability space, $K$ an index set and $X=(X_k)_{k\in K}$ a family of random variables with values in an ordered measurable space $\beta$; the paper's clocks take values in $[0,\infty]=\mathbb R_+\cup\{\infty\}$ and its first ages in $\mathbb R$. For $A\subseteq K$ write $X_A=(X_k)_{k\in A}$. The family is **negatively associated** if for all finite disjoint $A,B\subseteq K$ and all bounded measurable functions $f$ of $X_A$ and $g$ of $X_B$ that are both nondecreasing in each coordinate or both nonincreasing in each coordinate,
--
--   $$\mathbb E\big[f(X_A)\,g(X_B)\big]\ \le\ \mathbb E\big[f(X_A)\big]\,\mathbb E\big[g(X_B)\big].\qquad(1)$$
--
--   Negative association is the correlation notion of the paper: an OCEC generator must return negatively associated clocks, and Lemma 8 shows that the first ages of disjoint intervals of a Poisson process are negatively associated.
--
--   **Formalization Note** `NegAssoc P X` takes `X : K → Ω → β` for any preordered measurable `β` (used with `ℝ≥0∞` and `ℝ`), so the value $\infty$ is allowed, unlike the platform's real-valued definitions. Each $X_k$ is required to be measurable. The test functions are maps `(A → β) → ℝ` that are measurable for the product σ-algebra (the Borel σ-algebra of the finite product for these second-countable value spaces), bounded, and `Monotone`/`Antitone` for the coordinatewise order. The paper's $K$ is countable; the definition only looks at finite subsets of $K$, and every use in this mission has a finite $K$.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 5, Definition 1, eq. (1)

import Mathlib

open MeasureTheory

namespace OCEClocks.DisplayAds

/-!
# Negative association (Definition 1)

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), p. 5, Definition 1.

A family `X = (X_k)_{k ∈ K}` of random variables on a probability space `(Ω, P)` with values in
an ordered measurable space `β` (used with `β = ℝ≥0∞ = [0, ∞]` for clocks and `β = ℝ` for ages)
is negatively associated when, for all finite disjoint index sets `A, B ⊆ K` and all bounded
measurable `f, g` that are both coordinatewise nondecreasing or both coordinatewise
nonincreasing, `E[f(X_A) g(X_B)] ≤ E[f(X_A)] E[g(X_B)]` (eq. (1)).
-/

/-- Negative association of the family `X = (X_k)_{k ∈ K}` under `P` (Definition 1, p. 5).
Every `X k` is a random variable (measurable). For all finite disjoint `A, B ⊆ K` and all bounded
measurable test functions `f` of `X_A = (X_k)_{k ∈ A}` and `g` of `X_B`, both monotone
(nondecreasing in every coordinate) or both antitone (nonincreasing in every coordinate),
`E[f(X_A) g(X_B)] ≤ E[f(X_A)] E[g(X_B)]`. The order on `A → β` is the coordinatewise order, so
`Monotone f` is "nondecreasing in each coordinate". -/
def NegAssoc {Ω K β : Type*} [MeasurableSpace Ω] [Preorder β] [MeasurableSpace β]
    (P : Measure Ω) (X : K → Ω → β) : Prop :=
  (∀ k, Measurable (X k)) ∧
  ∀ A B : Finset K, Disjoint A B →
    ∀ (f : (A → β) → ℝ) (g : (B → β) → ℝ),
      Measurable f → Measurable g →
      (∃ C : ℝ, ∀ y, |f y| ≤ C) → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
      ((Monotone f ∧ Monotone g) ∨ (Antitone f ∧ Antitone g)) →
      ∫ ω, f (fun k => X k ω) * g (fun k => X k ω) ∂P ≤
        (∫ ω, f (fun k => X k ω) ∂P) * ∫ ω, g (fun k => X k ω) ∂P

end OCEClocks.DisplayAds


