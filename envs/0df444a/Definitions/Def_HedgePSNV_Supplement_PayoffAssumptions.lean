-- Prove2me | Definitions.Def_HedgePSNV_Supplement_PayoffAssumptions
-- name    : HedgePSNV_Supplement_PayoffAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:52:19.370115+00:00
-- url     : https://prove2.me/theorems/f2357a45-f31c-45de-9f03-6e3af99b766f
-- title:
--   Assumption EC.1 (concavity, monotonicity, supermodularity, increasing differences) and arg max over $q\ge0$
-- statement:
--   Let $H:\mathbb R^n\times\mathbb R^J\to\mathbb R$ be an operational payoff, $H(q,a)$, of a decision $q\ge0$ at a level $a$ of the stochastic operational factors; $\mathbb R^n$ and $\mathbb R^J$ carry the coordinatewise order, $\vee$ and $\wedge$ the coordinatewise maximum and minimum.
--
--   **Arg max over the orthant.** For $f:\mathbb R^n\to\mathbb R$, $\arg\max_{q\ge0}f=\{q\ge0: f(q')\le f(q)\ \forall q'\ge0\}$; the paper's $\min\arg\max$ ((EC.5.5), (EC.10.9)) is its least element.
--
--   **Increasing differences** (Assumption EC.1(iv)): for all $0\le q_1\le q_2$ and $a_1\le a_2$,
--   $$
--   H(q_1,a_2)-H(q_1,a_1)\le H(q_2,a_2)-H(q_2,a_1).
--   $$
--
--   **Assumption EC.1.** (i) for any $a$, $H(q,a)$ is concave in $q_i$ for all $i$ (each coordinate on $q_i\ge0$, the others fixed); (ii) for any $q\ge0$, $H(q,a)$ is increasing in $a_j$ for all $j$; (iii) for any $a$, $H(q,a)$ is supermodular in $q$: $H(q,a)+H(q',a)\le H(q\vee q',a)+H(q\wedge q',a)$ for $q,q'\ge0$; (iv) increasing differences.
--
--   These are the structural conditions under which Theorems EC.1, EC.3 and Lemmas EC.12–EC.13 compare operational decisions.
--
--   **Formalization Note** All conditions are on the orthant $q\ge0$ of feasible decisions (“Without loss of generality, we assume $q\ge0$”, p.ec14).
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Assumption EC.1, p.ec15; (EC.5.5), p.ec16

import Mathlib

open scoped NNReal

namespace HedgePSNV.Supplement

/-- The set of maximizers of `f` over the nonnegative orthant `{q ∈ ℝⁿ : q ≥ 0}`,
`arg max_{q ≥ 0} f(q)`, arXiv:2201.01026v4, (EC.5.5) p.ec16, (EC.10.9) p.ec63 and Theorem EC.3
p.ec62. The paper's `min arg max` ("the minimization takes effect entry-wise", p.ec16) is the
least element of this set in the coordinatewise order of `Fin n → ℝ`; statements take it as a
hypothesis `IsLeast (orthantArgmax f) q` instead of constructing it. -/
def orthantArgmax {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {q | 0 ≤ q ∧ ∀ q' : Fin n → ℝ, 0 ≤ q' → f q' ≤ f q}

/-- Increasing differences of an operational payoff `H(q, a)` in `(q, a)`, arXiv:2201.01026v4,
Assumption EC.1(iv), p.ec15: `H(q₁,a₂) − H(q₁,a₁) ≤ H(q₂,a₂) − H(q₂,a₁)` for all decisions
`0 ≤ q₁ ≤ q₂` and all factor levels `a₁ ≤ a₂` (coordinatewise orders on `ℝⁿ` and `ℝᴶ`).

**Formalization Note** Decisions range over `q ≥ 0` ("Without loss of generality, we assume
q ≥ 0", p.ec14); the factor levels `a` range over all of `ℝᴶ`. -/
def HasIncreasingDifferences {n J : ℕ} (H : (Fin n → ℝ) → (Fin J → ℝ) → ℝ) : Prop :=
  ∀ q₁ q₂ : Fin n → ℝ, ∀ a₁ a₂ : Fin J → ℝ, 0 ≤ q₁ → q₁ ≤ q₂ → a₁ ≤ a₂ →
    H q₁ a₂ - H q₁ a₁ ≤ H q₂ a₂ - H q₂ a₁

/-- Assumption EC.1, arXiv:2201.01026v4, p.ec15, on an operational payoff
`H : ℝⁿ × ℝᴶ → ℝ` (decisions `q ≥ 0`, stochastic operational factors `a`):
1. for any `a`, `H(q,a)` is concave in `qᵢ` for all `i` (each coordinate separately, the others
   fixed, over `qᵢ ≥ 0`);
2. for any `q`, `H(q,a)` is increasing in `aⱼ` for all `j` (equivalently, monotone in the
   coordinatewise order of `ℝᴶ`);
3. for any `a`, `H(q,a)` is supermodular in `q`:
   `H(q,a) + H(q',a) ≤ H(q ∨ q', a) + H(q ∧ q', a)` for `q, q' ≥ 0`;
4. `H(q,a)` has increasing differences in `(q,a)` (`HasIncreasingDifferences`).

**Formalization Note** All four parts are conditions on the orthant `q ≥ 0` of feasible
decisions (p.ec14). The lattice operations on `Fin n → ℝ` are coordinatewise. -/
def AssumptionEC1 {n J : ℕ} (H : (Fin n → ℝ) → (Fin J → ℝ) → ℝ) : Prop :=
  (∀ a : Fin J → ℝ, ∀ q : Fin n → ℝ, 0 ≤ q → ∀ i : Fin n,
      ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => H (Function.update q i t) a)) ∧
    (∀ q : Fin n → ℝ, 0 ≤ q → Monotone (H q)) ∧
    (∀ a : Fin J → ℝ, ∀ q q' : Fin n → ℝ, 0 ≤ q → 0 ≤ q' →
      H q a + H q' a ≤ H (q ⊔ q') a + H (q ⊓ q') a) ∧
    HasIncreasingDifferences H

end HedgePSNV.Supplement


