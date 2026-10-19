-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Setting
-- name    : OpaquePricing_Dominance_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:24.264853+00:00
-- url     : https://prove2.me/theorems/91c6f9fc-37cd-4a47-8acc-a09c5f6d9cf3
-- title:
--   Selling model, opaque valuations, and exchangeable two-value laws
-- statement:
--   A seller offers $N\ge 2$ items to a unit-demand customer. The customer buys an option with maximal nonnegative utility and pays the highest price among options tied for maximal utility. An opaque product is a nonempty set $S$ of items. Its value is either the minimum or the arithmetic mean of the item values in $S$; a singleton is an ordinary item. All items share one price in opaque selling, and opaque sets of the same size share one price.
--
--   For a valuation law $F$, let $R_{\mathrm{DP}}$ be the supremum of expected revenue over nonnegative item-price vectors. Let $R_{\mathrm{OPQ}}^\alpha$ be the supremum over nonnegative item and size prices when a customer is pessimistic with probability $\alpha$ and risk-neutral with probability $1-\alpha$, independently of valuations. Expectations and suprema take values in $[0,\infty]$. A law is exchangeable when every coordinate permutation preserves it. It is two-valued when almost every valuation vector has all coordinates in one common set $\{a,b\}$ with $a<b$.
--
--   These definitions give the common model used by the theorem and its supporting claims.
--
--   **Formalization Note** Items are indexed by \(\operatorname{Fin} N\), beginning at zero. Empty opaque sets are excluded from the offered menu. The helper values on an empty set do not affect revenue.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), §2–§2.3, pp. 8–13

import Mathlib

open MeasureTheory

namespace OpaquePricing.Dominance

/-- Revenue under the utility-maximizing choice rule, with the highest-price tie-break. -/
noncomputable def menuRevenue {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u price : ι → ℝ) : ℝ := by
  classical
  let winners := s.filter (fun o => 0 ≤ u o ∧ ∀ o' ∈ s, u o' ≤ u o)
  exact if h : winners.Nonempty then winners.sup' h price else 0

noncomputable def dpRevenue {N : ℕ} (p v : Fin N → ℝ) : ℝ :=
  menuRevenue Finset.univ (fun i => v i - p i) p

noncomputable def pessValue {N : ℕ} (v : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  if h : S.Nonempty then S.inf' h v else 0

noncomputable def rnValue {N : ℕ} (v : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  (∑ i ∈ S, v i) / S.card

def opqPrice {N : ℕ} (p : ℝ) (q : ℕ → ℝ) (S : Finset (Fin N)) : ℝ :=
  if S.card = 1 then p else q S.card

def opqOptions (N : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter Finset.Nonempty

noncomputable def opqRevenue {N : ℕ}
    (val : (Fin N → ℝ) → Finset (Fin N) → ℝ)
    (p : ℝ) (q : ℕ → ℝ) (v : Fin N → ℝ) : ℝ :=
  menuRevenue (opqOptions N)
    (fun S => val v S - opqPrice p q S) (opqPrice p q)

noncomputable def expDP {N : ℕ} (μ : Measure (Fin N → ℝ))
    (p : Fin N → ℝ) : ENNReal :=
  ∫⁻ v, ENNReal.ofReal (dpRevenue p v) ∂μ

noncomputable def expOPQ {N : ℕ} (μ : Measure (Fin N → ℝ))
    (α p : ℝ) (q : ℕ → ℝ) : ENNReal :=
  ENNReal.ofReal α * (∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ) +
  ENNReal.ofReal (1 - α) * (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ)

noncomputable def optDP {N : ℕ} (μ : Measure (Fin N → ℝ)) : ENNReal :=
  ⨆ (p : Fin N → ℝ) (_ : ∀ i, 0 ≤ p i), expDP μ p

noncomputable def optOPQ {N : ℕ} (μ : Measure (Fin N → ℝ))
    (α : ℝ) : ENNReal :=
  ⨆ (p : ℝ) (q : ℕ → ℝ) (_ : 0 ≤ p ∧ ∀ k, 0 ≤ q k), expOPQ μ α p q

def Exchangeable {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), μ.map (fun v => v ∘ σ) = μ

def TwoValued {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∃ a b : ℝ, a < b ∧ ∀ᵐ v ∂μ, ∀ i, v i = a ∨ v i = b

/-- The (k+1)-st largest coordinate, preserving repeated values. -/
noncomputable def orderStat {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ := by
  classical
  exact (((Finset.univ : Finset (Fin N)).toList.map v).mergeSort (fun a b => b ≤ a)).getD k 0

def sortedEvent {N : ℕ} (σ : Equiv.Perm (Fin N)) : Set (Fin N → ℝ) :=
  {v | ∀ i j, i ≤ j → v (σ j) ≤ v (σ i)}

noncomputable def highCount {N : ℕ} (b : ℝ) (v : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => v i = b)).card

def mixedPrice {N : ℕ} (a b : ℝ) : Fin N → ℝ :=
  if h : 0 < N then Function.update (fun _ => b) ⟨0, h⟩ a else fun _ => b

noncomputable def ladder (N : ℕ) (a b : ℝ) (k : ℕ) : ℝ :=
  a + (((N : ℝ) - k) / N) * (b - a)

end OpaquePricing.Dominance


