-- Prove2me | Definitions.Def_StaticCalendar_DemandModel
-- name    : StaticCalendar_DemandModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:14.643011+00:00
-- url     : https://prove2.me/theorems/a65f0cf0-d351-4150-bab5-28b0d0f12f2c
-- title:
--   The stationary assortment and pricing model
-- statement:
--   A firm sells $n\ge1$ items at $m\ge1$ positive prices $p_1,\dots,p_m$. A **product** is a pair $(i,j)$ of an item and a price index, and an **assortment** is a set of products. The feasible assortments form a family $\mathcal S$ that is downward closed and contains $\emptyset$.
--
--   For every feasible assortment $S$ the model gives a joint probability law $D_S$ of the demand vector $Q=(Q_{ij})$, the quantity of each product demanded in a period in which $S$ is shown. Almost surely under $D_S$:
--
--   1. every quantity lies in $[0,1]$;
--   2. a product outside $S$ has quantity $0$;
--   3. two products of one item are never demanded together, that is, for each item at most one quantity is positive.
--
--   Demand is stationary: the same family $(D_S)$ applies in every period. The expected quantity $q(i,j,S)=\mathbb E_{Q\sim D_S}[Q_{ij}]$ is part of the definition.
--
--   This covers single-purchase choice, multiple purchases and fractional consumption at once. The horizon and the inventories are not part of the model, since the paper's induction varies them.
--
--   **Formalization Note** Demand laws live on all of $\mathbb R^{[n]\times[m]}$ and vanish off $S$, rather than on $[0,1]^{|S|}$. Condition 3 is a condition on the law, as on p.12; an assortment may still list two prices of one item.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, §2.1, pp.9–10; §2.2, pp.12–13; footnotes 3–4, p.10; q(i,j,S), p.13

import Mathlib

open MeasureTheory

namespace StaticCalendar

/-- An assortment: a set of products `(i, j)` (item `i`, price index `j`). Ma, Simchi-Levi & Zhao,
Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, §2.1, pp.9–10.

**Formalization Note.** `Finset (Fin n × Fin m)` carries Mathlib's `Finset.instMeasurableSpace`,
which is discrete here because the product type is finite. -/
abbrev Assortment (n m : ℕ) := Finset (Fin n × Fin m)

/-- A demand vector: the quantity of each product demanded in one period. -/
abbrev Demand (n m : ℕ) := Fin n × Fin m → ℝ

/-- The stationary assortment and pricing model of arXiv:1811.01077v5, §2.1 and §2.2, pp.9–13:
`n` items, `m` positive prices `p j`, a downward-closed family `family` of assortments with
`∅ ∈ family` (p.10, footnotes 3–4), and for each assortment `S` a joint law `D S` of the quantities
demanded when `S` is shown.

The law is stationary: there is one `D`, the same in every period (pp.12–13). Quantities lie in
`[0,1]` (p.13), a product outside `S` has zero demand (p.10), and two products of one item are
never demanded together (p.12).

**Formalization Note.** `D S` lives on all of `Fin n × Fin m → ℝ` and vanishes off `S`, instead of
on `[0,1]^|S|`. Its properties are required for `S ∈ family` only; `D S` for `S ∉ family` is never
used. The clause `one_price` restricts the law, not the family, which is how p.12 words it.
Starting inventories and the horizon are not part of the model: they vary along the paper's backward
induction. -/
structure DemandModel (n m : ℕ) where
  /-- `n ∈ ℕ` is positive, p.9. -/
  n_pos : 0 < n
  /-- `m ∈ ℕ` is positive, p.9. -/
  m_pos : 0 < m
  /-- The prices `p₁,…,p_m`. -/
  p : Fin m → ℝ
  /-- Prices are positive, p.9. -/
  p_pos : ∀ j, 0 < p j
  /-- The family `𝒮` of feasible assortments. -/
  family : Finset (Assortment n m)
  /-- `∅ ∈ 𝒮`, p.10, footnote 4. -/
  empty_mem : ∅ ∈ family
  /-- `𝒮` is downward closed, p.10, footnote 3. -/
  down_closed : ∀ S ∈ family, ∀ S' : Assortment n m, S' ⊆ S → S' ∈ family
  /-- The joint demand law when assortment `S` is shown. -/
  D : Assortment n m → Measure (Demand n m)
  /-- `D S` is a probability measure for every feasible `S`. -/
  isProb : ∀ S ∈ family, IsProbabilityMeasure (D S)
  /-- Quantities lie in `[0,1]`, p.13. -/
  demand_mem : ∀ S ∈ family, ∀ᵐ Q ∂D S, ∀ ij, Q ij ∈ Set.Icc (0 : ℝ) 1
  /-- A product outside the assortment is not demanded, p.10. -/
  demand_off : ∀ S ∈ family, ∀ᵐ Q ∂D S, ∀ ij, ij ∉ S → Q ij = 0
  /-- The demand never contains two products of one item, p.12. -/
  one_price : ∀ S ∈ family, ∀ᵐ Q ∂D S, ∀ i j j', 0 < Q (i, j) → 0 < Q (i, j') → j = j'

/-- `q(i,j,S)`: the expected quantity of product `(i,j)` demanded when `S` is shown,
arXiv:1811.01077v5, p.13. -/
noncomputable def DemandModel.q {n m : ℕ} (I : DemandModel n m) (S : Assortment n m)
    (i : Fin n) (j : Fin m) : ℝ :=
  ∫ Q, Q (i, j) ∂I.D S

end StaticCalendar


