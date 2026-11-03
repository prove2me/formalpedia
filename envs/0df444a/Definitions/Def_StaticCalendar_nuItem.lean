-- Prove2me | Definitions.Def_StaticCalendar_nuItem
-- name    : StaticCalendar_nuItem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:52.351407+00:00
-- url     : https://prove2.me/theorems/16610c30-610c-48d7-9b0b-6dbf29ff8e0a
-- title:
--   Mixture law of an item's demand
-- statement:
--   The law of the quantity of item $i$ demanded in one period of Algorithm 1: draw the assortment and the demand, and sum the quantities of the products of $i$ in the assortment. This is the variable $Q_i$ of (EC.7) and the demand law of the virtual calendar. Its mean is $\rho_i$, and it is supported on $[0,1]$.
--
--   **Formalization Note** The printed CDF $\sum_S x(S)\sum_j F_{(i,j,S)}$ omits the atom at $0$ coming from the assortments that do not contain $i$. The law of (EC.7) is the intended object.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, (EC.7), p.ec13; F(i,p_C,i,S_C), p.ec10

import Mathlib
import Definitions.Def_StaticCalendar_pathRev
import Definitions.Def_StaticCalendar_period

open MeasureTheory

namespace StaticCalendar

/-- The mixture law of item `i`'s per-period demand under Algorithm 1: the law of `Qᵢ` in (EC.7),
arXiv:1811.01077v5, p.ec13, which is the CDF `F(i,p_{C,i},S_C)` of the virtual calendar, p.ec10.

**Formalization Note.** The push-forward of the one-period law under `itemDemand i`. The printed
CDF `Σ_S x(S) Σ_j F(i,j,S)` omits the atom at `0` of the periods in which item `i` is not offered and
sums to less than `1` when an assortment omits `i`; the law of (EC.7) is the intended object.
`itemDemand i` is measurable because assortments are discrete. -/
noncomputable def nuItem {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ) (i : Fin n) :
    Measure ℝ :=
  (period I x).map (itemDemand i)

end StaticCalendar


