-- Prove2me | Definitions.Def_StaticCalendar_pC
-- name    : StaticCalendar_pC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:37.235193+00:00
-- url     : https://prove2.me/theorems/ca569d9c-7832-42b2-83d2-f2a4cc0251c1
-- title:
--   Virtual price $p_{\mathsf C,i}$
-- statement:
--   The revenue-weighted average price of item $i$ under $x$:
--
--   $$
--   p_{\mathsf C,i}=\frac{\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}p_j\,q(i,j,S)}{\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}q(i,j,S)}.
--   $$
--
--   **Formalization Note** The paper defines it only for items offered with positive probability. For an item with $\rho_i=0$ the value is $0$; the numerator also vanishes for feasible $x$, so such an item contributes nothing to any sum in which it appears.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, p.ec10

import Mathlib
import Definitions.Def_StaticCalendar_rho

namespace StaticCalendar

/-- The virtual price `p_{C,i}`, arXiv:1811.01077v5, p.ec10:
`Σ_{S∈𝒮} x(S) Σ_{j:(i,j)∈S} p_j q(i,j,S) / Σ_{S∈𝒮} x(S) Σ_{j:(i,j)∈S} q(i,j,S)`.

**Formalization Note.** The paper defines it only on items offered with positive probability.
When `ρᵢ = 0` Lean's value is `0`, which is harmless: for feasible `x` the numerator is `0` too, and
such an item contributes nothing to any revenue. -/
noncomputable def pC {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ) (i : Fin n) : ℝ :=
  (∑ S ∈ I.family, x S * ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ S), I.p j * I.q S i j) /
    rho I x i

end StaticCalendar


