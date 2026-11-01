-- Prove2me | Definitions.Def_PrefDeals_vmax
-- name    : PrefDeals_vmax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:39.728928+00:00
-- url     : https://prove2.me/theorems/9b7d139a-dec6-4805-a051-ea44064eaeaf
-- title:
--   Highest valuation $v_{(1)}(T)$ among a set of buyers
-- statement:
--   For a set of buyers $T$ and an impression $\omega$,
--
--   $$
--   v_{(1)}(T)(\omega)=\max_{k\in T} v_k(\omega)
--   $$
--
--   is the highest valuation among the buyers in $T$. The benchmark of the paper is $\mathrm E[v_{(1)}(\text{all buyers})]=\mathrm E[\max_i v_i]$, the expected revenue of selling every impression to its highest-value buyer at that buyer's value.
--
--   **Formalization Note** For the empty set, $v_{(1)}(\emptyset)=0$; the paper never evaluates this case.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Figure 1, p.11, and p.12 ("where $v_{(1)}(S_1)=\max_{i\in S_1}\{v_i\}$")

import Mathlib
import Definitions.Def_PrefDeals_ValuationModel

open MeasureTheory

namespace PrefDeals

/-- **The highest valuation `v₍₁₎(T)` among a set of buyers.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Figure 1, p.11, and p.12:
"where `v₍₁₎(S₁) = max_{i∈S₁} {vᵢ}`".

`vmax M T ω = max_{k ∈ T} v_k(ω)` for a nonempty set of buyers `T`.

**Formalization Note.** The paper never evaluates `v₍₁₎(∅)`; here `vmax M ∅ = 0`, which is the
revenue an empty set of buyers can generate. -/
noncomputable def vmax {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (T : Finset (Fin n)) (ω : Ω) : ℝ :=
  if h : T.Nonempty then T.sup' h (fun k => M.v k ω) else 0

end PrefDeals


