-- Prove2me | Definitions.Def_PrefDeals_optRevenue
-- name    : PrefDeals_optRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:38.874689+00:00
-- url     : https://prove2.me/theorems/c2540cb1-def9-445a-a9af-b89ad473e4f3
-- title:
--   Optimal revenue of a sequence of preferred deals
-- statement:
--   The **optimal revenue** is
--
--   $$
--   \mathrm{OPT}=\sup\{\mathrm{Rev}(\mathit{seq}) : \mathit{seq}\text{ an admissible priority sequence of deals}\},
--   $$
--
--   the largest expected per-impression revenue a seller can obtain with a sequence of preferred deals when buyers behave as in §2.
--
--   Theorem 2 compares the Auction-Adjusted Greedy revenue with this quantity.
--
--   **Formalization Note** The set is nonempty and bounded above by $\mathrm E[\max_i v_i]$ (a milestone of this mission), so the real supremum is the true one. The paper's recursion $\omega(\mathcal I,S)$ of (1) ranges over surplus-extracting deals, all of which are admissible here; this supremum is at least $\omega$, so a guarantee relative to it is at least as strong.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §3, p.9 (optimal sequence of preferred deals) and Theorem 2, p.12 (optimal revenue)

import Mathlib
import Definitions.Def_PrefDeals_dealRevenue
import Definitions.Def_PrefDeals_IsPrioritySequence

open MeasureTheory

namespace PrefDeals

/-- **The optimal revenue of a sequence of preferred deals.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §3, p.9 ("the problem of finding the
optimal (i.e., revenue-maximizing) sequence of preferred deals") and Theorem 2, p.12 ("at least a
third of the optimal revenue").

`optRevenue M = sup { dealRevenue M seq : seq an admissible priority sequence }`: the largest
expected per-impression revenue any priority sequence of deals earns under the buyers' behaviour
of §2 (`boughtSet`).

**Formalization Note.** The supremum is the real `sSup`. The set is nonempty (the empty list earns
`0`) and bounded above by `E[maxⱼ vⱼ]` (the benchmark of p.12, a milestone of this mission), so the
`sSup` is the true supremum. The paper's recursion `ω(𝓘, S)` of (1), p.10, ranges over
surplus-extracting deals; every such sequence is admissible here, so this supremum is at least the
paper's. -/
noncomputable def optRevenue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) : ℝ :=
  sSup (dealRevenue M '' {seq | IsPrioritySequence seq})

end PrefDeals


