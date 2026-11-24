-- Prove2me | Definitions.Def_TwoSidedMatching_Statics_Supplement_Deviation
-- name    : TwoSidedMatching_Statics_Supplement_Deviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:04:23.639479+00:00
-- url     : https://prove2.me/theorems/65a93d33-0499-4e80-ad92-005df9e7e321
-- title:
--   Main text pp. 9–13 — tagged requests, FCFS outcomes and touching-support market
-- statement:
--   A tagged agent chooses a stopping time and whether to request; all opponents follow the source's arrival-time threshold rules. An accepted tagged request is inserted by its request time into the existing FCFS streams. A match departs at the later of the two request times and pays the posted price at the tagged request time. An accepted request without a match departs at $T$, and rejection departs at the stopping time. Utilities include the entire wait from arrival $t$:
--
--   $$U^d=vm-p-b(s-t),\qquad U^s=p-cm-h(s-t).$$
--
--   The file also constructs the concrete regular market with unit densities on buyer support $[0,1]$ and seller support $[1,2]$. It supports the counterexample to Theorem 1, where only constant arrival-time actions are needed; those actions are measurable under both of the paper's information structures.
--
--   **Formalization Note** The existing published Poisson-count-plus-i.i.d.-marks law and compensation kernels are reused. Null simultaneous requests are ordered by index. No class of arbitrary adapted deviations or general best-response theorem is asserted here. The utilities for the two constant counterexample actions are their actual source utilities; no payoff inequality defines feasibility.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 9–13, buyer and seller outcomes and utilities; pp. 17–19, greedy matching and waiting adjusted FP policy

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.Statics.Supplement

/-- A tagged agent's stopping time and request decision, represented as random variables.
Constant arrival-time acceptance and rejection are admissible under either source filtration. -/
structure TaggedAction where
  stop : TwoSidedMatching.Guarantee.Ω → ℝ
  request : TwoSidedMatching.Guarantee.Ω → Bool

/-- Arrival-time stopping, including threshold ties as acceptance. -/
def immediate (t : ℝ) (accept : Bool) : TaggedAction :=
  ⟨fun _ => t, fun _ => accept⟩

/-- The tagged buyer is inserted in request order. Opponents remain all-myopic.
The tagged request is placed before a simultaneous opponent request (a null tie). -/
noncomputable def buyerMatch (E : TwoSidedMatching.Guarantee.Environment)
    (lamD lamS T : ℝ) (a : TaggedAction) (ω : TwoSidedMatching.Guarantee.Ω) :
    Option (Fin ω.2.1) :=
  if a.request ω then
    (TwoSidedMatching.Guarantee.sortedS E lamD lamS T ω)[
      TwoSidedMatching.Guarantee.taggedBuyerRank E lamD lamS T ω (a.stop ω)]?
  else none

noncomputable def sellerMatch (E : TwoSidedMatching.Guarantee.Environment)
    (lamD lamS T : ℝ) (a : TaggedAction) (ω : TwoSidedMatching.Guarantee.Ω) :
    Option (Fin ω.1.1) :=
  if a.request ω then
    (TwoSidedMatching.Guarantee.sortedB E lamD lamS T ω)[
      TwoSidedMatching.Guarantee.taggedSellerRank E lamD lamS T ω (a.stop ω)]?
  else none

/-- Payment only upon a match; waiting starts at arrival, including any wait before request.
If a request never matches, departure is T; rejection departs at the stopping time. -/
noncomputable def buyerUtility (E : TwoSidedMatching.Guarantee.Environment)
    (lamD lamS T b t v : ℝ) (a : TaggedAction) (ω : TwoSidedMatching.Guarantee.Ω) : ℝ :=
  match buyerMatch E lamD lamS T a ω with
  | some j => v - TwoSidedMatching.Guarantee.askPrice E lamD lamS T b ω (a.stop ω) -
      b * (max (a.stop ω) (TwoSidedMatching.Guarantee.sellerTime ω j) - t)
  | none => -b * ((if a.request ω then T else a.stop ω) - t)

noncomputable def sellerUtility (E : TwoSidedMatching.Guarantee.Environment)
    (lamD lamS T h t c : ℝ) (a : TaggedAction) (ω : TwoSidedMatching.Guarantee.Ω) : ℝ :=
  match sellerMatch E lamD lamS T a ω with
  | some i => TwoSidedMatching.Guarantee.bidPrice E lamD lamS T h (a.stop ω) - c -
      h * (max (a.stop ω) (TwoSidedMatching.Guarantee.buyerTime ω i) - t)
  | none => -h * ((if a.request ω then T else a.stop ω) - t)

/-- Counterexample: continuous unit densities on touching supports [0,1] and [1,2]. -/
noncomputable def touchingMarket : TwoSidedMatching.Guarantee.Environment where
  loB := 0
  hiB := 1
  loS := 1
  hiS := 2
  fB := fun _ => 1
  fS := fun _ => 1
  loB_lt_hiB := by norm_num
  loS_lt_hiS := by norm_num
  fB_measurable := measurable_const
  fS_measurable := measurable_const
  fB_pos := by intros; norm_num
  fS_pos := by intros; norm_num
  fB_intervalIntegrable := intervalIntegrable_const
  fS_intervalIntegrable := intervalIntegrable_const
  fB_integral := by simp
  fS_integral := by norm_num

end TwoSidedMatching.Statics.Supplement


