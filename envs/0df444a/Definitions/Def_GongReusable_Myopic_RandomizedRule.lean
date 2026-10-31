-- Prove2me | Definitions.Def_GongReusable_Myopic_RandomizedRule
-- name    : GongReusable_Myopic_RandomizedRule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:22:49.803996+00:00
-- url     : https://prove2.me/theorems/97007fdc-8628-457a-be25-2f4342d402d6
-- title:
--   Measurable randomized decision rules
-- statement:
--   A randomized decision rule receives a fixed observed input i, an observed history h, and a fresh uniform seed u in [0,1], and produces an action. For every fixed i, the action is jointly measurable in (h,u). This general object imposes no optimization criterion, transition law or revenue bound. With a finite action space it represents all measurable probability kernels: sample the finitely many action probabilities by their cumulative sums. The rental policy specializes the input to the arrival index, current epoch and current customer's choice model, the history to past rentals, and the action to an assortment.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 5–6 / PDF pp. 5–6 (explicit measurability convention)

import Mathlib

open MeasureTheory

namespace GongReusable.Myopic

/-- A behavioral decision rule with a fixed observed input and an independent uniform seed.
For finite action spaces this represents probability kernels through inverse cumulative sampling. -/
structure RandomizedRule (I H A : Type) [MeasurableSpace H] [MeasurableSpace A] where
  act : I → H → ℝ → A
  measurable_act : ∀ i, Measurable (fun x : H × ℝ => act i x.1 x.2)

end GongReusable.Myopic


