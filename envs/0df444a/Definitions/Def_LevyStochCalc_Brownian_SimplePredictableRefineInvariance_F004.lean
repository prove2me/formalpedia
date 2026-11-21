-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F004
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:11:47.421064+00:00
-- url     : https://prove2.me/theorems/f593d641-e6b5-4c63-b9ba-51bb607448be
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineInvariance
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineInvariance. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F000
import Definitions.Def_SourceProof_8e16a5db202937f7386898ce
import Definitions.Def_SourceProof_ee0e53cddc38a360e7874cbc

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **General-time `refine` invariance of `simpleIntegral`.** The `min (·) t`
clamped analogue of `simpleIntegral_refine`: refining the partition leaves
`simpleIntegral W · t` unchanged at *every* time `t`, not just at the endpoint.
Uses the clamped fiber telescope. -/
lemma SimplePredictable.simpleIntegral_refine_intermediate
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (t : ℝ) (ω : Ω) :
    simpleIntegral W (H.refine M π' h_zero h_last h_strictMono idxMap h_idx_le h_idx_ge) t ω
      = simpleIntegral W H t ω := by
  unfold simpleIntegral
  change (∑ j : Fin M, H.ξ (idxMap j) ω
        * (W.W (min (π' j.succ) t) ω - W.W (min (π' j.castSucc) t) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
  rw [← Finset.sum_fiberwise_of_maps_to (g := idxMap)
      (fun (j : Fin M) (_ : j ∈ (Finset.univ : Finset (Fin M))) => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_8e16a5db202937f7386898ce p2mMethodArg0 H) W h_strictMono h_idx_le h_idx_ge h_refines i ω t
/-- **C0b.3: `refine` preserves `simpleIntegral` (pointwise).** Under
the hypothesis that `π'` refines `H.partition` (every `H.partition i`
is some `π' k`), the simple integral evaluated at time `T` is unchanged
by refining.

Assembly:
* `simpleIntegral_eq_sum` reduces both sides to plain sums (no
  `min ... T` clauses, since `H.partition_le_T`).
* `Finset.sum_fiberwise_of_maps_to` groups the LHS by `idxMap j = i`.
* For each `i`, `fiber_sum_telescope` collapses the fiber sum to
  `H.ξ i ω · (W (H.partition i.succ) ω - W (H.partition i.castSucc) ω)`,
  which is the `i`-th term of the RHS. -/
lemma SimplePredictable.simpleIntegral_refine
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (ω : Ω) :
    simpleIntegral W (H.refine M π' h_zero h_last h_strictMono idxMap h_idx_le h_idx_ge) T ω
      = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum, simpleIntegral_eq_sum]
  change (∑ j : Fin M, H.ξ (idxMap j) ω
        * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)
  rw [← Finset.sum_fiberwise_of_maps_to (g := idxMap)
      (fun (j : Fin M) (_ : j ∈ (Finset.univ : Finset (Fin M))) => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_ee0e53cddc38a360e7874cbc p2mMethodArg0 H) W h_strictMono h_idx_le h_idx_ge h_refines i ω
end LevyStochCalc.Brownian.Ito


