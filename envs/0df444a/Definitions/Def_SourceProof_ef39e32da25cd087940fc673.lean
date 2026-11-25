-- Prove2me | Definitions.Def_SourceProof_ef39e32da25cd087940fc673
-- name    : SourceProof_ef39e32da25cd087940fc673
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:42.675306+00:00
-- url     : https://prove2.me/theorems/43a8a7a0-72c5-49cc-8ed5-a2c1c56b68e0
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.sum

import Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
import Definitions.Def_SourceProof_c55d17120c217e6f4e472165

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite sums in the existing real UCP topology -/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_ef39e32da25cd087940fc673 {Ω α κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {l : Filter α} (s : Finset κ)
    {X : κ → α → ℝ≥0 → Ω → ℝ} {Y : κ → ℝ≥0 → Ω → ℝ}
    (h : ∀ k ∈ s, TendstoUCP P (X k) l (Y k)) :
    TendstoUCP P (fun n ↦ ∑ k ∈ s, X k n) l (∑ k ∈ s, Y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty] using _root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 l (0 : ℝ≥0 → Ω → ℝ)
  | @insert k s hk ih =>
    simp only [sum_insert hk]
    exact (_root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 (h k (mem_insert_self _ _))) (ih (fun j hj ↦ h j (mem_insert_of_mem hj)))
end TendstoUCP

end ProbabilityTheory


