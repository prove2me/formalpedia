-- Prove2me | Definitions.Def_SourceProof_f267311a53bb9d8d0cbfc95b
-- name    : SourceProof_f267311a53bb9d8d0cbfc95b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:40.362056+00:00
-- url     : https://prove2.me/theorems/c2ee5c5a-9687-5f23-8c5e-55db1e52800a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_neg

import Definitions.Def_SourceProof_2e6ca13dfe2fe5276b1d3986
import Definitions.Def_SourceProof_92f98353d1ecfc763009098e
import Definitions.Def_SourceProof_c128905347c476a8d319023c
import Definitions.Def_SourceProof_de08a420ec63708a2d73d894

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_f267311a53bb9d8d0cbfc95b (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    (_root_.Prove2MeSourceProof.h_c128905347c476a8d319023c hH).elementaryIntegral X = fun ω ↦ -hH.elementaryIntegral X ω := by
  have heq : (-H : ℝ≥0 → Ω → ℝ) = (-1 : ℝ) • H := by simp
  rw [(_root_.Prove2MeSourceProof.h_92f98353d1ecfc763009098e (_root_.Prove2MeSourceProof.h_c128905347c476a8d319023c hH)) ((_root_.Prove2MeSourceProof.h_2e6ca13dfe2fe5276b1d3986 hH) (-1)) heq X, (_root_.Prove2MeSourceProof.h_de08a420ec63708a2d73d894 hH)]
  funext ω
  ring
end IsSimplePredictable
end ProbabilityTheory


