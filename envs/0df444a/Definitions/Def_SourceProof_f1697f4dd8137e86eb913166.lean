-- Prove2me | Definitions.Def_SourceProof_f1697f4dd8137e86eb913166
-- name    : SourceProof_f1697f4dd8137e86eb913166
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:59.741843+00:00
-- url     : https://prove2.me/theorems/b8439684-1c81-5352-a3b5-a157469f7fab
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.represents_finiteJumpLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F012
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F021
import Definitions.Def_SourceProof_14aaba468c338b75c22998f2
import Definitions.Def_SourceProof_442eedb3cbc1d65319ef7cc0
import Definitions.Def_SourceProof_e7578178dcf5fa404cb3a96e
import Definitions.Def_SourceProof_f37d4d80988d84677202c555

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet


theorem _root_.Prove2MeSourceProof.h_f1697f4dd8137e86eb913166 (η : LevyTriplet) [IsFiniteMeasure η.jumpMeasure] :
    η.Represents η.finiteJumpLaw := by
  let νf : FiniteMeasure ℝ := ⟨η.jumpMeasure, inferInstance⟩
  have hzero : (νf : Measure ℝ) {0} = 0 := η.isLevyMeasure_jumpMeasure.1
  have hdet := _root_.Prove2MeSourceProof.h_14aaba468c338b75c22998f2
    (η.drift - ∫ x, ProbabilityTheory.levyTruncation x ∂η.jumpMeasure)
  have hgauss := _root_.Prove2MeSourceProof.h_442eedb3cbc1d65319ef7cc0 0 η.gaussianVariance
  have hjump := _root_.Prove2MeSourceProof.h_e7578178dcf5fa404cb3a96e νf hzero
  have hsum := (_root_.Prove2MeSourceProof.h_f37d4d80988d84677202c555 ((_root_.Prove2MeSourceProof.h_f37d4d80988d84677202c555 hdet) hgauss)) hjump
  have htriplet :
      ((ProbabilityTheory.LevyTriplet.pointMass (η.drift - ∫ x, ProbabilityTheory.levyTruncation x ∂η.jumpMeasure)).add
          (ProbabilityTheory.LevyTriplet.gaussian 0 η.gaussianVariance)).add
            (ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure νf hzero) = η := by
    rw [LevyTriplet.mk.injEq]
    simp [ProbabilityTheory.LevyTriplet.add, ProbabilityTheory.LevyTriplet.pointMass, ProbabilityTheory.LevyTriplet.gaussian,
      ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure, νf]
  rw [htriplet] at hsum
  change η.Represents
    (MeasureTheory.ProbabilityMeasure.conv
      (MeasureTheory.ProbabilityMeasure.conv
        (MeasureTheory.ProbabilityMeasure.pointMass
          (η.drift - ∫ x, ProbabilityTheory.levyTruncation x ∂η.jumpMeasure))
        (ProbabilityTheory.LevyTriplet.gaussianLaw 0 η.gaussianVariance))
      (ProbabilityTheory.CompoundPoisson.ofFiniteMeasure νf))
  exact hsum
end LevyTriplet

end ProbabilityTheory


