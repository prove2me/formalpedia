-- Prove2me | Definitions.Def_SourceProof_aa05bbbbd7a39bd6fd18d38a
-- name    : SourceProof_aa05bbbbd7a39bd6fd18d38a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:43:18.683835+00:00
-- url     : https://prove2.me/theorems/2100564f-0c8c-4bc5-8a51-ee68beb9cefb
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_sq_integral_min_const_le_of_coefficients

import Definitions.Def_SourceProof_1cb0c9fe6028b1c6a5abe505
import Definitions.Def_SourceProof_2113cbfa026fcf89ba3d35af
import Definitions.Def_SourceProof_29c5ae821e5120b570769687
import Definitions.Def_SourceProof_2e30df4bf39f89baaefd8aab
import Definitions.Def_SourceProof_4f959de634195da08dfdbf83
import Definitions.Def_SourceProof_51cff7b6f18c4ccd4d6713f8
import Definitions.Def_SourceProof_7dbceac91c975186454d86e6
import Definitions.Def_SourceProof_9a05df2506f159e4ed7b785f
import Definitions.Def_SourceProof_9d0c3e934cbd4c316503217d
import Definitions.Def_SourceProof_d36deae29721c35a59f8058d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary-integral L2 estimate

For a martingale stopped at a finite deterministic horizon `T`, a uniform process bound `C`
on a simple predictable integrand gives `E[(H · X^T)^2] ≤ C^2 E[X_T^2]`. The source initial
term is retained, random endpoints are not bounded deterministically, and coefficients on
empty intervals are normalized before applying the discrete martingale estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_aa05bbbbd7a39bd6fd18d38a (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hinit : ∀ ω, ‖H.initial ω‖ ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) :
    ∫ ω, (H.integral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P := by
  let M := H.partition.sampledProcess (fun t ↦ X (min t T))
  have hM : Martingale M H.partition.sampledFiltration P :=
    (_root_.Prove2MeSourceProof.h_7dbceac91c975186454d86e6 H.partition) hX hF hr T
  have hlp : ∀ n, MemLp (M n) 2 P :=
    (_root_.Prove2MeSourceProof.h_9a05df2506f159e4ed7b785f H.partition) hX hF hr T (by norm_num) hXT
  let Z : Ω → ℝ := fun ω ↦ H.initial ω * M 0 ω
  have hZ : StronglyMeasurable[H.partition.sampledFiltration 0] Z :=
    (H.measurable_initial.mono ((_root_.Prove2MeSourceProof.h_2e30df4bf39f89baaefd8aab H.partition) 0) le_rfl).stronglyMeasurable.mul
      (hM.stronglyMeasurable 0)
  have htop : MemLp H.initial ∞ P := memLp_top_of_bound
    (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable C (ae_of_all _ hinit)
  have hZlp : MemLp Z 2 P := (hlp 0).mul' htop
  have hZb : ∀ᵐ ω ∂P, (Z ω) ^ 2 ≤ (C : ℝ) ^ 2 * (M 0 ω) ^ 2 := by
    apply ae_of_all
    intro ω
    dsimp only [Z]
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (H.initial ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hinit ω) 2
  have hi := (_root_.Prove2MeSourceProof.h_9d0c3e934cbd4c316503217d hM) hlp
    (_root_.Prove2MeSourceProof.h_d36deae29721c35a59f8058d H) C
    (fun n ↦ ae_of_all _ ((_root_.Prove2MeSourceProof.h_51cff7b6f18c4ccd4d6713f8 H) C.coe_nonneg hb n)) hZ hZlp hZb
    H.partition.size
  have hterminal : (∫ ω, (M H.partition.size ω) ^ 2 ∂P) ≤ ∫ ω, (X T ω) ^ 2 ∂P := by
    apply _root_.Prove2MeSourceProof.h_1cb0c9fe6028b1c6a5abe505 (hlp _) hXT
    exact (_root_.Prove2MeSourceProof.h_4f959de634195da08dfdbf83 hX) hF hr (H.partition.pointNat H.partition.size)
      T (by norm_num)
  have hrewrite : H.integral (fun t ↦ X (min t T)) = fun ω ↦ Z ω +
      MeasureTheory.discreteStochasticIntegral H.discreteCoefficient M H.partition.size ω := by
    rw [(_root_.Prove2MeSourceProof.h_2113cbfa026fcf89ba3d35af H)]
    simp only [Z, M, _root_.Prove2MeSourceProof.h_29c5ae821e5120b570769687, zero_min]
  rw [hrewrite]
  exact hi.trans (mul_le_mul_of_nonneg_left hterminal (sq_nonneg _))
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


