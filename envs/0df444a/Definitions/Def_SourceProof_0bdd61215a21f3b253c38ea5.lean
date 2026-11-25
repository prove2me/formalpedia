-- Prove2me | Definitions.Def_SourceProof_0bdd61215a21f3b253c38ea5
-- name    : SourceProof_0bdd61215a21f3b253c38ea5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:49.790783+00:00
-- url     : https://prove2.me/theorems/460e79d0-9d1d-4e1c-80c2-3df689f5f247
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isUIMartingale_min_const

import Definitions.Def_SourceProof_83eb039cc13d2afe8058ee05
import Definitions.Def_SourceProof_95717ff969660c2022f9fd24

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Martingales are locally uniformly integrable

Protter I.6 Example 1 and Klenke 21.69(i). Stopping at deterministic time T
closes the martingale with the terminal variable X_T. Thus it is UI even when
the original martingale is not UI over the whole half-line. No continuous-time
optional sampling or integrability of an unbounded stopping value is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_0bdd61215a21f3b253c38ea5
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T : ℝ≥0) :
    IsUIMartingale (fun t ↦ X (min t T)) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_95717ff969660c2022f9fd24 hX) T, ((hX.integrable T).uniformIntegrable_condExp F.le).ae_eq
    (fun t ↦ (_root_.Prove2MeSourceProof.h_83eb039cc13d2afe8058ee05 hX) T t)⟩
end ProbabilityTheory


