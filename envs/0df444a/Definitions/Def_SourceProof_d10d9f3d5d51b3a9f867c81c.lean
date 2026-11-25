-- Prove2me | Definitions.Def_SourceProof_d10d9f3d5d51b3a9f867c81c
-- name    : SourceProof_d10d9f3d5d51b3a9f867c81c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:32.708626+00:00
-- url     : https://prove2.me/theorems/d9891b37-de16-5cbf-866b-979f55c9f165
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isLocalMartingale

import Definitions.Def_SourceProof_1a1f53b6ab20a545868ab216
import Definitions.Def_SourceProof_4975513a3ada74dcc663cdcd

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

theorem _root_.Prove2MeSourceProof.h_d10d9f3d5d51b3a9f867c81c
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P)
    (hcad : HasCadlagPaths X P) : IsLocalMartingale X F P :=
  (_root_.Prove2MeSourceProof.h_4975513a3ada74dcc663cdcd (_root_.Prove2MeSourceProof.h_1a1f53b6ab20a545868ab216 hX)) hX.stronglyAdapted.adapted hcad
end ProbabilityTheory


