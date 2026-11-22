-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:09.937413+00:00
-- url     : https://prove2.me/theorems/74451b6b-81ef-4eea-b792-e80bb24d752e
-- title:
--   Smith Ball
-- statement:
--   Definitions and structural lemmas for Smith Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SmithBall.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
namespace SmithNormalFormAlt
open Matrix
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def Dec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) : Prop :=
  ∃ (U V : Matrix ι ι K) (d : ι → K),
      (∀ i j, ‖U i j‖ ≤ 1) ∧ (∀ i j, ‖V i j‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
      M = U * Matrix.diagonal d * V
end SmithNormalFormAlt
end Formalism.GM


