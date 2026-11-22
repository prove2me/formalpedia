-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_StatementE
-- name    : Formalism_MahlerMeasure_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:42.990907+00:00
-- url     : https://prove2.me/theorems/ade2f39d-5921-4f7c-ac1d-ffbd8347d3b7
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/StatementE.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
def SmithBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K),
    (∀ i j, ‖M i j‖ ≤ 1) →
    ∃ (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖U i j‖ ≤ 1) ∧ (∀ i j, ‖V i j‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
      M = U * Matrix.diagonal d * V
end Formalism.GM


