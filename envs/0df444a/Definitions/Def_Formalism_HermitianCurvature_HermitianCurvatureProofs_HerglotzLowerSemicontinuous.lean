-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:48.61388+00:00
-- url     : https://prove2.me/theorems/33453065-7b40-4578-b6c8-395d74925bae
-- title:
--   Herglotz Lower Semicontinuous
-- statement:
--   Definitions and structural lemmas for Herglotz Lower Semicontinuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
noncomputable def tp (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : Fin d → ℝ) : ℂ :=
  ∑ σ ∈ B, c σ * ee y σ
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.Icc (fun _ => -(1 / 2)) (fun _ => 1 / 2)
noncomputable def pk (y : Fin d → ℝ) : ℝ := ∏ j, ‖1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))‖ ^ 2
end Formalism.FourierDecayAlt.P.HLsc
namespace Formalism.FourierDecayAlt.P
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.HLsc
end Formalism.FourierDecayAlt.P


