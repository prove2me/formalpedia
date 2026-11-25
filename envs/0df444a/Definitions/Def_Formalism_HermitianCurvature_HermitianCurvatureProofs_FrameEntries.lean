-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:59.460196+00:00
-- url     : https://prove2.me/theorems/b3f35359-44f7-4c13-a8fa-6fdd291473d1
-- title:
--   Frame Entries
-- statement:
--   Definitions and structural lemmas for Frame Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace FrameEntries
section Hom
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Hom
section Grp
variable {k r : ℕ}
end Grp
section Main
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Main
end FrameEntries
namespace FrameEntries
section Reg
variable {k r : ℕ}
def entL (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
end Reg
end FrameEntries
end Formalism.FourierDecayAlt.P


