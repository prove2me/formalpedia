-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:59.609361+00:00
-- url     : https://prove2.me/theorems/1c24d0de-1d4d-469e-b860-26d2d61d4eea
-- title:
--   Level Nabla Star Relations
-- statement:
--   Definitions and structural lemmas for Level Nabla Star Relations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
noncomputable def nabE (a TT : ℝ) : Pr r := dzP + (a : ℂ) • (zbP * ggiP TT)
noncomputable def nabsE (a TT : ℝ) : Pr r := -dzbP + (a : ℂ) • (zP * ggiP TT)
theorem nabA_eq (P : Par) : nabA P = Matrix.diagonal fun π => nabE (aC P π) P.TT := rfl
theorem nabsA_eq (P : Par) : nabsA P = Matrix.diagonal fun π => nabsE (aC P π) P.TT := rfl
def ZF (f : Fn r) : Prop := ∀ l : Fin r, euler (vc l) f = 0 ∧ euler (vcb l) f = 0
def CF (f : Fn r) : Prop := euler vz f = 0 ∧ euler vzb f = 0
end Formalism.FourierDecayAlt.P.Mx2
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


