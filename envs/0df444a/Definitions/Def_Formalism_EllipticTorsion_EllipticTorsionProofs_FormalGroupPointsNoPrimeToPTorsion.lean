-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:57.1609+00:00
-- url     : https://prove2.me/theorems/c594a491-8827-4970-9ed7-f0835226f72a
-- title:
--   Formal Group Points No Prime To PTorsion
-- statement:
--   Definitions and structural lemmas for Formal Group Points No Prime To PTorsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}
def zf : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => x / y
end Formalism.ELL.FormalGroupPointsTorsion
namespace Formalism.ELL
open WeierstrassCurve
end Formalism.ELL


