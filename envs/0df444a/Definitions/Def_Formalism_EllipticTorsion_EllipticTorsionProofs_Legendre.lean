-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Legendre
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_Legendre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:46.281997+00:00
-- url     : https://prove2.me/theorems/c0159a74-42fb-4f1d-991d-4a0d77d6e68a
-- title:
--   Legendre
-- statement:
--   Definitions and structural lemmas for Legendre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Legendre.lean

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.ELL
namespace LegendreModelEllipticTorsion
open Polynomial
noncomputable def legPoly {K : Type*} [Field K] (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * (X * (X - 1)) ^ 2
end LegendreModelEllipticTorsion
end Formalism.ELL


