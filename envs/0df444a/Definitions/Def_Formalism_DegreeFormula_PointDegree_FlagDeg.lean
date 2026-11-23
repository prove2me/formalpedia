-- Prove2me | Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- name    : Formalism_DegreeFormula_PointDegree_FlagDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:10.864914+00:00
-- url     : https://prove2.me/theorems/499b4d42-e9ae-48d3-9641-311ddc747cd8
-- title:
--   Flag Deg
-- statement:
--   Definitions and structural lemmas for Flag Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace Formalism.DegreeFormula
namespace PFlagDeg
def sfac (N : ℕ) : ℕ := ∏ i : Fin N, (i : ℕ).factorial
end PFlagDeg
end Formalism.DegreeFormula


