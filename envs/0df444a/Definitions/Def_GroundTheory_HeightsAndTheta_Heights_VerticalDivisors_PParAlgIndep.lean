-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PParAlgIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PParAlgIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:29.743728+00:00
-- url     : https://prove2.me/theorems/38cc05ef-b41d-43c7-ab43-4b15550b5ddd
-- title:
--   PPar Alg Indep
-- statement:
--   Definitions and structural lemmas for PPar Alg Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PParAlgIndep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end GroundTheory.Heights₂.Heights.Vertical


