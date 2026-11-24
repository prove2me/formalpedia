-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:11.603337+00:00
-- url     : https://prove2.me/theorems/dd870803-02ff-4cec-b8a3-dd48f58a0f75
-- title:
--   Inhabitants
-- statement:
--   Definitions and structural lemmas for Inhabitants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/Inhabitants.lean

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
abbrev pointPar : Par 0 1 → FractionRing (MvPolynomial (Par 0 1) ℚ) :=
  fun p => algebraMap (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ)) (X p)
abbrev pointForm : MvPolynomial (Fin (0 + 1) × Fin 1) (𝓞 ℚ) := X (0, 0)
end
end GroundTheory.Heights₂.Heights.Vertical


