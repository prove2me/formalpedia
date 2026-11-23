-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:23.775467+00:00
-- url     : https://prove2.me/theorems/b42e756d-6d3d-493c-8290-f1bb76479fb7
-- title:
--   Mj Smul Right
-- statement:
--   Definitions and structural lemmas for Mj Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
def mj (z x y : S.V) : E := S.hT x y - 2 / S.hT z z * (S.hT x z * S.hT z y)
variable {S}
section Pos
variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos
end Pos
end PI.AutLzFinite.SlopeTestRemainingChoices


