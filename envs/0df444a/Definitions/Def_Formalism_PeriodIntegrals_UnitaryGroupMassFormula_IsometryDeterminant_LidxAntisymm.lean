-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:18.724436+00:00
-- url     : https://prove2.me/theorems/03038ae3-dfb1-4f18-af83-9b5ec4f7254b
-- title:
--   Lidx Antisymm
-- statement:
--   Definitions and structural lemmas for Lidx Antisymm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.IsoDetW.Loc
open PI.IsoDetDefs
section Gen
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
def relative₂ (X Z : Submodule R W) : ℕ∞ := Module.length R (Z ⧸ X.comap Z.subtype)
end Gen
section Loc
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]
end Loc
section Sat
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
variable {W W' : Type*} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
  [AddCommGroup W'] [Module K W'] [Module R W'] [IsScalarTower R K W']
end Sat
end PI.IsoDetW.Loc


