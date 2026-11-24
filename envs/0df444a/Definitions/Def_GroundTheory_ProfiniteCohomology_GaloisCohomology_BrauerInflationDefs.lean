-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_BrauerInflationDefs
-- name    : GroundTheory_ProfiniteCohomology_GaloisCohomology_BrauerInflationDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:58:17.727932+00:00
-- url     : https://prove2.me/theorems/d12e3a15-1679-4c70-b066-48342727a598
-- title:
--   Brauer Inflation Defs
-- statement:
--   Definitions and structural lemmas for Brauer Inflation Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/BrauerInflationDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
section Tower
variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]
noncomputable def unitsTowerHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩
noncomputable def unitsInflationTower (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E) (unitsTowerHom K E F) n
end Tower
section LE
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F) [Normal K E]
noncomputable def galRestrictOfLE : Gal(F/K) →* Gal(E/K) :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  AlgEquiv.restrictNormalHom E
noncomputable def unitsOfLE :
    Rep.res (galRestrictOfLE h) (galUnits.{u} K E) ⟶ galUnits.{u} K F :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  unitsTowerHom K E F
noncomputable def unitsInflationOfLE (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (galRestrictOfLE h) (unitsOfLE h) n
end LE
end GroundTheory.ProfCoh


