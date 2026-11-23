-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
-- name    : GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:41.148919+00:00
-- url     : https://prove2.me/theorems/e3a8bba2-cdbe-4738-bbef-ba282cde3e07
-- title:
--   Order Scalars
-- statement:
--   Definitions and structural lemmas for Order Scalars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
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
section General
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)
def cocycles₂IntRepAddEquiv :
    cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) ≃+ cocycles₂ (Rep.of (zRepOfMonoidEnd φ)) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
theorem h2π_intRepOfMonoidEnd_surjective :
    Function.Surjective (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance
theorem h2π_zRepOfMonoidEnd_surjective :
    Function.Surjective (H2π (Rep.of (zRepOfMonoidEnd φ))).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance
theorem map_ker_h2π_intRepOfMonoidEnd :
    (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom.toAddMonoidHom.ker.map
        (cocycles₂IntRepAddEquiv φ : cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) →+
          cocycles₂ (Rep.of (zRepOfMonoidEnd φ))) =
      (H2π (Rep.of (zRepOfMonoidEnd φ))).hom.toAddMonoidHom.ker := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (H2π _).hom _ = 0
    change (H2π _).hom y = 0 at hy
    rw [H2π_eq_zero_iff] at hy ⊢
    exact hy
  · intro hx
    refine ⟨(cocycles₂IntRepAddEquiv φ).symm x, ?_, rfl⟩
    change (H2π _).hom x = 0 at hx
    change (H2π _).hom _ = 0
    rw [H2π_eq_zero_iff] at hx ⊢
    exact hx
noncomputable def h2IntRepAddEquiv :
    groupCohomology (Rep.of (intRepOfMonoidEnd.{0} φ)) 2 ≃+
      groupCohomology (Rep.of (zRepOfMonoidEnd φ)) 2 :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective _
      (h2π_intRepOfMonoidEnd_surjective φ)).symm.trans
    (QuotientAddGroup.congr _ _ (cocycles₂IntRepAddEquiv φ)
      (map_ker_h2π_intRepOfMonoidEnd φ))).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (h2π_zRepOfMonoidEnd_surjective φ))
end General
section Galois
variable (K L : Type) [Field K] [Field L] [Algebra K L]
noncomputable def h2GalUnitsAddEquiv :
    groupCohomology (galUnits K L) 2 ≃+ groupCohomology (galUnitsZ K L) 2 :=
  h2IntRepAddEquiv (galUnitsHom K L)
end Galois
end GroundTheory.ProfCoh


