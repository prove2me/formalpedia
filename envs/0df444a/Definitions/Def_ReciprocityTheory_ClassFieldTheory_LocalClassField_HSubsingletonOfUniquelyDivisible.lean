-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:49.153958+00:00
-- url     : https://prove2.me/theorems/c7ab86cd-4770-4db6-a19c-3ceaa2ff6e8e
-- title:
--   HSubsingleton Of Uniquely Divisible
-- statement:
--   Definitions and structural lemmas for HSubsingleton Of Uniquely Divisible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def oneCocycleEquivCharacters : Gal.Z1 (trivRep G QZ).rho ≃+ charGrp G where
  toFun c := ⟨AddMonoidHom.mk' (fun a : Additive G => (c.1 a.toMul : QZ)) fun a b => c.2.2 a.toMul b.toMul,
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ c.1).2 c.2.1⟩
  invFun χ := ⟨fun g => χ.1 (Additive.ofMul g),
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ _).1 χ.2,
    fun g h => map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


