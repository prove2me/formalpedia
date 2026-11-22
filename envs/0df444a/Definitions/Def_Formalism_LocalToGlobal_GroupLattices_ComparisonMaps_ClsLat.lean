-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
-- name    : Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:43:24.971297+00:00
-- url     : https://prove2.me/theorems/aefff0fd-a09c-4086-9c93-da43aa10bef8
-- title:
--   Cls Lat
-- statement:
--   Definitions and structural lemmas for Cls Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
namespace Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
section One
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
def gMap (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) : Submodule W (Fin k → Qq) :=
  A.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)
theorem mem_gMap (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) (x : Fin k → Qq) :
    x ∈ gMap W g A ↔ ∃ y ∈ A, (g : Matrix (Fin k) (Fin k) Qq) *ᵥ y = x := Submodule.mem_map
theorem gMap_one (A : Submodule W (Fin k → Qq)) : gMap W 1 A = A := by
  ext x
  rw [mem_gMap]
  simp
theorem gMap_mul (g h : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) : gMap W (g * h) A = gMap W g (gMap W h A) := by
  ext x
  simp only [mem_gMap, Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(h : Matrix (Fin k) (Fin k) Qq) *ᵥ y, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩
theorem gMap_inj (g : GL (Fin k) Qq) {A B : Submodule W (Fin k → Qq)} (h : gMap W g A = gMap W g B) : A = B := by
  have e := congrArg (gMap W g⁻¹) h
  rwa [← gMap_mul, ← gMap_mul, inv_mul_cancel, gMap_one, gMap_one] at e
def stdL : Submodule W (Fin k → Qq) := colSpan W (1 : Matrix (Fin k) (Fin k) Qq)
def stabStd : Subgroup (GL (Fin k) Qq) where
  carrier := {g | gMap W g (stdL W) = stdL W}
  one_mem' := gMap_one W _
  mul_mem' := by
    intro a b ha hb
    show gMap W (a * b) _ = _
    rw [gMap_mul, show gMap W b (stdL W) = stdL W from hb]
    exact ha
  inv_mem' := by
    intro a ha
    show gMap W a⁻¹ _ = _
    apply gMap_inj W a
    rw [← gMap_mul, mul_inv_cancel, gMap_one]
    exact (show gMap W a (stdL W) = stdL W from ha).symm
end One
section Tuples
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k nV : ℕ}
def tupOf (g : Fin nV → GL (Fin k) Qq) : Fin nV → Submodule W (Fin k → Qq) := fun v => gMap W (g v) (stdL W)
def stabTup : Subgroup (Fin nV → GL (Fin k) Qq) := Subgroup.pi Set.univ fun _ => stabStd W
end Tuples
end Formalism.L2.G.Cmp


