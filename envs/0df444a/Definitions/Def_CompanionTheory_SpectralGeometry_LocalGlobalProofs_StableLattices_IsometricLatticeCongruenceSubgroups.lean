-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:09.946591+00:00
-- url     : https://prove2.me/theorems/9199e327-2992-42d6-90b7-6d6935b53e47
-- title:
--   Isometric Lattice Congruence Subgroups
-- statement:
--   Definitions and structural lemmas for Isometric Lattice Congruence Subgroups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
namespace GlobalTheory.CompanionTheory.CartanU
section Form
variable {L : Type} [NontriviallyNormedField L] {n : ℕ}
def form (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  dotProduct (s ∘ x) (J.mulVec y)
def toE : GL (Fin n) L →* ((Fin n → L) ≃ₗ[L] (Fin n → L)) where
  toFun g := LinearEquiv.ofLinear (Matrix.mulVecLin g.1) (Matrix.mulVecLin (g⁻¹).1)
    (by rw [← Matrix.mulVecLin_mul]; simp) (by rw [← Matrix.mulVecLin_mul]; simp)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [Matrix.mulVec_mulVec]
def ofE (t : (Fin n → L) ≃ₗ[L] (Fin n → L)) : GL (Fin n) L :=
  ⟨LinearMap.toMatrix' t.toLinearMap, LinearMap.toMatrix' t.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
end Form
section Tor
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
end Tor
def ind {l : ℕ} (i : Fin l) : Fin l → ℕ := fun j => if j ≤ i then 1 else 0
end GlobalTheory.CompanionTheory.CartanU
end


