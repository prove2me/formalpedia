-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:30.596663+00:00
-- url     : https://prove2.me/theorems/e9393732-1db3-4850-9cf9-2ab882f9061b
-- title:
--   Exists Odd Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Odd Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsOddNeZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
section Ring
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
def homRing : Subring (AddMonoid.End (Additive (A ⟶ A))) where
  carrier := {f | ∃ u : A ⟶ A, IsMonHom u ∧ ∀ x : A ⟶ A, f (Additive.ofMul x) = Additive.ofMul (x ≫ u)}
  mul_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    exact ⟨v ≫ u, inferInstance, fun x => by
      change f (g _) = _
      rw [hg, hf, Category.assoc]⟩
  one_mem' := ⟨𝟙 A, inferInstance, fun x => by rw [Category.comp_id]; rfl⟩
  add_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    refine ⟨u * v, by rw [Hom.mul_def]; infer_instance, fun x => ?_⟩
    rw [MonObj.comp_mul, ofMul_mul, ← hf, ← hg]; rfl
  zero_mem' := ⟨1, by rw [Hom.one_def]; infer_instance, fun x => by rw [MonObj.comp_one]; rfl⟩
  neg_mem' := by
    rintro f ⟨u, hu, hf⟩
    refine ⟨u⁻¹, by rw [Hom.inv_def]; infer_instance, fun x => ?_⟩
    rw [GrpObj.comp_inv, ofMul_inv, ← hf]; rfl
variable {A}
def toRing (u : A ⟶ A) [IsMonHom u] : homRing A :=
  ⟨MonoidHom.toAdditive (IsMonHom.monoidHom u A), u, inferInstance, fun _ => rfl⟩
noncomputable def iter (σ : A ≅ A) : ℕ → (A ≅ A)
  | 0 => Iso.refl A
  | m + 1 => iter σ m ≪≫ σ
omit [IsCommMonObj A] in
instance isMonHom_iter (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) : IsMonHom (iter σ m).hom := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 A))
  | succ m ih => exact inferInstanceAs (IsMonHom ((iter σ m).hom ≫ σ.hom))
end Ring
end GlobalTheory.SerreField


