-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_AugTrivial
-- name    : GroundTheory_TateCohomology_AugTrivial
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:50.97081+00:00
-- url     : https://prove2.me/theorems/efe30386-c598-4b45-af25-f24be1f044c4
-- title:
--   Aug Trivial
-- statement:
--   Definitions and structural lemmas for Aug Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_of_linear
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
namespace GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
noncomputable def augHom : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨augmentation k G, fun g => LinearMap.ext fun x => by
    change augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x
    exact augmentation_ρ g x⟩
@[simp] theorem augHom_apply (x : Rep.leftRegular k G) :
    (augHom k G).hom x = augmentation k G x := rfl
theorem augIdealι_augHom : augIdealι k G ≫ augHom k G = 0 := by
  ext x
  exact LinearMap.mem_ker.1 x.2
noncomputable def augTrivSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (augIdealι k G) (augHom k G) (augIdealι_augHom k G)
@[simp] theorem augTrivSES_X₁ : (augTrivSES k G).X₁ = augIdeal k G := rfl
@[simp] theorem augTrivSES_X₂ : (augTrivSES k G).X₂ = Rep.leftRegular k G := rfl
@[simp] theorem augTrivSES_X₃ : (augTrivSES k G).X₃ = Rep.trivial k G k := rfl
theorem augTrivSES_shortExact : (augTrivSES k G).ShortExact := by
  refine shortExact_of_linear (fun a b h => Subtype.ext h)
    (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩)
    (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)
  exact augmentation_single (k := k) (1 : G) (show k from r)
variable {k G}
noncomputable def augIdealSubOne (g : G) : augIdeal k G :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augmentation_single, augmentation_single, sub_self]⟩
@[simp] theorem augIdealSubOne_val (g : G) :
    ((augIdealSubOne g : augIdeal k G) : MonoidAlgebra k G) =
      MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl
section Cocycle
variable {A : Rep.{u} k G}
noncomputable def cocycleLinear (f : cocycles₁ A) : MonoidAlgebra k G →ₗ[k] A.V :=
  Finsupp.linearCombination k (fun g => f g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
theorem cocycleLinear_single (f : cocycles₁ A) (g : G) (r : k) :
    cocycleLinear f (MonoidAlgebra.single g r) = r • f g := by
  simp [cocycleLinear]
theorem cocycleLinear_ρ (f : cocycles₁ A) (s : G) (x : MonoidAlgebra k G) :
    cocycleLinear f ((Rep.leftRegular k G).ρ s x) =
      A.ρ s (cocycleLinear f x) + augmentation k G x • f s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]; abel
  | single g r =>
    have hf : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff _).1 f.2 s g
    rw [Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single,
      augmentation_single, map_smul, hf, smul_add]
noncomputable def cocycleHom (f : cocycles₁ A) : augIdeal k G ⟶ A :=
  Rep.ofHom ⟨cocycleLinear f ∘ₗ (LinearMap.ker (augmentation k G)).subtype, fun s =>
    LinearMap.ext fun x => by
      have hx : augmentation k G x.1 = 0 := LinearMap.mem_ker.1 x.2
      change cocycleLinear f ((Rep.leftRegular k G).ρ s x.1) = A.ρ s (cocycleLinear f x.1)
      rw [cocycleLinear_ρ, hx, zero_smul, add_zero]⟩
end Cocycle
section Restrict
variable (k) {H : Type u} [Group H] (φ : H →* G)
noncomputable def augCocycle : cocycles₁ (Rep.res φ (augIdeal k G)) :=
  ⟨fun h => augIdealSubOne (φ h), (mem_cocycles₁_iff _).2 fun a b => by
    apply Subtype.ext
    change MonoidAlgebra.single (φ (a * b)) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ a) (MonoidAlgebra.single (φ b) 1 - MonoidAlgebra.single 1 1) +
        (MonoidAlgebra.single (φ a) 1 - MonoidAlgebra.single 1 1)
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, smul_eq_mul,
      smul_eq_mul, mul_one, map_mul]
    abel⟩
theorem augTrivSES_res_shortExact : ((augTrivSES k G).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (augTrivSES_shortExact k G)
def oneInvariant : (Rep.res φ (Rep.trivial k G k)).ρ.invariants :=
  ⟨(1 : k), fun _ => rfl⟩
end Restrict
end GroundTheory.GroupCoh


