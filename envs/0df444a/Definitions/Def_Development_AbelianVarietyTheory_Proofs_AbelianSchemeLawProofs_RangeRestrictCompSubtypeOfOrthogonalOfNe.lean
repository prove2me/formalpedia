-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:08.193632+00:00
-- url     : https://prove2.me/theorems/7b0bc0d7-752d-5a28-a22e-e44d84b6ca3d
-- title:
--   Range Restrict Comp Subtype Of Orthogonal Of Ne
-- statement:
--   Definitions and structural lemmas for Range Restrict Comp Subtype Of Orthogonal Of Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Theorems.Thm_P2M_GlobalTheory_Cube_subsingleton_trunc__e70445e4868d
import Theorems.Thm_P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d
import Theorems.Thm_P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45
import Theorems.Thm_P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
namespace GlobalTheory
section Retract
variable {R : Type u} [Ring R]
end Retract
namespace Cube
section Total
variable {ι : Type} {R : Type u} [Ring R]
def restrictDeg (A : Cube.{v} ι R) (p : ℕ) : (∀ s, A.obj s) →ₗ[R] Term A p :=
  LinearMap.pi fun s => LinearMap.proj s.1
def degProj (A : Cube.{v} ι R) (p : ℕ) : Module.End R (∀ s, A.obj s) :=
  extend A p ∘ₗ restrictDeg A p
def degSign (A : Cube.{v} ι R) : Module.End R (∀ s, A.obj s) :=
  LinearMap.pi fun s => (-1 : ℤ) ^ s.card • LinearMap.proj s
variable [LinearOrder ι]
end Total
end Cube
section Criterion
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
open GlobalTheory.Cube
end Criterion
section Contraction
variable {ι : Type} [LinearOrder ι] {K : Type u} [Field K]
open GlobalTheory.Cube
end Contraction
section TensorAlgebra
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
end TensorAlgebra
namespace Cube
section ExtTensor
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
noncomputable def extTensor (A : Cube.{v} ι K) (B : Cube.{v} κ K) : Cube.{v} (ι ⊕ₗ κ) K :=
  mk (fun w => ModuleCat.of K (A.obj (part (inlEmb ι κ) w) ⊗[K] B.obj (part (inrEmb ι κ) w)))
    (fun h => TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)))
    (fun _ x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, hx, hy])
    (fun _ _ x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add])
theorem extTensor_obj (A : Cube.{v} ι K) (B : Cube.{v} κ K) (w : Finset (ι ⊕ₗ κ)) :
    (extTensor A B).obj w =
      ModuleCat.of K (A.obj (part (inlEmb ι κ) w) ⊗[K] B.obj (part (inrEmb ι κ) w)) := rfl
variable (ι κ) in

noncomputable def partsEquiv : Finset (ι ⊕ₗ κ) ≃ Σ _ : Finset ι, Finset κ where
  toFun w := ⟨part (inlEmb ι κ) w, part (inrEmb ι κ) w⟩
  invFun x := sumVertex x.1 x.2
  left_inv := sumVertex_part
  right_inv x := by simp
noncomputable def totalTensorEquiv [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K) :
    (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t) ≃ₗ[K] ∀ w, (extTensor A B).obj w :=
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite κ
  TensorProduct.piLeft K (∀ t, B.obj t) (fun s => A.obj s) ≪≫ₗ
    (LinearEquiv.piCongrRight fun s => TensorProduct.piRight K K (A.obj s) fun t => B.obj t) ≪≫ₗ
    (LinearEquiv.piCurry K fun (s : Finset ι) (t : Finset κ) => A.obj s ⊗[K] B.obj t).symm ≪≫ₗ
    (LinearEquiv.piCongrLeft K (fun x : Σ _ : Finset ι, Finset κ => A.obj x.1 ⊗[K] B.obj x.2)
      (partsEquiv ι κ)).symm
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
omit [Finite ι] [Finite κ]
variable {A B}
noncomputable def extTensorMap {A' : Cube.{v} ι K} {B' : Cube.{v} κ K} (φ : A ⟶ A') (ψ : B ⟶ B') :
    extTensor A B ⟶ extTensor A' B' :=
  homMk (A := extTensor A B) (B := extTensor A' B')
    (fun w => TensorProduct.map (φ.app (part (inlEmb ι κ) w)).hom (ψ.app (part (inrEmb ι κ) w)).hom)
    fun {w w'} h x => by
      have : TensorProduct.map (φ.app (part (inlEmb ι κ) w')).hom
            (ψ.app (part (inrEmb ι κ) w')).hom ∘ₗ
          TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)) =
          TensorProduct.map (res A' (monotone_part _ h)) (res B' (monotone_part _ h)) ∘ₗ
            TensorProduct.map (φ.app (part (inlEmb ι κ) w)).hom
              (ψ.app (part (inrEmb ι κ) w)).hom :=
        TensorProduct.ext' fun a b => congrArg₂ (fun a b => a ⊗ₜ[K] b) (app_res φ _ a)
          (app_res ψ _ b)
      exact LinearMap.congr_fun this x
variable (A B)
noncomputable def trunc₂ExtTensorIso :
    trunc₂ (extTensor A B) ≅ extTensor (trunc₁ A) (trunc₁ B) :=
  (trunc₂Iso (extTensorMap (trunc₁Incl A) (trunc₁Incl B)) fun s t hs ht =>
    TensorProduct.map_bijective (trunc₁Incl_bijective A (by simpa using hs))
      (trunc₁Incl_bijective B (by simpa using ht))).symm ≪≫
  @asIso _ _ _ _ (trunc₂Incl _) (isIso_of_bijective _ fun w => by
    obtain ⟨s, t, rfl⟩ : ∃ s t, w = sumVertex s t := ⟨_, _, (sumVertex_part w).symm⟩
    by_cases h : s = ∅ ∨ t = ∅
    · have := subsingleton_trunc₂ (extTensor (trunc₁ A) (trunc₁ B)) h
      have : Subsingleton ((extTensor (trunc₁ A) (trunc₁ B)).obj (sumVertex s t)) := by
        rw [extTensor_obj, part_inlEmb_sumVertex, part_inrEmb_sumVertex]
        rcases h with rfl | rfl
        · have := subsingleton_trunc₁_empty A
          exact inferInstanceAs (Subsingleton (_ ⊗[K] _))
        · have := subsingleton_trunc₁_empty B
          exact inferInstanceAs (Subsingleton (_ ⊗[K] _))
      exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
    · rw [not_or] at h
      exact trunc₂Incl_bijective _ (Finset.nonempty_iff_ne_empty.2 h.1)
        (Finset.nonempty_iff_ne_empty.2 h.2))
end ExtTensor
end Cube
section Kuenneth
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]
end Kuenneth
end GlobalTheory


