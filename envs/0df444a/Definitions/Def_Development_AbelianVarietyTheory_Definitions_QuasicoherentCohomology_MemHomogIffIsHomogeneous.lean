-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:13.70885+00:00
-- url     : https://prove2.me/theorems/e0ae95c7-1d24-4225-87a8-fff2b6e7db50
-- title:
--   Mem Homog Iff Is Homogeneous
-- statement:
--   Definitions and structural lemmas for Mem Homog Iff Is Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
namespace GlobalTheory
namespace SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
def map (f : M →ₗ[R] M') : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M' :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R M' ∘ₗ f)
@[simp] theorem map_ι (f : M →ₗ[R] M') (m : M) :
    map f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M' (f m) := by
  simp [map]
@[simp] theorem map_id : map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ := by
  ext m; simp
theorem map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map (g ∘ₗ f) = (map g).comp (map f) := by
  ext m; simp
variable (R M) in

def homog (d : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ d
theorem ι_mem_homog (m : M) : SymmetricAlgebra.ι R M m ∈ homog R M 1 := by
  simpa only [homog, pow_one] using LinearMap.mem_range_self _ m
instance gradedMonoid : SetLike.GradedMonoid (homog R M) :=
  Submodule.nat_power_gradedMonoid _
variable (R M) in

def gradedι : M →ₗ[R] ⨁ i : ℕ, homog R M i :=
  DirectSum.lof R ℕ (fun i => homog R M i) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ ι_mem_homog
theorem gradedι_apply (m : M) :
    gradedι R M m = DirectSum.of (fun i : ℕ => homog R M i) 1
      ⟨SymmetricAlgebra.ι R M m, ι_mem_homog m⟩ := rfl
instance gradedAlgebra : GradedAlgebra (homog R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (gradedι R M))
    (by
      ext m
      change DirectSum.coeAlgHom (homog R M)
        (SymmetricAlgebra.lift (gradedι R M) (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
      rw [SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
instance projective [Module.Projective R M] : Module.Projective R (SymmetricAlgebra R M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R M›
  refine Module.Projective.of_split (map s).toLinearMap
    (map (Finsupp.linearCombination R id)).toLinearMap ?_
  rw [← AlgHom.comp_toLinearMap, ← map_comp, hs, map_id]
  rfl
section BaseChange
variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]
variable (S) in

def mapOver (j : M →ₗ[R] W) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι S W).restrictScalars R ∘ₗ j)
@[simp] theorem mapOver_ι (j : M →ₗ[R] W) (m : M) :
    mapOver S j (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S W (j m) := by
  simp [mapOver]
variable (S) in

noncomputable def baseChangeHom (j : M →ₗ[R] W) :
    S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S W :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (mapOver S j) (fun _ _ => Commute.all _ _)
@[simp] theorem baseChangeHom_tmul (j : M →ₗ[R] W) (s : S) (x : SymmetricAlgebra R M) :
    baseChangeHom S j (s ⊗ₜ x) = s • mapOver S j x := by
  simp [baseChangeHom, Algebra.smul_def, Algebra.ofId_apply]
noncomputable def baseChangeEquiv {j : M →ₗ[R] W} (h : IsBaseChange S j) :
    S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S W :=
  AlgEquiv.ofAlgHom (baseChangeHom S j)
    (SymmetricAlgebra.lift
      (h.lift ((TensorProduct.mk R S (SymmetricAlgebra R M) 1) ∘ₗ SymmetricAlgebra.ι R M)))
    (by
      refine SymmetricAlgebra.algHom_ext (h.algHom_ext _ _ fun m => ?_)
      simp [h.lift_eq])
    (by
      ext m
      simp [h.lift_eq, Algebra.TensorProduct.one_def])
end BaseChange
end SymAlg
end GlobalTheory


