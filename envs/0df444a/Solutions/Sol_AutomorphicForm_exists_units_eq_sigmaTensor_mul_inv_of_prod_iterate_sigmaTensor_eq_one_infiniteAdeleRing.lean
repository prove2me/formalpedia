-- Prove2me | solution 1 for AutomorphicForm.exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f097b139-4ebe-54ed-96a9-ddd141fbbd90

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_Algebra_TensorProduct_exists_one_tmul_eq_of_map_eq_and_exists_units_eq_map_mul_inv_of_prod_iterate_map_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing

set_option autoImplicit false
set_option linter.unusedVariables false

open NumberField
open scoped TensorProduct

namespace ArchH90

theorem pi_version (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → Type) [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    (x : L ⊗[K] (Π i, F i))
    (hx : ((List.range (Module.finrank K L)).map fun k =>
        (⇑(Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (Π i, F i))))^[k] x).prod = 1) :
    ∃ y : (L ⊗[K] (Π i, F i))ˣ,
      x = Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (Π i, F i)) (y : L ⊗[K] (Π i, F i)) * ↑y⁻¹ := by
  set e : L ⊗[K] (Π i, F i) ≃ₐ[K] Π i, L ⊗[K] F i := Algebra.TensorProduct.piRight K K L F with he
  set S : L ⊗[K] (Π i, F i) →ₐ[K] L ⊗[K] (Π i, F i) :=
    Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (Π i, F i)) with hS
  set Si : ∀ i, L ⊗[K] F i →ₐ[K] L ⊗[K] F i :=
    fun i => Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (F i)) with hSi
  set ei : ∀ i, L ⊗[K] (Π i, F i) →ₐ[K] L ⊗[K] F i :=
    fun i => (Pi.evalAlgHom K (fun i => L ⊗[K] F i) i).comp e.toAlgHom with hei
  have hei_apply : ∀ i z, ei i z = e z i := fun i z => rfl

  have hnat : ∀ i z, ei i (S z) = Si i (ei i z) := by
    intro i z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      rw [hei_apply, hei_apply, hS, hSi, Algebra.TensorProduct.map_tmul, he,
        Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.map_tmul]
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hsemi : ∀ i, Function.Semiconj (ei i) S (Si i) := fun i z => hnat i z

  have hxi : ∀ i, ((List.range (Module.finrank K L)).map fun k => (⇑(Si i))^[k] (ei i x)).prod = 1 := by
    intro i
    have h := congrArg (ei i) hx
    rw [map_one, map_list_prod, List.map_map] at h
    have hfun : (⇑(ei i) ∘ fun k => (⇑S)^[k] x) = fun k => (⇑(Si i))^[k] (ei i x) :=
      funext fun k => ((hsemi i).iterate_right k).eq x
    rwa [hfun] at h

  have H : ∀ i, ∃ y : (L ⊗[K] F i)ˣ, ei i x = Si i (y : L ⊗[K] F i) * ↑y⁻¹ := fun i =>
    (Algebra.TensorProduct.exists_one_tmul_eq_of_map_eq_and_exists_units_eq_map_mul_inv_of_prod_iterate_map_eq_one
      K L (F i) σ hgen).2 (ei i x) (hxi i)
  choose y hy using H

  let Y : (Π i, L ⊗[K] F i)ˣ := MulEquiv.piUnits.symm y
  refine ⟨Units.mapEquiv e.symm.toRingEquiv.toMulEquiv Y, ?_⟩
  apply e.injective
  funext i
  rw [map_mul]
  change ei i x = ei i (S _) * e _ i
  rw [hnat i]
  simp only [hei_apply]
  have h1 : (e ((Units.mapEquiv e.symm.toRingEquiv.toMulEquiv Y : (L ⊗[K] (Π i, F i))ˣ) :
      L ⊗[K] (Π i, F i))) = (Y : Π i, L ⊗[K] F i) := by
    show e (e.symm (Y : Π i, L ⊗[K] F i)) = _
    exact e.apply_symm_apply _
  have h2 : (e (((Units.mapEquiv e.symm.toRingEquiv.toMulEquiv Y)⁻¹ : (L ⊗[K] (Π i, F i))ˣ) :
      L ⊗[K] (Π i, F i))) = ((Y⁻¹ : (Π i, L ⊗[K] F i)ˣ) : Π i, L ⊗[K] F i) := by
    rw [← map_inv]
    show e (e.symm ((Y⁻¹ : (Π i, L ⊗[K] F i)ˣ) : Π i, L ⊗[K] F i)) = _
    exact e.apply_symm_apply _
  rw [h1, h2]
  have hY : (Y : Π i, L ⊗[K] F i) i = (y i : L ⊗[K] F i) := rfl
  have hY' : ((Y⁻¹ : (Π i, L ⊗[K] F i)ˣ) : Π i, L ⊗[K] F i) i = ((y i)⁻¹ : (L ⊗[K] F i)ˣ) := rfl
  rw [hY, hY']
  exact hy i

end ArchH90

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L ⊗[K] InfiniteAdeleRing K)
    (hx : ((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ))^[i] x).prod = 1) :
    ∃ y : (L ⊗[K] InfiniteAdeleRing K)ˣ,
      x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (y : L ⊗[K] InfiniteAdeleRing K) * ↑y⁻¹ := by
  classical
  exact ArchH90.pi_version K L σ hgen (fun w : InfinitePlace K => w.Completion) x hx

end S_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing (solution)
