-- Prove2me | solution 1 for AutomorphicForm.exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/19440f85-1a6e-5fb7-bec0-c68e1521feb9

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z) :
    ∃ b : Fin 4 → Matrix (Fin 2) (Fin 2) L, LinearIndependent K b ∧
      ∀ X : Matrix (Fin 2) (Fin 2) L,
        X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
          X ∈ Submodule.span K (Set.range b) := by

  have hz := (AutomorphicForm.exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar K L h2 σ hgen δ₀ c u hN hns).1

  let D₀ : Submodule K (Matrix (Fin 2) (Fin 2) L) :=
    { carrier := {X | X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ}
      add_mem' := by
        intro X Y hX hY
        simp only [Set.mem_setOf_eq] at hX hY ⊢
        rw [add_mul, Matrix.map_add (σ : L → L) (map_add σ), mul_add, hX, hY]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, zero_mul]
        rw [Matrix.map_zero (σ : L → L) (map_zero σ), mul_zero]
      smul_mem' := by
        intro a X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have hmap : (a • X).map σ = a • X.map σ := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
        rw [smul_mul_assoc, hmap, mul_smul_comm, hX] }
  have hmem : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X ∈ D₀ ↔ X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ := fun X => Iff.rfl

  set e₁ : Fin 2 → L := Pi.single 0 1 with he₁
  have he₁0 : e₁ ≠ 0 := by
    intro h; have := congrFun h 0; simp [he₁] at this
  have huniq := AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two K L h2 σ hgen δ₀ hz hns e₁ he₁0
  let φ : D₀ →ₗ[K] (Fin 2 → L) :=
    { toFun := fun X => (X : Matrix (Fin 2) (Fin 2) L).mulVec e₁
      map_add' := by intro X Y; simp [Matrix.add_mulVec]
      map_smul' := by intro a X; simp [Matrix.smul_mulVec] }
  have hφ : Function.Bijective φ := by
    refine ⟨fun X Y hXY => ?_, fun w => ?_⟩
    · obtain ⟨Z, hZ, hZu⟩ := huniq ((X : Matrix (Fin 2) (Fin 2) L).mulVec e₁)
      have h1 : (X : Matrix (Fin 2) (Fin 2) L) = Z := hZu _ ⟨(hmem _).mp X.2, rfl⟩
      have h2' : (Y : Matrix (Fin 2) (Fin 2) L) = Z := hZu _ ⟨(hmem _).mp Y.2, hXY.symm⟩
      exact Subtype.ext (h1.trans h2'.symm)
    · obtain ⟨Z, ⟨hZ, hZw⟩, -⟩ := huniq w
      exact ⟨⟨Z, (hmem Z).mpr hZ⟩, hZw⟩
  let Φ : D₀ ≃ₗ[K] (Fin 2 → L) := LinearEquiv.ofBijective φ hφ
  have hrank : Module.finrank K D₀ = 4 := by
    rw [Φ.finrank_eq, Module.finrank_pi_fintype K]
    simp [h2]

  let B := Module.finBasisOfFinrankEq K D₀ hrank
  refine ⟨fun i => (B i : Matrix (Fin 2) (Fin 2) L), ?_, fun X => ?_⟩
  · exact B.linearIndependent.map' D₀.subtype (Submodule.ker_subtype D₀)
  · have hspan : Submodule.span K (Set.range fun i => (B i : Matrix (Fin 2) (Fin 2) L)) = D₀ := by
      have : (Set.range fun i => (B i : Matrix (Fin 2) (Fin 2) L)) = D₀.subtype '' Set.range B := by
        ext X; simp [Set.mem_image, Set.mem_range]
      rw [this, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [hspan]
    exact (hmem X).symm

end S_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
end P2MW
export P2MW.S_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar (solution)
