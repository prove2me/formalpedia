-- Prove2me | solution 1 for AutomorphicForm.eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/53fd3fdd-a92e-5007-9cb0-fe3ce8e18806

import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace K42H90

theorem scale {K : Type*} [Field K] (A D A' D' r Z : K) (hr0 : r ≠ 0)
    (hr : r * D = A) (hr' : r * D' = A') (hZ : Z * A = A') :
    A' = Z * A ∧ D' = Z * D := by
  refine ⟨hZ.symm, ?_⟩
  apply mul_left_cancel₀ hr0
  rw [hr', ← hZ, ← hr]
  ring

end K42H90

open scoped TensorProduct.RightActions in
open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ t ∈ Δ, ∀ t' ∈ Δ,
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) =
        Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) → t = t' := by
  intro t ht t' ht' hN
  by_contra hne
  obtain ⟨h10, h01, -⟩ := hΔd t ht
  obtain ⟨h10', h01', -⟩ := hΔd t' ht'
  have hdisj := hΔdisj t ht t' ht' hne

  have hdet := Matrix.GeneralLinearGroup.det_ne_zero t
  have hdet' := Matrix.GeneralLinearGroup.det_ne_zero t'
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  rw [Matrix.det_fin_two, h10', mul_zero, sub_zero] at hdet'
  have ha : (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have ha' : (t' : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul hdet'
  have hd' : (t' : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul hdet'

  set ζ : L := (t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 0 0 with hζ
  have hζ0 : ζ ≠ 0 := div_ne_zero ha' ha
  have hr0 : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (div_ne_zero ha hd)
  have hr : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) *
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    rw [← map_mul, div_mul_cancel₀ _ hd]
  have hr' : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) *
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    rw [hN, ← map_mul, div_mul_cancel₀ _ hd']
  have hZ : Algebra.norm K ζ * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) =
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    rw [← map_mul, hζ, div_mul_cancel₀ _ ha]
  have hsc := K42H90.scale _ _ _ _ _ _ hr0 hr hr' hZ
  have key := (LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
    (K := K) (L := L) hgen).2.2 t t' ⟨h10, h01⟩ ⟨h10', h01'⟩
  have heq := key.2.mpr ⟨ζ, hζ0, Or.inl hsc⟩
  have hmem : ∀ s : GL (Fin 2) L, s ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      s⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} := by
    intro s
    refine ⟨1, ?_⟩
    simp only [inv_one, one_mul, map_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  have h1 : t ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} := by
    rw [heq]; exact hmem t
  exact Set.disjoint_left.mp hdisj (hmem t) h1

end S_AutomorphicForm_eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses
end P2MW
export P2MW.S_AutomorphicForm_eq_of_norm_div_eq_norm_div_of_mem_of_disjoint_sigmaClasses (solution)
