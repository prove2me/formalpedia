-- Prove2me | solution 1 for AutomorphicForm.semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/43064300-c42a-5153-9c0b-680e18914fde

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace E29AW

open AutomorphicForm NumberField.AdelicHeight

example (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    IsUltrametricDist (w.adicCompletion L) := inferInstance

theorem weight_diagUnits2_mul {F : Type*} [NormedField F] (t₁ t₂ : Fˣ) (x : GL (Fin 2) F) :
    LocalWeight.weight (diagUnits2 t₁ t₂ * x) = LocalWeight.weight x := by
  have h1 : ‖(t₁ : F)‖ ≠ 0 := norm_ne_zero_iff.mpr t₁.ne_zero
  have h2 : ‖(t₂ : F)‖ ≠ 0 := norm_ne_zero_iff.mpr t₂.ne_zero
  have e : ∀ j : Fin 2,
      ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 j = (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 j ∧
      ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j = (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 j := by
    intro j
    simp [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (t₁ : F) * (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Units.val_mul, Matrix.det_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.det_fin_two_of]
    ring
  unfold LocalWeight.weight AdelicHeight.rowMaxNorm
  rw [(e 0).1, (e 1).1, (e 0).2, (e 1).2, hdet]
  simp only [norm_mul]
  rw [← mul_max_of_nonneg _ _ (norm_nonneg (t₁ : F)), ← mul_max_of_nonneg _ _ (norm_nonneg (t₂ : F))]
  congr 1
  field_simp

theorem rowmax_mul_le {F : Type*} [NormedField F] [IsUltrametricDist F]
    (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i : Fin 2) :
    max ‖(M * N) i 0‖ ‖(M * N) i 1‖ ≤ max ‖M i 0‖ ‖M i 1‖ := by
  have key : ∀ j : Fin 2, ‖(M * N) i j‖ ≤ max ‖M i 0‖ ‖M i 1‖ := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hN 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hN 1 j)).trans (le_max_right _ _)
  exact max_le (key 0) (key 1)

theorem weight_mul_integral {F : Type*} [NormedField F] [IsUltrametricDist F] (x k : GL (Fin 2) F)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1) :
    LocalWeight.weight (x * k) = LocalWeight.weight x := by

  have hrow : ∀ i : Fin 2,
      max ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 1‖ =
        max ‖(x : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) i 1‖ := by
    intro i
    refine le_antisymm ?_ ?_
    · rw [Units.val_mul]; exact rowmax_mul_le _ _ hk i
    · have : (x : Matrix (Fin 2) (Fin 2) F) = ((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]; exact rowmax_mul_le _ _ hk' i

  have hdk : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ = 1 := by
    have hle : ∀ (m : Matrix (Fin 2) (Fin 2) F), (∀ i j, ‖m i j‖ ≤ 1) → ‖m.det‖ ≤ 1 := by
      intro m hm
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_one₀ (hm 0 0) (norm_nonneg _) (hm 1 1)
      · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hm 0 1) (norm_nonneg _) (hm 1 0)
    have h1 := hle _ hk
    have h2 := hle _ hk'
    have hprod : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ * ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    have ha0 : 0 ≤ ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ := norm_nonneg _
    have hge : 1 ≤ ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ := by
      calc (1 : ℝ) = ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ * ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ := hprod.symm
        _ ≤ ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ * 1 := mul_le_mul_of_nonneg_left h2 ha0
        _ = ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ := mul_one _
    exact le_antisymm h1 hge
  unfold LocalWeight.weight AdelicHeight.rowMaxNorm
  rw [hrow 0, hrow 1, Units.val_mul, Matrix.det_mul, norm_mul, hdk, mul_one]

end E29AW

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (p₁ p₂ : (L ⊗[K] v.adicCompletion K)ˣ) (x k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    AutomorphicForm.semiLocalWeight K L v (diagUnits2 p₁ p₂ * x * k) = AutomorphicForm.semiLocalWeight K L v x := by
  classical

  set comp := AutomorphicForm.semiLocalPlaceComponent K L v with hcomp

  have hint : ∀ (w : v.Extension (𝓞 L)) (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      g ∈ AutomorphicForm.semiLocalIntegralSet K L v →
        (∀ i j, ‖((comp w g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j‖ ≤ 1) ∧
        (∀ i j, ‖(((comp w g)⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j‖ ≤ 1) := by
    intro w g hg
    have key : ∀ y : L ⊗[K] v.adicCompletion K, y ∈ AutomorphicForm.semiLocalIntegers K L v →
        ‖((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
            (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom) y‖ ≤ 1 := by
      intro y hy
      rw [AutomorphicForm.semiLocalIntegers_eq_preimage] at hy
      have hyw := hy w (Set.mem_univ w)
      dsimp only at hyw
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hyw
      exact hyw
    rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact key _ (hg.1 i j)
    · rw [← map_inv]
      exact key _ (hg.2 i j)

  have hdiag : ∀ w : v.Extension (𝓞 L),
      comp w (diagUnits2 p₁ p₂) =
        diagUnits2
          (Units.map (((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
            (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom).toMonoidHom) p₁)
          (Units.map (((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
            (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom).toMonoidHom) p₂) := by
    intro w
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hcomp, AutomorphicForm.semiLocalPlaceComponent, Matrix.GeneralLinearGroup.map,
        LanglandsTunnell.CubicInduction.coe_diagUnits2]
  unfold AutomorphicForm.semiLocalWeight
  refine finsum_congr fun w => ?_
  rw [map_mul, map_mul]
  obtain ⟨h1, h2⟩ := hint w k hk
  rw [show AutomorphicForm.semiLocalPlaceComponent K L v w = comp w from rfl, E29AW.weight_mul_integral _ _ h1 h2, hdiag w,
    E29AW.weight_diagUnits2_mul]

end S_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet (solution)
