-- Prove2me | solution 1 for AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/393c8f3d-477a-5214-9942-5b980c3c2145

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace FinWindowFamily

theorem transport (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (C c : ℂ)
    {g₁ g₂ : GL (Fin 2) (v.adicCompletion K)} (h : g₁ = g₂)
    (H : ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v g₂) (AutomorphicForm.localCentralizerBorel K v g₂)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g₂) τ →
      τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v g₂ τ fv I → C * I = c)
    (τ : @Measure (AutomorphicForm.localCentralizer K v g₁) (AutomorphicForm.localCentralizerBorel K v g₁))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g₁) τ)
    (h1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v g₁ τ fv I) : C * I = c := by
  subst h
  exact H τ hτ h1 I hI

theorem finComponent_eq (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) *
        diagUnits2 (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u) 1 := by
  have e1 : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      ((Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) := rfl
  have e2 : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      ((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) := rfl
  have e3 : ((NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := rfl
  have hs : ∀ i j : Fin 2, ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      if i = j then ((NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) else 0 := by
    intro i j
    change Matrix.scalar (Fin 2) _ i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, e1, e2, ← e3, Units.val_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hs, hs, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp

end FinWindowFamily

open FinWindowFamily in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (τF : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z))
    (hτF1 : ∀ z, τF z (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z) fv I →
          (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
            Φ (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
  classical
  obtain ⟨Φ, hΦlc, hΦcs, hΦ⟩ :=
    AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
      K v fv hfv
  refine ⟨Φ, hΦlc, hΦcs, fun z I hI => ?_⟩
  have huv : ((Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) ≠ 1 := by
    rw [Units.coe_map, MonoidHom.coe_coe, ne_eq, ← (algebraMap K (v.adicCompletion K)).map_one]
    exact fun h => hu1 ((algebraMap K (v.adicCompletion K)).injective h)
  have key := transport K v fv _ _ (finComponent_eq K v u z)
    (hΦ (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u)
      (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) huv)
    (τF z) (hτF z) (hτF1 z) I hI
  simpa only [Units.coe_map, MonoidHom.coe_coe] using key

end S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2 (solution)
