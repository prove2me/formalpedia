-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b64843bd-19f7-5fa1-a7ae-8e9701ba57aa

import Mathlib
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
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

open scoped TensorProduct.RightActions
open AutomorphicForm AutomorphicForm.TransversalMeasure

noncomputable section

namespace Blk408SuppDet

section Det

theorem continuous_glDet (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (Matrix.GeneralLinearGroup.det : GL (Fin 2) A → Aˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · have h : (fun g : GL (Fin 2) A => ((Matrix.GeneralLinearGroup.det g)⁻¹ : Aˣ).val) =
        fun g : GL (Fin 2) A => Matrix.det ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := by
      funext g; rw [← map_inv]; rfl
    rw [h]
    exact Units.continuous_coe_inv.matrix_det

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem semiLocalIdele_det (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 L) L) :
    semiLocalIdele K L v (Matrix.GeneralLinearGroup.det g) =
      Matrix.GeneralLinearGroup.det (semiLocalComponent K L v (glFin (𝓞 L) L g)) := by
  apply Units.ext
  rw [semiLocalComponent, glFin, Matrix.GeneralLinearGroup.map_det, Matrix.GeneralLinearGroup.map_det]
  rfl

theorem archSemiLocalIdele_det (u : InfinitePlace K) (g : AdelicGL2 (𝓞 L) L) :
    archSemiLocalIdele K L u (Matrix.GeneralLinearGroup.det g) =
      archFibre K L u (Matrix.GeneralLinearGroup.det (glArch (𝓞 L) L g)) := by
  apply Units.ext
  rw [glArch, Matrix.GeneralLinearGroup.map_det]
  rfl

theorem continuous_archFibre (u : InfinitePlace K) : Continuous (archFibre K L u) :=
  Continuous.units_map _ (continuous_pi fun w => continuous_apply w.1)

theorem continuous_idelicNorm :
    Continuous ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) :=
  Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)

end Det

section Integral

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def slSubring : Subring (L ⊗[K] v.adicCompletion K) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring

theorem mem_slSubring_iff (y : L ⊗[K] v.adicCompletion K) :
    y ∈ slSubring K L v ↔ y ∈ semiLocalIntegers K L v := by
  rw [slSubring, Subalgebra.mem_toSubring, AlgHom.mem_range, semiLocalIntegers, Set.mem_range]

theorem det_val_mem {M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ semiLocalIntegers K L v) : M.det ∈ semiLocalIntegers K L v := by
  simp_rw [← mem_slSubring_iff] at hM ⊢
  rw [Matrix.det_fin_two]
  exact (slSubring K L v).sub_mem ((slSubring K L v).mul_mem (hM 0 0) (hM 1 1))
    ((slSubring K L v).mul_mem (hM 0 1) (hM 1 0))

theorem mem_integralUnits_iff (u : (L ⊗[K] v.adicCompletion K)ˣ) :
    u ∈ integralUnits K L v ↔
      (u : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v ∧
        ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  Iff.rfl

theorem det_mem_integralUnits {k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hk : k ∈ semiLocalIntegralSet K L v) : Matrix.GeneralLinearGroup.det k ∈ integralUnits K L v := by
  rw [semiLocalIntegralSet, mem_integralUnitsSet] at hk
  rw [mem_integralUnits_iff]
  refine ⟨?_, ?_⟩
  · exact det_val_mem K L v hk.1
  · rw [← map_inv]
    exact det_val_mem K L v hk.2

theorem det_mul_inv_mem_integralUnits {a g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) :
    Matrix.GeneralLinearGroup.det g * (Matrix.GeneralLinearGroup.det a)⁻¹ ∈ integralUnits K L v := by
  obtain ⟨x, hx, k', hk', rfl⟩ := Set.mem_mul.1 hg
  obtain ⟨k, hk, a', ha', rfl⟩ := Set.mem_mul.1 hx
  rw [Set.mem_singleton_iff] at ha'
  rw [ha', map_mul, map_mul]
  have h : Matrix.GeneralLinearGroup.det k * Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det k' *
      (Matrix.GeneralLinearGroup.det a)⁻¹ =
      Matrix.GeneralLinearGroup.det k * Matrix.GeneralLinearGroup.det k' := by
    rw [mul_right_comm (Matrix.GeneralLinearGroup.det k) (Matrix.GeneralLinearGroup.det a)
      (Matrix.GeneralLinearGroup.det k'), mul_inv_cancel_right]
  rw [h]
  exact (integralUnits K L v).mul_mem (det_mem_integralUnits K L v hk) (det_mem_integralUnits K L v hk')

end Integral

end Blk408SuppDet

end

open Blk408SuppDet AutomorphicForm.TransversalMeasure in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) :
    ∃ C₀ : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact C₀ ∧
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∃ b : (AdeleRing (𝓞 K) K)ˣ,
        ∀ g : AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Matrix.GeneralLinearGroup.det g) * b ∈ C₀ := by
  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hN
  obtain ⟨-, hfin, -, -, hsurj, hbox, -, -⟩ :=
    NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L

  have hextract : ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      IsCompact (tsupport φa) ∧ ∀ v ∈ S, v ∉ T → IsCompact (tsupport (φS v)) := by
    intro ρ φ φf hfac
    refine ⟨hfac.1.2.isCompact, fun v hvS hvT => ?_⟩
    have h3 := hfac.2.2.1 v (Finset.mem_union_left T hvS)
    simp only [hvT, if_false] at h3
    exact h3.2.isCompact
  by_cases hcs : IsCompact (tsupport φa) ∧ ∀ v ∈ S, v ∉ T → IsCompact (tsupport (φS v))
  swap
  · exact ⟨∅, isCompact_empty, fun ρ φ φf hfac => absurd (hextract ρ φ φf hfac) hcs⟩
  obtain ⟨hφa, hφS⟩ := hcs

  set Dset : ∀ u : InfinitePlace K, Set (∀ w : u.Extension L, w.1.Completion)ˣ := fun u =>
    archFibre K L u '' (Matrix.GeneralLinearGroup.det '' tsupport φa) with hDset
  set Cset : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ := fun v =>
    if v ∈ S ∧ v ∉ T then Matrix.GeneralLinearGroup.det '' tsupport (φS v)
    else (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) with hCset
  have hD : ∀ u, IsCompact (Dset u) := fun u =>
    ((hφa.image (continuous_glDet _)).image (continuous_archFibre K L u))
  have hC : ∀ v, IsCompact (Cset v) := by
    intro v
    by_cases hv : v ∈ S ∧ v ∉ T
    · simp only [hCset, hv, and_self, if_true, not_false_eq_true]
      haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
      exact (hφS v hv.1 hv.2).image (continuous_glDet _)
    · simp only [hCset, hv, if_false]
      exact (hfin v).2.2.2.2.1
  have hCfin : {v : HeightOneSpectrum (𝓞 K) |
      Cset v ≠ (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite := by
    refine S.finite_toSet.subset fun v hv => ?_
    by_contra hvS
    apply hv
    have hn : ¬ (v ∈ S ∧ v ∉ T) := fun h => hvS h.1
    simp only [hCset, hn, if_false]
  set Box : Set (AdeleRing (𝓞 L) L)ˣ :=
    {t | (∀ u, archSemiLocalIdele K L u t ∈ Dset u) ∧ ∀ v, semiLocalIdele K L v t ∈ Cset v} with hBox
  have hBoxc : IsCompact Box := hbox Dset Cset hD hC hCfin
  refine ⟨N '' Box, hBoxc.image (continuous_idelicNorm K L), ?_⟩
  intro ρ φ φf hfac

  set a : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) := fun v =>
    semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)) with ha
  set x : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ := fun v =>
    if v ∈ T then (Matrix.GeneralLinearGroup.det (a v))⁻¹ else 1 with hx
  have hxT : ∀ v, v ∉ T → x v ∈ integralUnits K L v := by
    intro v hv
    simp only [hx, hv, if_false]
    exact (integralUnits K L v).one_mem
  obtain ⟨tρ, htρa, htρf⟩ := hsurj T (fun _ => 1) x hxT
  refine ⟨N tρ, fun g hg => ?_⟩
  rw [← map_mul]
  refine ⟨Matrix.GeneralLinearGroup.det g * tρ, ?_, rfl⟩

  obtain ⟨hφa', hφf, hΦ, hprod, hvan, hφeq⟩ := hfac
  have hne : φa (glArch (𝓞 L) L g) ≠ 0 ∧ φf (glFin (𝓞 L) L g) ≠ 0 := by
    rw [hφeq g] at hg
    exact ⟨left_ne_zero_of_mul hg, right_ne_zero_of_mul hg⟩
  set h := glFin (𝓞 L) L g with hh
  have hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
    by_contra hcon
    push Not at hcon
    exact hne.2 (hvan h hcon)
  have hprodne : ∀ v ∈ S ∪ T,
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
              semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
        else φS v) v (semiLocalComponent K L v h) ≠ 0 := by
    have h1 := hne.2
    rw [hprod h hint] at h1
    exact fun v hv => Finset.prod_ne_zero_iff.1 h1 v hv
  refine ⟨fun u => ?_, fun v => ?_⟩
  ·
    rw [map_mul, htρa u, mul_one, archSemiLocalIdele_det]
    exact ⟨_, ⟨_, subset_tsupport _ (Function.mem_support.2 hne.1), rfl⟩, rfl⟩
  ·
    rw [map_mul, htρf v, semiLocalIdele_det]
    by_cases hvT : v ∈ T
    · have hv := hprodne v (Finset.mem_union_right S hvT)
      simp only [hvT, if_true] at hv
      have hmem := Set.mem_of_indicator_ne_zero hv
      have hCv : Cset v = (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
        have hn : ¬ (v ∈ S ∧ v ∉ T) := fun h' => h'.2 hvT
        simp only [hCset, hn, if_false]
      rw [hCv]
      simp only [hx, hvT, if_true]
      exact det_mul_inv_mem_integralUnits K L v hmem
    · simp only [hx, hvT, if_false, mul_one]
      by_cases hvS : v ∈ S
      · have hv := hprodne v (Finset.mem_union_left T hvS)
        simp only [hvT, if_false] at hv
        have hCv : Cset v = Matrix.GeneralLinearGroup.det '' tsupport (φS v) := by
          simp only [hCset, hvS, hvT, not_false_eq_true, and_self, if_true]
        rw [hCv]
        exact ⟨_, subset_tsupport _ (Function.mem_support.2 hv), rfl⟩
      · have hvST : v ∉ S ∪ T := by
          rw [Finset.mem_union, not_or]; exact ⟨hvS, hvT⟩
        have hCv : Cset v = (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
          have hn : ¬ (v ∈ S ∧ v ∉ T) := fun h' => hvS h'.1
          simp only [hCset, hn, if_false]
        rw [hCv]
        exact det_mem_integralUnits K L v (hint v hvST)

end S_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset (solution)
