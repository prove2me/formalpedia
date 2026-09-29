-- Prove2me | solution 1 for AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cfa54e5a-0311-5d03-a9b2-658fe83361fb

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
import Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted
import Theorems.Thm_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel semiLocalIntegralSet IsOrbitalIntegralOn AreMatchingLocal IsUnitFactorizableAboveOfType AreMatchingAt IsUnitFactorizableOfTypeAt IsLocalTestFn localIntegralSet localGLBorel localHaar localCentralizer localCentralizerBorel IsOrbitalIntegral IsArchTestFactor IsFinTestFactor ArchTypeFamily AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup HeckeEigensystem.cNorm HeckeEigensystem satakePow satakePow_zero satakePow_add_two sigmaAdelicAct centralCell ellipticCell adelicKernelCentralPart adelicKernelEllipticPart SatakeCombination.slotDeg SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff WindingDatum sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted"
namespace WindingDatum
p2m_export "AutomorphicForm.WindingDatum" "fibreCoeff coeff lam s hΨc hΨd χ hsum Λ hω θ₀ hΛ m hpf Ψ hΨhatd x₀ ω hsub mk hΨi n₀ C sub"
p2m_open "AutomorphicForm.WindingDatum AutomorphicForm"

variable {r d c : ℕ}

private noncomputable def _root_.AutomorphicForm.WindingDatum.scale (κ : ℂ) (𝒟 : WindingDatum r d c) : WindingDatum r d c where
  Λ := 𝒟.Λ
  hΛ := 𝒟.hΛ
  s := 𝒟.s
  ω := 𝒟.ω
  hω := 𝒟.hω
  hpf := 𝒟.hpf
  χ := 𝒟.χ
  sub := 𝒟.sub
  hsub := 𝒟.hsub
  Ψ := 𝒟.Ψ
  hΨc := 𝒟.hΨc
  hΨi := 𝒟.hΨi
  C := 𝒟.C
  hΨd := 𝒟.hΨd
  hΨhatd := 𝒟.hΨhatd
  m := 𝒟.m
  θ₀ := 𝒟.θ₀
  x₀ := 𝒟.x₀
  n₀ := 𝒟.n₀
  lam := fun i => κ * 𝒟.lam i
  hsum := by
    have h := 𝒟.hsum.mul_left ‖κ‖
    refine h.congr fun i => ?_
    rw [norm_mul, mul_assoc]

p2m_export "AutomorphicForm.WindingDatum" "scale"
theorem fibreCoeff_scale (κ : ℂ) (𝒟 : WindingDatum r d c) (i : ℕ) (n : Fin d → ℤ) :
    (𝒟.scale κ).fibreCoeff i n = 𝒟.fibreCoeff i n := rfl

theorem coeff_scale (κ : ℂ) (𝒟 : WindingDatum r d c) (n : Fin d → ℤ) :
    (𝒟.scale κ).coeff n = κ * 𝒟.coeff n := by
  unfold coeff
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [fibreCoeff_scale]
  show κ * 𝒟.lam i * 𝒟.fibreCoeff i n = κ * (𝒟.lam i * 𝒟.fibreCoeff i n)
  ring

end AutomorphicForm.WindingDatum

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel semiLocalIntegralSet IsOrbitalIntegralOn AreMatchingLocal IsUnitFactorizableAboveOfType AreMatchingAt IsUnitFactorizableOfTypeAt IsLocalTestFn localIntegralSet localGLBorel localHaar localCentralizer localCentralizerBorel IsOrbitalIntegral IsArchTestFactor IsFinTestFactor ArchTypeFamily AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup HeckeEigensystem.cNorm HeckeEigensystem satakePow satakePow_zero satakePow_add_two sigmaAdelicAct centralCell ellipticCell adelicKernelCentralPart adelicKernelEllipticPart SatakeCombination.slotDeg SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff WindingDatum sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted"
namespace WindingDatum
p2m_export "AutomorphicForm.WindingDatum" "fibreCoeff coeff lam s hΨc hΨd χ hsum Λ hω θ₀ hΛ m hpf Ψ hΨhatd x₀ ω hsub mk hΨi n₀ C sub"
p2m_open "AutomorphicForm.WindingDatum AutomorphicForm"

noncomputable def zero (r d c : ℕ) (hd : d ≠ 0) : WindingDatum r d c where
  Λ := ⊥
  hΛ := Subsingleton.discreteTopology
  s := 0
  ω := fun _ => 1
  hω := by
    intro h
    obtain ⟨i⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    exact one_ne_zero (congr_fun h i)
  hpf := by
    intro x hx
    rw [AddSubgroup.mem_bot] at hx
    subst hx
    simp
  χ := 0
  sub := fun _ => ⊥
  hsub := fun _ => le_rfl
  Ψ := fun _ _ => 0
  hΨc := fun _ => continuous_const
  hΨi := fun _ => integrable_zero _ _ _
  C := fun _ => 0
  hΨd := fun _ _ => by simp
  hΨhatd := fun _ _ => by simp
  m := fun _ _ => 0
  θ₀ := fun _ _ => 0
  x₀ := fun _ _ => 0
  n₀ := fun _ _ => 0
  lam := fun _ => 0
  hsum := by simpa using summable_zero

theorem coeff_zero (r d c : ℕ) (hd : d ≠ 0) (n : Fin d → ℤ) : (zero r d c hd).coeff n = 0 := by
  unfold coeff
  simp [zero]

end AutomorphicForm.WindingDatum

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel semiLocalIntegralSet IsOrbitalIntegralOn AreMatchingLocal IsUnitFactorizableAboveOfType AreMatchingAt IsUnitFactorizableOfTypeAt IsLocalTestFn localIntegralSet localGLBorel localHaar localCentralizer localCentralizerBorel IsOrbitalIntegral IsArchTestFactor IsFinTestFactor ArchTypeFamily AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup HeckeEigensystem.cNorm HeckeEigensystem satakePow satakePow_zero satakePow_add_two sigmaAdelicAct centralCell ellipticCell adelicKernelCentralPart adelicKernelEllipticPart SatakeCombination.slotDeg SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff WindingDatum sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted"
p2m_open "AutomorphicForm"

theorem map_satakePow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    ∀ (n : ℕ) (s e : R), φ (satakePow n s e) = satakePow n (φ s) (φ e)
  | 0, s, e => by rw [satakePow_zero, satakePow_zero]; exact map_ofNat φ 2
  | 1, s, e => by simp [satakePow]
  | n + 2, s, e => by
    rw [satakePow_add_two, satakePow_add_two, map_sub, map_mul, map_mul, map_satakePow φ (n + 1),
      map_satakePow φ n]

theorem satakePow_two_one : ∀ n : ℕ, satakePow n (2 : ℂ) 1 = 2
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [satakePow_add_two, satakePow_two_one (n + 1), satakePow_two_one n]
    norm_num

namespace SatakeCombination
p2m_export "AutomorphicForm.SatakeCombination" "univWord slotDeg slotIndex slotFamilyCoeff"
p2m_open "AutomorphicForm.SatakeCombination"

theorem univWord_ne_zero (n k j : ℕ) : univWord n k j ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (![2, 1] : Fin 2 → ℂ)) h
  rw [univWord, map_mul, map_pow, map_pow, map_pow, map_satakePow, MvPolynomial.eval_X, MvPolynomial.eval_X,
    map_zero] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, satakePow_two_one, one_pow, mul_one] at h2
  exact absurd h2 (pow_ne_zero _ two_ne_zero)

theorem slotIndex_nonempty (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) (k j : HeightOneSpectrum (𝓞 K) → ℕ)
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (slotIndex K L ws k j T).Nonempty :=
  Finset.pi_nonempty.mpr fun v _ => MvPolynomial.support_nonempty.mpr (univWord_ne_zero _ _ _)

end SatakeCombination

end AutomorphicForm

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff.AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (T : Finset (HeightOneSpectrum (𝓞 K))) (hTdisj : Disjoint T SK) (hT2 : 2 ≤ T.card)
    (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hw' : ∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal)
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖirr : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T, algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hϖKirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (hNw' : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm (w' v).asIdeal)
    (hNwf' : ∀ v ∈ T, Ideal.absNorm (w' v).asIdeal =
      Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hs : ∀ v ∈ T, s v ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hxK : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (κ₀K κK : ℝ) (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    (κm : ℂ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card),
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
      (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
      (hfam : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
          AutomorphicForm.IsFinTestFactor K ff ∧
          (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
            (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ AutomorphicForm.localIntegralSet K v) →
              ff h = ∏ v ∈ SK ∪ T,
                (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                    ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                        (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                  else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
          (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
            (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ AutomorphicForm.localIntegralSet K v) →
              ff h = 0) ∧
          ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
      (ΔK : Finset (GL (Fin 2) K))
      (hΔK : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
      (hΔKinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK,
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
          (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
      (τK : ∀ γ : GL (Fin 2) K,
        Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
      (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
      (hτKc : ∀ γ ∈ ΔK, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
        ∫ t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
            g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τK γ) =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
      (IK : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
      (hIK : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ γ ∈ ΔK,
        ∀ z : (AdeleRing (𝓞 K) K)ˣ,
          AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
            (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g))
            (IK m γ z))

      (hΔKc : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ u : Kˣ, (u : K) ≠ 1 →
        (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
          ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
            fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0)
      , κm * (∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK, (κ₀K : ℂ) *
            (((κK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK)) =
        ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * 𝒜.coeff n := by
  classical

  obtain ⟨PZ, hPo, hPp, hPν⟩ :=
    NumberField.Idele.exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt K SK νZK

  have hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) :=
    fun ξ hξ => ((hΞ ξ).mp hξ).1
  have hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1 := fun ξ hξ => ((hΞ ξ).mp hξ).2.1
  have hζ : ∀ v ∈ T, (fun v => ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) v ≠ 0 := fun v _ => Units.ne_zero _

  obtain ⟨𝒜₀, h𝒜₀⟩ :=
    AutomorphicForm.exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted
      K L ws νZK Ξ hΞc hΞt SK T hTdisj hT2 hur (fun v => Ideal.absNorm (w' v).asIdeal) hNw' hNwf' (fun v => ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) s hζ hs hxK faK hfaK fSK hfSK κ₀K κK νA cG
      hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT PZ hPo hPp hPν IA hIA IF hIF
  refine ⟨𝒜₀.scale κm, ?_⟩
  intro ks js fam hfam ΔK hΔK hΔKinj τK hτK hτKc IK hIK hΔKc

  have hK6 :=
    AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
      K L ws νZK Ξ hΞc hΞt SK T hTdisj hur ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs ks js (fun v => Ideal.absNorm (w' v).asIdeal) hNw' hNwf' (fun v => ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) s hζ hs
      hxK faK hfaK fSK hfSK fam hfam ΔK hΔK hΔKinj cτK hcτK τK hτK hτKc IK hIK hΔKc κ₀K κK νA cG hG τG hτG hτGc τA hτA
      τF hτF hτF1 cT hcT hT PZ hPo hPp hPν IA hIA IF hIF _ _ 𝒜₀ h𝒜₀
  beta_reduce at hK6
  rw [hK6, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [AutomorphicForm.WindingDatum.coeff_scale]
  ring

end S_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff
end P2MW
export P2MW.S_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff (solution)
