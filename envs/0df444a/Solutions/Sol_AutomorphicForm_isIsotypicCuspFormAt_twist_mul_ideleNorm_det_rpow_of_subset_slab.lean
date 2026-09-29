-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cbfad1ca-450a-5027-84bc-6f7088d7843c

import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel MeasureTheory FLT.SmoothVectors

namespace TwistForm
variable (K : Type) [Field K] [NumberField K]

theorem det_fst_apply (g : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w =
      ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := by
  have h1 : ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
          (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* w.Completion) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_snd_eq (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)).det := by
  have h1 : ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
          (RingHom.id (AdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem ideleNorm_det_eq_one (u : AdelicGL2 (𝓞 K) K) (harch : glArch (𝓞 K) K u = 1)
    (hint : ∀ i j, ((glFin (𝓞 K) K u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hint' : ∀ i j, (((glFin (𝓞 K) K u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) = 1 := by
  have hdet2 : ∀ g' : AdelicGL2 (𝓞 K) K, (∀ i j, ((glFin (𝓞 K) K g' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) →
      ∀ v : HeightOneSpectrum (𝓞 K),
        ((Matrix.GeneralLinearGroup.det g' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈
          v.adicCompletionIntegers K := by
    intro g' h v
    rw [det_snd_eq K g', Matrix.det_fin_two]
    exact sub_mem (mul_mem (h 0 0 v) (h 1 1 v)) (mul_mem (h 0 1 v) (h 1 0 v))
  refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K _ ?_ ?_
  · funext v
    rw [det_fst_apply K, harch]
    show ((AdelicLevel.archComponent K v (1 : GL (Fin 2) (InfiniteAdeleRing K)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det = 1
    rw [map_one, Units.val_one, Matrix.det_one]
  · rw [FiniteAdeleRing.mem_unitIdeles_iff]
    refine ⟨fun v => hdet2 u hint v, fun v => ?_⟩
    rw [← map_inv]
    have : ((Matrix.GeneralLinearGroup.det u)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) = Matrix.GeneralLinearGroup.det u⁻¹ := by
      rw [map_inv]
    rw [this]
    refine hdet2 u⁻¹ (fun i j => ?_) v
    simpa only [map_inv] using hint' i j

theorem ideleNorm_det_eq_one_of_mem (N : Ideal (𝓞 K)) (u : AdelicGL2 (𝓞 K) K)
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) = 1 := by
  have h12 := Subgroup.mem_inf.mp hu
  have hpl : u ∈ levelOne (𝓞 K) K N := (Subgroup.mem_inf.mp h12.1).1
  have h1 : glFin (𝓞 K) K u ∈ finiteLevelOne (𝓞 K) K N := mem_levelOne_iff.mp hpl
  exact ideleNorm_det_eq_one K u ((mem_finiteAdelicGL2Subgroup_iff K u).mp h12.2)
    h1.1.integral h1.2.integral

noncomputable def mult (s : ℝ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s : ℝ) : ℂ)

theorem mult_mul (s : ℝ) (g h : AdelicGL2 (𝓞 K) K) : mult K s (g * h) = mult K s g * mult K s h := by
  simp only [mult, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  rw [Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le,
    Complex.ofReal_mul]

theorem mult_eq_one_of (s : ℝ) {u : AdelicGL2 (𝓞 K) K}
    (hu : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) = 1) : mult K s u = 1 := by
  simp only [mult, hu, Real.one_rpow, Complex.ofReal_one]

theorem mult_ne_zero (s : ℝ) (g : AdelicGL2 (𝓞 K) K) : mult K s g ≠ 0 := by
  simp only [mult, ne_eq, Complex.ofReal_eq_zero]
  exact (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _).ne'

theorem continuous_mult (s : ℝ) : Continuous (mult K s) := by
  unfold mult
  refine Complex.continuous_ofReal.comp ?_
  exact (NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const fun g => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'

theorem mult_globalPoints_mul (s : ℝ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    mult K s (globalPoints (𝓞 K) K γ * g) = mult K s g := by
  rw [mult_mul, mult_eq_one_of K s (AutomorphicForm.ideleNorm_det_globalPoints γ), one_mul]

theorem det_unipotentGL2' {A : Type*} [CommRing A] (x : A) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

theorem mult_unipotentGL2_mul (s : ℝ) (q : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    mult K s (unipotentGL2 q * g) = mult K s g := by
  rw [mult_mul]
  have : mult K s (unipotentGL2 q) = 1 := by
    simp only [mult, det_unipotentGL2', (NumberField.TateGlobal.mem_normOneIdeles_iff _).mp (Subgroup.one_mem _),
      Real.one_rpow, Complex.ofReal_one]
  rw [this, one_mul]

theorem mult_centralScalar_mul (s : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    mult K s (centralScalar (𝓞 K) K z * g) =
      (((NumberField.TateGlobal.ideleNorm K z) ^ s : ℝ) : ℂ) ^ 2 * mult K s g := by
  rw [mult_mul]
  congr 1
  simp only [mult, det_centralScalar K, sq, NumberField.TateGlobal.ideleNorm_mul,
    Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le,
    Complex.ofReal_mul]

end TwistForm

open AutomorphicForm TwistForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦdet : ∃ α β : ℝ, 0 < α ∧
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (-w) : ℝ) : ℂ))
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π φ) :
    IsIsotypicCuspFormAt K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK
      (π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)))
      (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) := by
  classical
  set P := (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) with hP
  set s : ℝ := -(w / 2) with hs
  have hψ : (fun g : AdelicGL2 (𝓞 K) K => φ g *
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) =
      fun g => φ g * mult K s g := rfl
  rw [hψ]

  have hsc := hφ.smoothCusp
  have hcusp : IsCuspAutomorphicFnAt K P ξK φ := hsc.1
  have hKf : IsKfSmooth K φ := hsc.2
  have hauto : IsAutomorphicFnAt K P ξK φ := hcusp.1
  have hcuspidal := hcusp.2
  have hls := (lsXiMemberAt_iff (𝓞 K) K P.μ P.Z ξK P.D φ).mp hauto
  have hχ : ∀ v, (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)) v = mult K s (heckeGen (𝓞 K) K v) := fun v => rfl

  have hmultKf : IsKfSmooth K (mult K s) := by
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
    let V : Subgroup ↥(finiteAdelicGL2Subgroup K) :=
      (finiteIntegralGL2 (𝓞 K) K).comap ((glFin (𝓞 K) K).comp (finiteAdelicGL2Subgroup K).subtype)
    have hVopen : IsOpen (V : Set ↥(finiteAdelicGL2Subgroup K)) :=
      (isOpen_finiteLevelZero (𝓞 K) K (N := ⊤) top_ne_bot).preimage
        ((continuous_glFin (𝓞 K) K).comp continuous_subtype_val)
    refine Subgroup.isOpen_mono ?_ hVopen
    intro k hk
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    have hk' := mem_finiteIntegralGL2_iff.mp hk
    rw [mult_mul, mult_eq_one_of K s (ideleNorm_det_eq_one K (k : AdelicGL2 (𝓞 K) K)
      ((mem_finiteAdelicGL2Subgroup_iff K _).mp k.2) hk'.1 hk'.2), mul_one]

  obtain ⟨α, β, hα, hΦsub⟩ := hΦdet
  set C : ℝ := max (α ^ s) (β ^ s) with hC
  have hbound : ∀ g ∈ Φ, ‖mult K s g‖ ≤ C := by
    intro g hg
    obtain ⟨h1, h2⟩ := hΦsub hg
    simp only [mult, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _)]
    rcases le_or_gt 0 s with hs0 | hs0
    · exact (Real.rpow_le_rpow (NumberField.TateGlobal.ideleNorm_pos _).le h2 hs0).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hα h1 hs0.le).trans (le_max_left _ _)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, (hφ.continuous.mul (continuous_mult K s)), ?_, ?_, ?_⟩
  ·
    refine (lsXiMemberAt_iff (𝓞 K) K P.μ P.Z ξ₀K P.D _).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
    · show φ (globalPoints (𝓞 K) K γ * g) * mult K s (globalPoints (𝓞 K) K γ * g) = φ g * mult K s g
      rw [hls.1.left_invariant γ g, mult_globalPoints_mul]
    · show φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) * mult K s (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) =
        ((ξ₀K z : ℂˣ) : ℂ) * (φ g * mult K s g)
      have hz : ((ξ₀K z : ℂˣ) : ℂ) = ((ξK z : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ (-w) : ℝ) : ℂ) := hξ₀ z
      have hsq : (((NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ s : ℝ) : ℂ) ^ 2 =
          (((NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ (-w) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (NumberField.TateGlobal.ideleNorm_pos _).le]
        congr 2; push_cast; rw [hs]; ring
      have hct := hls.1.central_transform z g
      calc φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) *
            mult K s (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g)
          = (((ξK z : ℂˣ) : ℂ) * φ g) * ((((NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ s : ℝ) : ℂ) ^ 2 *
              mult K s g) := by rw [hct, mult_centralScalar_mul]; rfl
        _ = (((ξK z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ (-w) : ℝ) : ℂ)) *
              (φ g * mult K s g) := by rw [hsq]; ring
        _ = ((ξ₀K z : ℂˣ) : ℂ) * (φ g * mult K s g) := by rw [hz]
    ·
      have hmem : MemLp φ 2 (P.μ.restrict P.D) := hls.2
      have hmeas : AEStronglyMeasurable (fun g => φ g * mult K s g) (P.μ.restrict P.D) := by
        haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
        exact (hφ.continuous.mul (continuous_mult K s)).aestronglyMeasurable
      refine MemLp.of_le_mul (c := C) hmem hmeas ?_
      have hS : MeasurableSet {g : AdelicGL2 (𝓞 K) K |
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
        NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
      have hae : ∀ᵐ g ∂(P.μ.restrict P.D), g ∈ {g : AdelicGL2 (𝓞 K) K |
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
        (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hΦsub le_rfl)).ae_le (ae_restrict_mem hS)
      filter_upwards [hae] with g hg
      rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      obtain ⟨h1, h2⟩ := hg
      simp only [mult, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _)]
      rcases le_or_gt 0 s with hs0 | hs0
      · exact (Real.rpow_le_rpow (NumberField.TateGlobal.ideleNorm_pos _).le h2 hs0).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos hα h1 hs0.le).trans (le_max_left _ _)
  ·
    intro g
    have h0 := hcuspidal g
    unfold constantTerm constantTermIntegrand at h0 ⊢
    simp only [mult_unipotentGL2_mul]
    rw [integral_mul_const, h0, zero_mul]
  ·
    exact isSmoothVector_rightTranslationFn_mul hKf hmultKf
  ·
    intro g u hu
    show φ (g * u) * mult K s (g * u) = φ g * mult K s g
    rw [hφ.level_invariant g u hu, mult_mul, mult_eq_one_of K s (ideleNorm_det_eq_one_of_mem K N u hu), mul_one]
  ·
    intro v hv
    obtain ⟨reps, hsys, hsum⟩ := hφ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    have hrep : ∀ i, mult K s (reps i) = mult K s (heckeGen (𝓞 K) K v) := by
      intro i
      obtain ⟨u₁, hu₁, u₂, hu₂, he⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
      rw [← he, mult_mul, mult_mul, mult_eq_one_of K s (ideleNorm_det_eq_one_of_mem K N u₁ hu₁),
        mult_eq_one_of K s (ideleNorm_det_eq_one_of_mem K N u₂ hu₂), one_mul, mul_one]
      rfl
    have hsum' := hsum g
    unfold SmoothCusp.heckeCosetSum at hsum' ⊢
    show ∑ i, φ (g * reps i) * mult K s (g * reps i) = (π.twist _).a v * (φ g * mult K s g)
    simp_rw [mult_mul, hrep]
    rw [← Finset.sum_mul, hsum', HeckeEigensystem.twist_a]
    simp only [mult]
    ring
  ·
    intro v hv g
    have hce : φ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g) =
        π.toRawCentral.b v * φ g := hφ.central_eigen v hv g
    show φ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g) *
        mult K s (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g) =
      (HeckeEigensystem.cNorm v)⁻¹ * (mult K s (heckeGen (𝓞 K) K v) ^ 2 * π.b v) * (φ g * mult K s g)
    rw [hce, mult_centralScalar_mul]
    show (HeckeEigensystem.cNorm v)⁻¹ * π.b v * φ g * ((((NumberField.TateGlobal.ideleNorm K
        (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ s : ℝ) : ℂ) ^ 2 * mult K s g) = _
    simp only [mult]
    ring

end S_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab (solution)
