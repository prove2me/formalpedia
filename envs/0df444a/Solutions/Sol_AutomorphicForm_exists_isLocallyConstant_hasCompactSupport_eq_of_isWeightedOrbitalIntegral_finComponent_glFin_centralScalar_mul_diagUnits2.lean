-- Prove2me | solution 1 for AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f7b3de7b-c258-58c9-a128-5ee6f6a36cf2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
import Theorems.Thm_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace S4aux

open MeasureTheory
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem transportHaar {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Set G) {H₁ H₂ : Subgroup G} (h : H₁ = H₂)
    (τ : @Measure H₁ (borel H₁)) (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ)
    (hτ1 : τ (Subtype.val ⁻¹' S) = 1) :
    ∃ τ₂ : @Measure H₂ (borel H₂), @Measure.IsHaarMeasure H₂ _ _ (borel H₂) τ₂ ∧ τ₂ (Subtype.val ⁻¹' S) = 1 := by
  subst h
  exact ⟨τ, hτ, hτ1⟩

theorem transportW (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {γ₁ γ₂ : GL (Fin 2) (v.adicCompletion K)} (h : γ₁ = γ₂)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ₁) (AutomorphicForm.localCentralizerBorel K v γ₁))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₁) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v γ₁ τ f J) :
    ∃ τ₂ : @Measure (AutomorphicForm.localCentralizer K v γ₂) (AutomorphicForm.localCentralizerBorel K v γ₂),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₂) τ₂ ∧
      τ₂ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 ∧
      AutomorphicForm.IsWeightedOrbitalIntegral K v γ₂ τ₂ f J := by
  subst h
  exact ⟨τ, hτ, hτ1, hJ⟩

theorem local_core (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (uv : (v.adicCompletion K)ˣ) (huv1 : (uv : (v.adicCompletion K)) ≠ 1) :
    ∃ F : (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant F ∧ HasCompactSupport F ∧
      ∀ (b : (v.adicCompletion K)ˣ)
        (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1))
          (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1))),
        @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1)) τ →
        τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
        ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1) τ fv J → J = F b := by
  classical
  obtain ⟨hlc, hcs⟩ := hfv

  let γb : (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K) := fun b =>
    Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1
  have hγb : ∀ b : (v.adicCompletion K)ˣ, ((γb b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(b : (v.adicCompletion K)) * (uv : (v.adicCompletion K)), (b : (v.adicCompletion K))] := by
    intro b
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1 : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]
  have hreg : ∀ b : (v.adicCompletion K)ˣ, AutomorphicForm.IsRegularSemisimple (γb b) := by
    intro b
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, hγb b, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ((b : (v.adicCompletion K)) * (uv : (v.adicCompletion K)) + (b : (v.adicCompletion K))) ^ 2 - 4 * ((b : (v.adicCompletion K)) * (uv : (v.adicCompletion K)) * (b : (v.adicCompletion K)) - 0 * 0) =
        ((b : (v.adicCompletion K)) * ((uv : (v.adicCompletion K)) - 1)) ^ 2 by ring]
    exact pow_ne_zero 2 (mul_ne_zero b.ne_zero (sub_ne_zero.mpr huv1))
  have h01 : ∀ b : (v.adicCompletion K)ˣ, ((γb b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := fun b => by
    rw [hγb b]; exact Matrix.diagonal_apply_ne _ (by decide)
  have h10 : ∀ b : (v.adicCompletion K)ˣ, ((γb b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := fun b => by
    rw [hγb b]; exact Matrix.diagonal_apply_ne _ (by decide)

  let P : (v.adicCompletion K)ˣ → ℂ → Prop := fun b J =>
    ∃ τ : @Measure (AutomorphicForm.localCentralizer K v (γb b)) (AutomorphicForm.localCentralizerBorel K v (γb b)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (γb b)) τ ∧
      τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 ∧
      AutomorphicForm.IsWeightedOrbitalIntegral K v (γb b) τ fv J
  let F : (v.adicCompletion K)ˣ → ℂ := fun b => if h : ∃ J, P b J then h.choose else 0
  have huniq : ∀ (b : (v.adicCompletion K)ˣ) (J₁ J₂ : ℂ), P b J₁ → P b J₂ → J₁ = J₂ := by
    intro b J₁ J₂ h1 h2
    obtain ⟨τ₁, h₁, h₁1, hJ₁⟩ := h1
    obtain ⟨τ₂, h₂, h₂1, hJ₂⟩ := h2
    exact AutomorphicForm.eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
      K v (γb b) (hreg b) (h01 b) (h10 b) τ₁ τ₂ h₁ h₂ h₁1 h₂1 fv ⟨hlc, hcs⟩ J₁ J₂ hJ₁ hJ₂
  have hF : ∀ (b : (v.adicCompletion K)ˣ) (J : ℂ), P b J → F b = J := by
    intro b J hJ
    have hex : ∃ J, P b J := ⟨J, hJ⟩
    simp only [F, dif_pos hex]
    exact huniq b _ _ hex.choose_spec hJ
  have hF0 : ∀ b : (v.adicCompletion K)ˣ, (¬ ∃ J, P b J) → F b = 0 := by
    intro b h
    simp only [F, dif_neg h]

  have hscal : ∀ c : (v.adicCompletion K)ˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (c : (v.adicCompletion K)) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro c
    rw [Matrix.smul_one_eq_diagonal]
    ext i j
    simp [Matrix.diagonal]
  have hcomm : ∀ (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)),
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    intro c x
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hscal, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hval : Continuous fun c : (v.adicCompletion K)ˣ =>
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    have e : (fun c : (v.adicCompletion K)ˣ =>
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
        fun c : (v.adicCompletion K)ˣ => ((c : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
      funext fun c => hscal c
    rw [e]
    exact Units.continuous_val.smul continuous_const
  have hscalc : Continuous fun c : (v.adicCompletion K)ˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    show Continuous fun c : (v.adicCompletion K)ˣ =>
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    have e : (fun c : (v.adicCompletion K)ˣ =>
        (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
        (fun c : (v.adicCompletion K)ˣ =>
          ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ∘
          fun c : (v.adicCompletion K)ˣ => c⁻¹ := by
      funext c
      simp only [Function.comp_apply, map_inv]
    rw [e]
    exact hval.comp continuous_inv

  obtain ⟨W, hWo, h1W, hW⟩ :=
    IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport fv hlc hcs
  let V : Set (v.adicCompletion K)ˣ := (fun c : (v.adicCompletion K)ˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) c) ⁻¹' W
  have hVo : IsOpen V := hWo.preimage hscalc
  have h1V : (1 : (v.adicCompletion K)ˣ) ∈ V := by
    show Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (v.adicCompletion K)ˣ) ∈ W
    rwa [map_one]

  have hshift : ∀ c ∈ V, ∀ (b : (v.adicCompletion K)ˣ) (J : ℂ), P b J → P (c * b) J := by
    intro c hc b J hP
    obtain ⟨τ, hτ, hτ1, hJ⟩ := hP
    have hfc : (fun x => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) = fv :=
      funext fun x => (hW x _ hc).2
    have key : ∀ x : GL (Fin 2) (v.adicCompletion K), x * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * (x * γb b) := fun x => by
      rw [← mul_assoc, ← hcomm c x, mul_assoc]
    have hcen : AutomorphicForm.localCentralizer K v (γb b) =
        AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b) := by
      ext x
      constructor
      · intro h
        have h' := Subgroup.mem_centralizer_singleton_iff.mp h
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc x * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b)
            = Matrix.GeneralLinearGroup.scalar (Fin 2) c * (x * γb b) := key x
          _ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * (γb b * x) := by rw [h']
          _ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b * x :=
            (mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (γb b) x).symm
      · intro h
        have h' := Subgroup.mem_centralizer_singleton_iff.mp h
        refine Subgroup.mem_centralizer_singleton_iff.mpr (mul_left_cancel (a := Matrix.GeneralLinearGroup.scalar (Fin 2) c) ?_)
        calc Matrix.GeneralLinearGroup.scalar (Fin 2) c * (x * γb b)
            = x * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b) := (key x).symm
          _ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b * x := h'
          _ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * (γb b * x) :=
            mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (γb b) x
    obtain ⟨τ'', hτ'', hτ''1⟩ := S4aux.transportHaar (AutomorphicForm.localIntegralSet K v) hcen τ hτ hτ1
    have h2 := (AutomorphicForm.isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
      K v (γb b) c τ hτ hτ1 τ'' hτ'' hτ''1 fv).2 J (by rw [hfc]; exact hJ)
    have hγ : Matrix.GeneralLinearGroup.scalar (Fin 2) c * γb b = γb (c * b) := by
      show Matrix.GeneralLinearGroup.scalar (Fin 2) c * (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 uv 1) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (c * b) * diagUnits2 uv 1
      rw [map_mul, mul_assoc]
    obtain ⟨τ₃, hτ₃, hτ₃1, hJ₃⟩ := S4aux.transportW K v hγ τ'' hτ'' hτ''1 fv J h2
    exact ⟨τ₃, hτ₃, hτ₃1, hJ₃⟩
  have hFshift : ∀ c ∈ V, c⁻¹ ∈ V → ∀ b : (v.adicCompletion K)ˣ, F (c * b) = F b := by
    intro c hc hc' b
    by_cases hex : ∃ J, P b J
    · obtain ⟨J, hJ⟩ := hex
      rw [hF b J hJ, hF (c * b) J (hshift c hc b J hJ)]
    · have hex' : ¬ ∃ J, P (c * b) J := by
        rintro ⟨J, hJ⟩
        apply hex
        refine ⟨J, ?_⟩
        have h3 := hshift c⁻¹ hc' (c * b) J hJ
        rwa [inv_mul_cancel_left] at h3
      rw [hF0 b hex, hF0 (c * b) hex']
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_exists_open]
    intro b
    refine ⟨(fun c : (v.adicCompletion K)ˣ => c * b) '' (V ∩ (fun c : (v.adicCompletion K)ˣ => c⁻¹) ⁻¹' V), ?_, ?_, ?_⟩
    · exact (Homeomorph.mulRight b).isOpenMap _ (hVo.inter (hVo.preimage continuous_inv))
    · exact ⟨1, ⟨h1V, show (1 : (v.adicCompletion K)ˣ)⁻¹ ∈ V by rwa [inv_one]⟩, one_mul b⟩
    · rintro _ ⟨c, ⟨hc, hc'⟩, rfl⟩
      exact hFshift c hc hc' b

  have hdet : ∀ b : (v.adicCompletion K)ˣ, Matrix.GeneralLinearGroup.det (γb b) = b * uv * b := by
    intro b
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hγb b, Matrix.det_fin_two]
    simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_mul]
    ring
  set D : Set (v.adicCompletion K)ˣ := Matrix.GeneralLinearGroup.det '' tsupport fv with hD
  have hDc : IsCompact D := hcs.image Matrix.GeneralLinearGroup.continuous_det
  have hsuppD : ∀ b : (v.adicCompletion K)ˣ, F b ≠ 0 → b * uv * b ∈ D := by
    intro b hb
    by_cases hex : ∃ J, P b J
    swap
    · exact absurd (hF0 b hex) hb
    obtain ⟨J, hJ⟩ := hex
    rw [hF b J hJ] at hb
    obtain ⟨τ, -, -, s, -, hJs⟩ := hJ
    by_contra hD'
    apply hb
    rw [hJs]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    have hx : fv (x⁻¹ * γb b * x) = 0 := by
      by_contra hne
      apply hD'
      refine ⟨x⁻¹ * γb b * x, subset_tsupport _ hne, ?_⟩
      rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul, hdet]
    simp only [Pi.zero_apply, hx, zero_mul]
  obtain ⟨M, hM⟩ := hDc.exists_bound_of_continuousOn (f := fun d : (v.adicCompletion K)ˣ => (d : (v.adicCompletion K)))
    Units.continuous_val.continuousOn
  obtain ⟨M', hM'⟩ := hDc.exists_bound_of_continuousOn (f := fun d : (v.adicCompletion K)ˣ => ((d⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)))
    Units.continuous_coe_inv.continuousOn
  have huv0 : 0 < ‖(uv : (v.adicCompletion K))‖ := norm_pos_iff.mpr uv.ne_zero
  let R : ℝ := max 1 (M / ‖(uv : (v.adicCompletion K))‖)
  let R' : ℝ := max 1 (M' * ‖(uv : (v.adicCompletion K))‖)
  let Box : Set (v.adicCompletion K)ˣ := Units.embedProduct (v.adicCompletion K) ⁻¹'
    (Metric.closedBall 0 R ×ˢ (MulOpposite.opHomeomorph '' Metric.closedBall 0 R'))
  have hBox : IsCompact Box := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_closedBall 0 R).prod ((isCompact_closedBall 0 R').image MulOpposite.opHomeomorph.continuous))
  have hFcs : HasCompactSupport F := by
    refine HasCompactSupport.intro hBox fun b hb => ?_
    by_contra hFb
    apply hb
    have hmem := hsuppD b hFb
    have h1 : ‖(((b * uv * b : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ ≤ M := by simpa using hM _ hmem
    have h2 : ‖(((b * uv * b)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ ≤ M' := by simpa using hM' _ hmem
    have hb0 : 0 ≤ ‖(b : (v.adicCompletion K))‖ := norm_nonneg _
    have hbi0 : 0 ≤ ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ := norm_nonneg _
    have e1 : ‖(((b * uv * b : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ = ‖(b : (v.adicCompletion K))‖ * ‖(uv : (v.adicCompletion K))‖ * ‖(b : (v.adicCompletion K))‖ := by
      rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul]
    have e2 : ‖(((b * uv * b)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ * ‖(uv : (v.adicCompletion K))‖ =
        ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ * ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ := by
      have hb0' : ‖(b : (v.adicCompletion K))‖ ≠ 0 := norm_ne_zero_iff.mpr b.ne_zero
      simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
      field_simp
    refine ⟨?_, ?_⟩
    ·
      show (b : (v.adicCompletion K)) ∈ Metric.closedBall 0 R
      rw [mem_closedBall_zero_iff]
      rcases le_or_gt ‖(b : (v.adicCompletion K))‖ 1 with hle | hlt
      · exact hle.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        rw [le_div_iff₀ huv0]
        calc ‖(b : (v.adicCompletion K))‖ * ‖(uv : (v.adicCompletion K))‖ ≤ ‖(b : (v.adicCompletion K))‖ * ‖(uv : (v.adicCompletion K))‖ * ‖(b : (v.adicCompletion K))‖ := by
              exact le_mul_of_one_le_right (mul_nonneg hb0 huv0.le) hlt.le
          _ = _ := e1.symm
          _ ≤ M := h1
    · show MulOpposite.op (((b⁻¹ : (v.adicCompletion K)ˣ)) : (v.adicCompletion K)) ∈ MulOpposite.opHomeomorph '' Metric.closedBall 0 R'
      refine ⟨((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)), ?_, rfl⟩
      rw [mem_closedBall_zero_iff]
      rcases le_or_gt ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ 1 with hle | hlt
      · exact hle.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        calc ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ ≤ ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ * ‖((b⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ :=
              le_mul_of_one_le_left hbi0 hlt.le
          _ = ‖(((b * uv * b)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ * ‖(uv : (v.adicCompletion K))‖ := e2.symm
          _ ≤ M' * ‖(uv : (v.adicCompletion K))‖ := mul_le_mul_of_nonneg_right h2 huv0.le
  refine ⟨F, hFlc, hFcs, fun b τ hτ hτ1 J hJ => (hF b J ⟨τ, hτ, hτ1, hJ⟩).symm⟩

end S4aux

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
    ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Ψv ∧ HasCompactSupport Ψv ∧
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
        AutomorphicForm.IsWeightedOrbitalIntegral K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z) fv J →
          J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
  classical
  have huv1 : ((Units.map (algebraMap K (v.adicCompletion K) : K →* (v.adicCompletion K)) u : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 1 := by
    intro h
    apply hu1
    have h' : algebraMap K (v.adicCompletion K) (u : K) = 1 := h
    exact (algebraMap K (v.adicCompletion K)).injective (by rw [h', map_one])
  set uv : (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K) : K →* (v.adicCompletion K)) u with huv
  obtain ⟨F, hFlc, hFcs, hF⟩ := S4aux.local_core K v fv hfv uv huv1

  have hcomp : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) * diagUnits2 uv 1 := by
    intro z
    apply Units.ext
    rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, Units.val_mul,
      LanglandsTunnell.CubicInduction.coe_diagUnits2]
    have e1 : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = algebraMap K (v.adicCompletion K) (u : K) := rfl
    have e2 : ((((1 : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := rfl
    have e3 : ((uv : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = algebraMap K (v.adicCompletion K) (u : K) := by rw [huv]; rfl
    rw [e1, e2, mul_one, ← NumberField.AdeleRing.val_finiteUnitsComponent]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, e3]

  have huv0 : 0 < ‖(uv : (v.adicCompletion K))‖ := norm_pos_iff.mpr uv.ne_zero
  let A : Set (v.adicCompletion K)ˣ := (fun a : (v.adicCompletion K)ˣ => (a : (v.adicCompletion K))) ⁻¹' Metric.ball (uv : (v.adicCompletion K)) (‖(uv : (v.adicCompletion K))‖ / 2)
  have hAo : IsOpen A := (IsUltrametricDist.isClopen_ball _ _).isOpen.preimage Units.continuous_val
  have hAc : IsClosed A := (IsUltrametricDist.isClopen_ball _ _).isClosed.preimage Units.continuous_val
  have huvA : uv ∈ A := Metric.mem_ball_self (half_pos huv0)
  let BoxA : Set (v.adicCompletion K)ˣ := Units.embedProduct (v.adicCompletion K) ⁻¹'
    (Metric.closedBall 0 (2 * ‖(uv : (v.adicCompletion K))‖) ×ˢ (MulOpposite.opHomeomorph '' Metric.closedBall 0 (2 / ‖(uv : (v.adicCompletion K))‖)))
  have hBoxA : IsCompact BoxA := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_closedBall 0 _).prod ((isCompact_closedBall 0 _).image MulOpposite.opHomeomorph.continuous))
  have hAsub : A ⊆ BoxA := by
    intro a ha
    have ha' : ‖(a : (v.adicCompletion K)) - uv‖ < ‖(uv : (v.adicCompletion K))‖ / 2 := by
      simpa [A, Metric.mem_ball, dist_eq_norm] using ha
    have hup : ‖(a : (v.adicCompletion K))‖ ≤ 2 * ‖(uv : (v.adicCompletion K))‖ := by
      have := norm_le_norm_add_norm_sub' (a : (v.adicCompletion K)) (uv : (v.adicCompletion K))
      have h3 : ‖(a : (v.adicCompletion K))‖ ≤ ‖(uv : (v.adicCompletion K))‖ + ‖(a : (v.adicCompletion K)) - uv‖ := norm_le_insert' _ _
      linarith
    have hlow : ‖(uv : (v.adicCompletion K))‖ / 2 ≤ ‖(a : (v.adicCompletion K))‖ := by
      have h3 : ‖(uv : (v.adicCompletion K))‖ ≤ ‖(a : (v.adicCompletion K))‖ + ‖(a : (v.adicCompletion K)) - uv‖ := by
        have := norm_sub_le_norm_add (uv : (v.adicCompletion K)) (a : (v.adicCompletion K))
        calc ‖(uv : (v.adicCompletion K))‖ = ‖(a : (v.adicCompletion K)) - ((a : (v.adicCompletion K)) - uv)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖(a : (v.adicCompletion K))‖ + ‖(a : (v.adicCompletion K)) - uv‖ := norm_sub_le _ _
      linarith
    refine ⟨?_, ?_⟩
    · show (a : (v.adicCompletion K)) ∈ Metric.closedBall 0 (2 * ‖(uv : (v.adicCompletion K))‖)
      rw [mem_closedBall_zero_iff]; exact hup
    · show MulOpposite.op (((a⁻¹ : (v.adicCompletion K)ˣ)) : (v.adicCompletion K)) ∈ MulOpposite.opHomeomorph '' Metric.closedBall 0 (2 / ‖(uv : (v.adicCompletion K))‖)
      refine ⟨((a⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)), ?_, rfl⟩
      rw [mem_closedBall_zero_iff, Units.val_inv_eq_inv_val, norm_inv]
      have ha0 : 0 < ‖(a : (v.adicCompletion K))‖ := lt_of_lt_of_le (half_pos huv0) hlow
      rw [inv_le_comm₀ ha0 (by positivity)]
      calc (2 / ‖(uv : (v.adicCompletion K))‖)⁻¹ = ‖(uv : (v.adicCompletion K))‖ / 2 := by rw [inv_div]
        _ ≤ ‖(a : (v.adicCompletion K))‖ := hlow
  have hAk : IsCompact A := hBoxA.of_isClosed_subset hAc hAsub
  let χ : (v.adicCompletion K)ˣ → ℂ := A.indicator fun _ => (1 : ℂ)
  have hχ : IsLocallyConstant χ := AutomorphicForm.isLocallyConstant_indicator_one hAo hAc
  refine ⟨fun p => χ p.1 * F p.2, ?_, ?_, ?_⟩
  · exact (hχ.comp_continuous continuous_fst).mul (hFlc.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro (hAk.prod hFcs.isCompact) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h1 | h2
    · show A.indicator (fun _ => (1 : ℂ)) p.1 * F p.2 = 0
      rw [Set.indicator_of_notMem h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · intro z J hJ
    show J = A.indicator (fun _ => (1 : ℂ)) uv * F (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)
    rw [Set.indicator_of_mem huvA, one_mul]
    obtain ⟨τ₂, hτ₂, hτ₂1, hJ₂⟩ := S4aux.transportW K v (hcomp z) (τF z) (hτF z) (hτF1 z) fv J hJ
    exact hF _ τ₂ hτ₂ hτ₂1 J hJ₂

end S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2 (solution)
