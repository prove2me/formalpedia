-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b51462f8-0c26-5fff-a590-86bfcef893ee

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
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
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
import Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped Pointwise

noncomputable section

namespace TwLCU

variable (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

theorem scalar_mul_comm (u : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.scalar_apply]
  exact (Matrix.scalar_commute (u : (v.adicCompletion K)) (fun _ => Commute.all _ _) _).eq

theorem diag_mul_unipotent (a t a' t' : (v.adicCompletion K)ˣ) (x : (v.adicCompletion K)) :
    diagUnits2 a' (a' * t') * AutomorphicForm.unipotentGL2 x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (a' * a⁻¹) *
        (diagUnits2 a (a * t) * AutomorphicForm.unipotentGL2 (x * (((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)))) *
        diagUnits2 1 (t' * t⁻¹) := by
  refine Units.ext ?_
  have ha : (a : (v.adicCompletion K)) ≠ 0 := a.ne_zero
  have ht : (t : (v.adicCompletion K)) ≠ 0 := t.ne_zero
  have ht' : (t' : (v.adicCompletion K)) ≠ 0 := t'.ne_zero
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe,
    Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Units.val_inv_eq_inv_val, mul_inv, inv_inv, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.one_apply] <;> field_simp <;> ring

theorem arg_eq (k : GL (Fin 2) (v.adicCompletion K)) (a t a' t' : (v.adicCompletion K)ˣ) (x : (v.adicCompletion K)) :
    AutomorphicForm.LocalWeightedOrbital.arg k a' (a' * t') x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (a' * a⁻¹) *
        AutomorphicForm.LocalWeightedOrbital.arg k a (a * t) (x * (((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) *
        (k⁻¹ * diagUnits2 1 (t' * t⁻¹) * k) := by
  simp only [AutomorphicForm.LocalWeightedOrbital.arg]
  rw [diag_mul_unipotent K v a t a' t' x]
  rw [show k⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) (a' * a⁻¹) *
      (diagUnits2 a (a * t) * AutomorphicForm.unipotentGL2 (x * (((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)))) * diagUnits2 1 (t' * t⁻¹)) * k =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (a' * a⁻¹) * (k⁻¹ *
      ((diagUnits2 a (a * t) * AutomorphicForm.unipotentGL2 (x * (((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)))) * diagUnits2 1 (t' * t⁻¹)) * k) from by
    rw [← mul_assoc, ← mul_assoc, ← scalar_mul_comm K v (a' * a⁻¹) k⁻¹]; simp only [mul_assoc]]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem halfWeighted_congr
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (W V₀ : Set (GL (Fin 2) (v.adicCompletion K)))
    (hW : ∀ g : GL (Fin 2) (v.adicCompletion K), ∀ w ∈ W, f (g * w) = f g ∧ f (w * g) = f g)
    (hconj : ∀ k ∈ AutomorphicForm.localIntegralSet K v, ∀ w ∈ V₀, k⁻¹ * w * k ∈ W)
    (a t a' t' : (v.adicCompletion K)ˣ)
    (huW : diagUnits2 (a' * a⁻¹) (a' * a⁻¹) ∈ W) (hsV : diagUnits2 1 (t' * t⁻¹) ∈ V₀)
    (hnt' : ‖(t' : (v.adicCompletion K))‖ = ‖(t : (v.adicCompletion K))‖)
    (h1t' : ‖(1 : (v.adicCompletion K)) - (t' : (v.adicCompletion K))‖ = ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖) :
    letI := AutomorphicForm.localGLBorel K v
    AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : (v.adicCompletion K) => ‖x‖) f a' (a' * t') =
      AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
  have hK0c := AutomorphicForm.isCompact_localIntegralSet K v
  have hsn : ‖((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖ = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hnt', mul_inv_cancel₀ (norm_ne_zero_iff.mpr t.ne_zero)]

  have hslice : ∀ x : (v.adicCompletion K),
      AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a' (a' * t') x =
        AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a (a * t) (x * (((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) := by
    intro x
    unfold AutomorphicForm.LocalWeightedOrbital.slice
    refine setIntegral_congr_fun (hK0c.isClosed.measurableSet) fun k hk => ?_
    rw [TwLCU.arg_eq K v k a t a' t' x, ← AutomorphicForm.LocalWeightedOrbital.diagUnits2_self, mul_assoc,
      (hW _ _ huW).2, (hW _ _ (hconj k hk _ hsV)).1]

  have hratio : AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') =
      AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) := by
    unfold AutomorphicForm.LocalWeightedOrbital.ratio
    beta_reduce
    rw [Units.val_mul, Units.val_mul, mul_comm (a' : (v.adicCompletion K)), mul_assoc, Units.mul_inv, mul_one,
      mul_comm (a : (v.adicCompletion K)), mul_assoc, Units.mul_inv, mul_one, h1t']
  have hsqrt : AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') =
      AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) := by
    unfold AutomorphicForm.LocalWeightedOrbital.sqrtRatio
    beta_reduce
    rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul, hnt', div_mul_eq_div_div, div_mul_eq_div_div,
      div_self (norm_ne_zero_iff.mpr a'.ne_zero), div_self (norm_ne_zero_iff.mpr a.ne_zero)]

  have hμinv : Measure.map (fun x : (v.adicCompletion K) => x * ((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) μ = μ := by
    ext A hA
    rw [Measure.map_apply (measurable_mul_const _) hA]
    have hset : (fun x : (v.adicCompletion K) => x * ((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) ⁻¹' A = ((t' * t⁻¹)⁻¹ : (v.adicCompletion K)ˣ) • A := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul, mul_comm]
    rw [hset, ← distribHaarChar_mul, ← LanglandsTunnell.TateLocal.modulus_coe_units,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v, Units.val_inv_eq_inv_val, nnnorm_inv,
      show ‖((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))‖₊ = 1 from by ext; rw [coe_nnnorm, hsn]; rfl, inv_one, ENNReal.coe_one, one_mul]

  unfold AutomorphicForm.LocalWeightedOrbital.halfWeighted
  rw [hratio, hsqrt]
  congr 1
  simp_rw [hslice]
  set R : ℝ := AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) with hR
  let e : (v.adicCompletion K) ≃ᵐ (v.adicCompletion K) := MeasurableEquiv.mulRight₀ ((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) (t' * t⁻¹).ne_zero
  have hecoe : (⇑e : (v.adicCompletion K) → (v.adicCompletion K)) = fun x => x * ((t' * t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) := rfl
  conv_lhs => rw [← hμinv, ← hecoe, setIntegral_map_equiv]
  have hpre : ⇑e ⁻¹' {x : (v.adicCompletion K) | R < ‖x‖} = {x : (v.adicCompletion K) | R < ‖x‖} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hecoe, norm_mul, hsn, mul_one]
  rw [hpre]
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet fun x hx => ?_
  simp only [hecoe]
  rw [norm_mul, hsn, mul_one, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end TwLCU

end

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions

open scoped Classical

set_option maxHeartbeats 6400000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ (Λ₀ : (v.adicCompletion K)ˣ → ℂ) (C₀ : ℝ), ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ a : (v.adicCompletion K)ˣ, (¬ ∃ α : (L ⊗[K] (v.adicCompletion K))ˣ, Algebra.norm (v.adicCompletion K) (α : (L ⊗[K] (v.adicCompletion K))) = (a : (v.adicCompletion K))) →
      ∀ t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
        ‖2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ₀ a‖ ≤ C₀ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
  obtain ⟨hlc, hcs⟩ := hf
  have hK0c := AutomorphicForm.isCompact_localIntegralSet K v
  have hNSZ := AutomorphicForm.LocalWeightedOrbital.splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal K L σ hgen hdeg v φ hφ f ⟨hlc, hcs⟩ hmatch μ
  haveI := AutomorphicForm.isHaarMeasure_localHaar K v
  haveI hfinK : IsFiniteMeasure ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) := isFiniteMeasure_restrict.mpr hK0c.measure_lt_top.ne

  obtain ⟨Cf, hCf⟩ := hcs.exists_bound_of_continuous hlc.continuous
  set M : ℝ := max Cf 0 * (((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) Set.univ).toReal with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hM : ∀ a b : (v.adicCompletion K)ˣ, ∀ y : (v.adicCompletion K), ‖AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a b y‖ ≤ M := by
    intro a b y
    unfold AutomorphicForm.LocalWeightedOrbital.slice
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => (hCf _).trans (le_max_left _ _))

  have hball1 : {z : (v.adicCompletion K) | ‖z‖ ≤ 1} = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff
  have hball1c : IsCompact {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    rw [hball1]; exact isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hball1m : MeasurableSet {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := hball1c.isClosed.measurableSet
  have hμ1 : μ {z : (v.adicCompletion K) | ‖z‖ ≤ 1} = 1 := by rw [hball1]; exact hμ
  have hlogint : IntegrableOn (fun z : (v.adicCompletion K) => Real.log ‖z‖) {z | ‖z‖ ≤ 1} μ := by
    have hli := LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus K v μ
    have heq : (fun y : (v.adicCompletion K) => Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ)) = fun y => Real.log ‖y‖ := by
      funext y; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v y, coe_nnnorm]
    rw [← heq]
    exact hli.integrableOn_isCompact hball1c
  set Φ₁ : ℝ := ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, |Real.log ‖z‖| ∂μ with hΦ₁
  have hΦ₁0 : 0 ≤ Φ₁ := setIntegral_nonneg hball1m fun z _ => abs_nonneg _

  obtain ⟨W, hWo, h1W, hW⟩ :=
    IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport f hlc hcs
  have hSo : IsOpen {p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) | p.1⁻¹ * p.2 * p.1 ∈ W} := by
    have hc : Continuous fun p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) => p.1⁻¹ * p.2 * p.1 :=
      (continuous_fst.inv.mul continuous_snd).mul continuous_fst
    exact hWo.preimage hc
  have hsub : AutomorphicForm.localIntegralSet K v ×ˢ ({1} : Set (GL (Fin 2) (v.adicCompletion K))) ⊆ {p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) | p.1⁻¹ * p.2 * p.1 ∈ W} := by
    rintro ⟨k, w⟩ ⟨-, hw⟩
    have hw' : w = 1 := hw
    show k⁻¹ * w * k ∈ W
    rw [hw', mul_one, inv_mul_cancel]; exact h1W
  obtain ⟨U₀, V₀, -, hV₀o, hKU₀, h1V₀, hUV⟩ := generalized_tube_lemma hK0c isCompact_singleton hSo hsub
  have hconj : ∀ k ∈ AutomorphicForm.localIntegralSet K v, ∀ w ∈ V₀, k⁻¹ * w * k ∈ W := by
    intro k hk w hw
    have hmem : (k, w) ∈ {p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) | p.1⁻¹ * p.2 * p.1 ∈ W} := hUV (Set.mk_mem_prod (hKU₀ hk) hw)
    simpa only [Set.mem_setOf_eq] using hmem
  have h1V₀' : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ V₀ := h1V₀ (Set.mem_singleton (1 : GL (Fin 2) (v.adicCompletion K)))

  have hvalc : ∀ (φ ψ : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ), Continuous φ → Continuous ψ →
      Continuous (fun c : (v.adicCompletion K)ˣ => ((diagUnits2 (φ c) (ψ c) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
    intro φ ψ hφ hψ
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
      first | exact continuous_const | exact Units.continuous_val.comp hφ | exact Units.continuous_val.comp hψ
  have hinvd : ∀ x y : (v.adicCompletion K)ˣ, (diagUnits2 x y)⁻¹ = diagUnits2 x⁻¹ y⁻¹ := fun x y => Units.ext rfl
  have hdiagc : ∀ (φ ψ : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ), Continuous φ → Continuous ψ →
      Continuous (fun c : (v.adicCompletion K)ˣ => diagUnits2 (φ c) (ψ c)) := by
    intro φ ψ hφ hψ
    refine Units.continuous_iff.mpr ⟨hvalc φ ψ hφ hψ, ?_⟩
    simp only [hinvd]
    exact hvalc _ _ (hφ.inv) (hψ.inv)
  have hscal : Continuous (fun c : (v.adicCompletion K)ˣ => diagUnits2 c c) := hdiagc id id continuous_id continuous_id
  have hdiag : Continuous (fun c : (v.adicCompletion K)ˣ => diagUnits2 (1 : (v.adicCompletion K)ˣ) c) := hdiagc (fun _ => 1) id continuous_const continuous_id
  obtain ⟨N, hN⟩ : ∃ N : Set (v.adicCompletion K)ˣ, N = {c | diagUnits2 c c ∈ W ∧ diagUnits2 1 c ∈ V₀} := ⟨_, rfl⟩
  have hNn : N ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
    rw [hN]
    have h11 : diagUnits2 (1 : (v.adicCompletion K)ˣ) (1 : (v.adicCompletion K)ˣ) = 1 := by
      refine Units.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    refine Filter.inter_mem ?_ ?_
    · exact hscal.continuousAt.preimage_mem_nhds (hWo.mem_nhds (by rw [h11]; exact h1W))
    · exact hdiag.continuousAt.preimage_mem_nhds (hV₀o.mem_nhds (by rw [h11]; exact h1V₀'))
  obtain ⟨ε, hε, hball⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ c : (v.adicCompletion K)ˣ, ‖(c : (v.adicCompletion K)) - 1‖ < ε → c ∈ N := by
    have hemb := (Units.isEmbedding_val₀ (G₀ := (v.adicCompletion K)))
    rw [hemb.nhds_eq_comap, Filter.mem_comap] at hNn
    obtain ⟨T, hT, hTN⟩ := hNn
    rw [Units.val_one] at hT
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hT
    exact ⟨ε, hε, fun c hc => hTN (hb (by rwa [Metric.mem_ball, dist_eq_norm]))⟩

  let S : (v.adicCompletion K)ˣ → (v.adicCompletion K) → ℂ := fun a y => AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a a y
  refine ⟨fun a => -(2 * (Module.finrank K L : ℂ) * ∫ y, S a y * (Real.log ‖y‖ : ℂ) ∂μ),
    2 * (Module.finrank K L) * M * (Φ₁ + 2), {t : (v.adicCompletion K)ˣ | ‖(t : (v.adicCompletion K)) - 1‖ < min ε 1}, ?_, ?_⟩
  · exact (isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const).mem_nhds
      (by show ‖((1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - 1‖ < min ε 1; rw [Units.val_one, sub_self, norm_zero]; exact lt_min hε one_pos)
  intro a hna t ht1 htU
  have htε : ‖(t : (v.adicCompletion K)) - 1‖ < ε := lt_of_lt_of_le htU (min_le_left _ _)
  have ht1' : ‖(t : (v.adicCompletion K)) - 1‖ < 1 := lt_of_lt_of_le htU (min_le_right _ _)

  have hnt : ‖(t : (v.adicCompletion K))‖ = 1 := by
    have h : ‖(1 : (v.adicCompletion K))‖ ≠ ‖(t : (v.adicCompletion K)) - 1‖ := by rw [norm_one]; exact (ne_of_gt ht1')
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h
    rw [add_sub_cancel, norm_one, max_eq_left ht1'.le] at this
    exact this
  set R : ℝ := ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ with hR
  have hR0 : 0 < R := by rw [hR, norm_pos_iff, sub_ne_zero]; intro h; exact ht1 (Units.ext h.symm)
  have hR1 : R < 1 := by rw [hR, ← norm_neg, neg_sub]; exact ht1'
  have hRle : R ≤ 1 := hR1.le

  have hsV : diagUnits2 (1 : (v.adicCompletion K)ˣ) (t * 1⁻¹) ∈ V₀ := by
    have := hball (t * 1⁻¹) (by rw [inv_one, mul_one]; exact htε)
    rw [hN] at this; exact this.2
  have huW : diagUnits2 (a * a⁻¹) (a * a⁻¹) ∈ W := by
    rw [mul_inv_cancel]
    rw [show diagUnits2 (1 : (v.adicCompletion K)ˣ) (1 : (v.adicCompletion K)ˣ) = 1 from by
      refine Units.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]]
    exact h1W

  have htr : ∀ x : (v.adicCompletion K), AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a (a * t) x = S a (x * ((t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) := by
    intro x
    show AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a (a * t) x =
      AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a a (x * ((t⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)))
    unfold AutomorphicForm.LocalWeightedOrbital.slice
    refine setIntegral_congr_fun hK0c.isClosed.measurableSet fun k hk => ?_
    have := TwLCU.arg_eq K v k a 1 a t x
    rw [mul_one] at this
    rw [this, ← AutomorphicForm.LocalWeightedOrbital.diagUnits2_self, mul_assoc, (hW _ _ huW).2,
      (hW _ _ (hconj k hk _ hsV)).1]
    congr 2
    simp

  have hμt : Measure.map (fun x : (v.adicCompletion K) => x * (t : (v.adicCompletion K))) μ = μ := by
    ext A hA
    rw [Measure.map_apply (measurable_mul_const _) hA]
    have hset : (fun x : (v.adicCompletion K) => x * (t : (v.adicCompletion K))) ⁻¹' A = (t⁻¹ : (v.adicCompletion K)ˣ) • A := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul, mul_comm]
    rw [hset, ← distribHaarChar_mul, ← LanglandsTunnell.TateLocal.modulus_coe_units,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v, Units.val_inv_eq_inv_val, nnnorm_inv,
      show ‖(t : (v.adicCompletion K))‖₊ = 1 from by ext; rw [coe_nnnorm, hnt]; rfl, inv_one, ENNReal.coe_one, one_mul]

  have htrI : ∀ (g : (v.adicCompletion K) → ℂ), (∀ x, g (x * (t : (v.adicCompletion K))) = g x) →
      ∀ A : Set (v.adicCompletion K), MeasurableSet A → (fun x => x * (t : (v.adicCompletion K))) ⁻¹' A = A →
      ∫ x in A, AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a (a * t) x * g x ∂μ = ∫ y in A, S a y * g y ∂μ := by
    intro g hg A hAm hA
    simp_rw [htr]
    let e : (v.adicCompletion K) ≃ᵐ (v.adicCompletion K) := MeasurableEquiv.mulRight₀ (t : (v.adicCompletion K)) t.ne_zero
    have hecoe : (⇑e : (v.adicCompletion K) → (v.adicCompletion K)) = fun x => x * (t : (v.adicCompletion K)) := rfl
    conv_lhs => rw [← hμt, ← hecoe, setIntegral_map_equiv]
    simp only [hecoe]
    rw [hA]
    refine setIntegral_congr_fun hAm fun y hy => ?_
    rw [hg, Units.val_inv_eq_inv_val, mul_inv_cancel_right₀ t.ne_zero]

  have hSm : StronglyMeasurable (S a) := by
    have hF : Continuous fun p : (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) => f (AutomorphicForm.LocalWeightedOrbital.arg p.2 a a p.1) := by
      refine hlc.continuous.comp ?_
      unfold AutomorphicForm.LocalWeightedOrbital.arg
      refine ((continuous_snd.inv).mul (continuous_const.mul ?_)).mul continuous_snd

      have hu : Continuous fun y : (v.adicCompletion K) => AutomorphicForm.unipotentGL2 y := by
        refine Units.continuous_iff.mpr ⟨?_, ?_⟩
        · refine continuous_matrix fun i j => ?_
          fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2_coe] <;> first | exact continuous_const | exact continuous_id
        · have : ∀ y : (v.adicCompletion K), (AutomorphicForm.unipotentGL2 y)⁻¹ = AutomorphicForm.unipotentGL2 (-y) := fun y => by
            rw [← mul_eq_one_iff_inv_eq, ← AutomorphicForm.unipotentGL2_add, add_neg_cancel, AutomorphicForm.unipotentGL2_zero]
          simp only [this]
          refine continuous_matrix fun i j => ?_
          fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2_coe] <;> first | exact continuous_const | exact continuous_neg
      exact hu.comp continuous_fst
    exact (hF.stronglyMeasurable).integral_prod_right'

  obtain ⟨Ba, hBa⟩ : ∃ Ba : ℝ, ∀ y : (v.adicCompletion K), S a y ≠ 0 → ‖y‖ ≤ Ba := by
    set C : Set (GL (Fin 2) (v.adicCompletion K)) := (fun p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) => p.1 * p.2 * p.1⁻¹) '' (AutomorphicForm.localIntegralSet K v ×ˢ tsupport f) with hC
    have hCc : IsCompact C := (hK0c.prod hcs).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
    have hent : Continuous fun Mx : GL (Fin 2) (v.adicCompletion K) => ‖(Mx : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ :=
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).matrix_elem 0 1).norm
    obtain ⟨B, hB⟩ := hCc.bddAbove_image hent.continuousOn
    refine ⟨B / ‖(a : (v.adicCompletion K))‖, fun y hy => ?_⟩
    obtain ⟨k, hk, hfk⟩ : ∃ k ∈ AutomorphicForm.localIntegralSet K v, f (AutomorphicForm.LocalWeightedOrbital.arg k a a y) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hy (setIntegral_eq_zero_of_forall_eq_zero fun k hk => hall k hk)
    have hMx : diagUnits2 a a * AutomorphicForm.unipotentGL2 y ∈ C := by
      refine ⟨(k, AutomorphicForm.LocalWeightedOrbital.arg k a a y), ⟨hk, subset_tsupport _ hfk⟩, ?_⟩
      show k * (k⁻¹ * (diagUnits2 a a * AutomorphicForm.unipotentGL2 y) * k) * k⁻¹ = _
      group
    have h01 : ((diagUnits2 a a * AutomorphicForm.unipotentGL2 y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = (a : (v.adicCompletion K)) * y := by
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
    have hb : ‖((diagUnits2 a a * AutomorphicForm.unipotentGL2 y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ ≤ B := hB ⟨_, hMx, rfl⟩
    rw [h01, norm_mul] at hb
    rw [le_div_iff₀ (norm_pos_iff.mpr a.ne_zero), mul_comm]; exact hb
  set D : Set (v.adicCompletion K) := {y | ‖y‖ ≤ Ba} with hD
  have hDc : IsCompact D := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_norm continuous_const) ?_
    exact (Metric.isBounded_closedBall (x := (0 : (v.adicCompletion K))) (r := Ba)).subset fun y hy => by
      first
        | simpa [Metric.mem_closedBall, dist_zero_right] using hy
        | (have h' := hy; simp [Metric.mem_closedBall, dist_zero_right] at h' ⊢; exact h')
        | (have h' := hy; simp [Metric.mem_closedBall, dist_zero_right] at h'; exact h')
        | exact hy
        | (simpa [Metric.mem_closedBall, dist_zero_right, Function.comp_def] using hy)
  have hSsupp : ∀ y, y ∉ D → S a y = 0 := fun y hy => by
    by_contra h; exact hy (hBa y h)
  have hSint : Integrable (S a) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := D) ?_ hSsupp
    exact Measure.integrableOn_of_bounded (M := M) hDc.measure_lt_top.ne hSm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hM a a y)
  have hSlogint : Integrable (fun y => S a y * (Real.log ‖y‖ : ℂ)) μ := by
    have hlogD : IntegrableOn (fun z : (v.adicCompletion K) => (Real.log ‖z‖ : ℂ)) D μ := by
      have hli := LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus K v μ
      have heq : (fun y : (v.adicCompletion K) => Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ)) = fun y => Real.log ‖y‖ := by
        funext y; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v y, coe_nnnorm]
      have := hli.integrableOn_isCompact hDc
      rw [heq] at this
      exact this.ofReal
    have hprod : IntegrableOn (fun y => S a y * (Real.log ‖y‖ : ℂ)) D μ :=
      Integrable.bdd_mul hlogD (hSm.aestronglyMeasurable.restrict) (Filter.Eventually.of_forall fun y => hM a a y)
    refine hprod.integrable_of_forall_notMem_eq_zero fun y hy => ?_
    rw [hSsupp y hy, zero_mul]

  have hratio : AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) = R := by
    unfold AutomorphicForm.LocalWeightedOrbital.ratio
    beta_reduce
    rw [Units.val_mul, mul_comm (a : (v.adicCompletion K)), mul_assoc, Units.mul_inv, mul_one]
  have hsqrt : AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) = 1 := by
    unfold AutomorphicForm.LocalWeightedOrbital.sqrtRatio
    beta_reduce
    rw [Units.val_mul, norm_mul, hnt, mul_one, div_self (norm_ne_zero_iff.mpr a.ne_zero), Real.sqrt_one]
  have hAo : IsOpen {y : (v.adicCompletion K) | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hAinv : (fun x : (v.adicCompletion K) => x * (t : (v.adicCompletion K))) ⁻¹' {y : (v.adicCompletion K) | R < ‖y‖} = {y | R < ‖y‖} := by
    ext x; simp [norm_mul, hnt]
  have hwinv : ∀ x : (v.adicCompletion K), ((Real.log ‖x * (t : (v.adicCompletion K))‖ - Real.log R : ℝ) : ℂ) = ((Real.log ‖x‖ - Real.log R : ℝ) : ℂ) := by
    intro x; rw [norm_mul, hnt, mul_one]
  have hH : AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) =
      -∫ y in {y : (v.adicCompletion K) | R < ‖y‖}, S a y * ((Real.log ‖y‖ - Real.log R : ℝ) : ℂ) ∂μ := by
    unfold AutomorphicForm.LocalWeightedOrbital.halfWeighted
    rw [hratio, hsqrt, Complex.ofReal_one, neg_one_mul]
    congr 1
    exact htrI (fun x => ((Real.log ‖x‖ - Real.log R : ℝ) : ℂ)) hwinv _ hAo.measurableSet hAinv

  have hS0 : ∫ y, S a y ∂μ = 0 := by
    have h := hNSZ a hna t ht1
    unfold AutomorphicForm.LocalWeightedOrbital.splitOrbital at h
    have h2 := htrI (fun _ => (1 : ℂ)) (fun _ => rfl) Set.univ MeasurableSet.univ (Set.preimage_univ)
    simp only [mul_one, Measure.restrict_univ] at h2
    rw [← h2]; exact h

  set A : Set (v.adicCompletion K) := {y | R < ‖y‖} with hA
  set Bs : Set (v.adicCompletion K) := {y | ‖y‖ ≤ R} with hBs
  have hBm : MeasurableSet Bs := (isClosed_le continuous_norm continuous_const).measurableSet
  have hAc : Aᶜ = Bs := by ext y; simp [hA, hBs, not_lt]
  let G : (v.adicCompletion K) → ℂ := fun y => S a y * ((Real.log ‖y‖ - Real.log R : ℝ) : ℂ)
  have hGeq : ∀ y, G y = S a y * (Real.log ‖y‖ : ℂ) - (Real.log R : ℂ) * S a y := by
    intro y; simp only [G]; push_cast; ring
  have hGint : Integrable G μ := by
    have : G = fun y => S a y * (Real.log ‖y‖ : ℂ) - (Real.log R : ℂ) * S a y := funext hGeq
    rw [this]; exact hSlogint.sub (hSint.const_mul _)
  have hsplit : ∫ y in A, G y ∂μ = ∫ y, G y ∂μ - ∫ y in Bs, G y ∂μ := by
    have := integral_add_compl hAo.measurableSet hGint
    rw [hAc] at this
    linear_combination this
  have hGtot : ∫ y, G y ∂μ = ∫ y, S a y * (Real.log ‖y‖ : ℂ) ∂μ := by
    rw [show G = fun y => S a y * (Real.log ‖y‖ : ℂ) - (Real.log R : ℂ) * S a y from funext hGeq,
      integral_sub hSlogint (hSint.const_mul _), integral_const_mul, hS0, mul_zero, sub_zero]

  have hkey : 2 * (Module.finrank K L : ℂ) *
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) -
      -(2 * (Module.finrank K L : ℂ) * ∫ y, S a y * (Real.log ‖y‖ : ℂ) ∂μ) =
      2 * (Module.finrank K L : ℂ) * ∫ y in Bs, G y ∂μ := by
    rw [hH, show (∫ y in {y : (v.adicCompletion K) | R < ‖y‖}, S a y * ((Real.log ‖y‖ - Real.log R : ℝ) : ℂ) ∂μ) = ∫ y in A, G y ∂μ from rfl,
      hsplit, hGtot]
    ring
  rw [hkey]

  set r : (v.adicCompletion K) := (1 : (v.adicCompletion K)) - (t : (v.adicCompletion K)) with hr
  have hr0 : r ≠ 0 := fun h => hR0.ne' (by rw [hR, h, norm_zero])
  have hrn : ‖r‖ = R := rfl
  have hmapr : Measure.map (fun z : (v.adicCompletion K) => z * r) μ = ((‖r‖₊)⁻¹ : NNReal) • μ := by
    ext A' hA'
    rw [Measure.map_apply (measurable_mul_const _) hA', Measure.smul_apply]
    have hset : (fun z : (v.adicCompletion K) => z * r) ⁻¹' A' = ((Units.mk0 r hr0)⁻¹ : (v.adicCompletion K)ˣ) • A' := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul, mul_comm]; rfl
    rw [hset, ← distribHaarChar_mul, ← LanglandsTunnell.TateLocal.modulus_coe_units,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v, Units.val_inv_eq_inv_val, nnnorm_inv]
    rfl
  have hμeq : μ = (‖r‖₊ : NNReal) • Measure.map (fun z : (v.adicCompletion K) => z * r) μ := by
    rw [hmapr, smul_smul, mul_inv_cancel₀ (by rwa [ne_eq, nnnorm_eq_zero]), one_smul]
  have hpreB : (fun z : (v.adicCompletion K) => z * r) ⁻¹' Bs = {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    ext z
    simp only [Set.mem_preimage, hBs, Set.mem_setOf_eq, norm_mul, hrn]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

  have hμBs : μ.real Bs = R := by
    rw [measureReal_def, hμeq, Measure.smul_apply, Measure.map_apply (measurable_mul_const _) hBm, hpreB, hμ1]
    simp [hrn]
  have hsub : Bs ⊆ {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := fun y hy => le_trans hy hRle
  have hB1fin : μ {z : (v.adicCompletion K) | ‖z‖ ≤ 1} ≠ ⊤ := by rw [hμ1]; exact ENNReal.one_ne_top
  have hBsfin : μ Bs ≠ ⊤ := ne_top_of_le_ne_top hB1fin (measure_mono hsub)

  have hlogBs : ∫ y in Bs, |Real.log ‖y‖| ∂μ ≤ R * (Φ₁ + |Real.log R|) := by
    have hint : IntegrableOn (fun y : (v.adicCompletion K) => |Real.log ‖y‖|) Bs μ := (hlogint.mono_set hsub).abs
    let e : (v.adicCompletion K) ≃ᵐ (v.adicCompletion K) := MeasurableEquiv.mulRight₀ r hr0
    have hecoe : (⇑e : (v.adicCompletion K) → (v.adicCompletion K)) = fun z => z * r := rfl
    have step : ∫ y in Bs, |Real.log ‖y‖| ∂μ = R * ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, |Real.log ‖z * r‖| ∂μ := by
      conv_lhs => rw [hμeq, Measure.restrict_smul, integral_smul_nnreal_measure, ← hecoe, setIntegral_map_equiv]
      simp only [hecoe, hpreB, norm_mul, hrn, NNReal.smul_def, coe_nnnorm, smul_eq_mul]
    rw [step]
    refine mul_le_mul_of_nonneg_left ?_ hR0.le
    have hbound : ∀ z : (v.adicCompletion K), |Real.log ‖z * r‖| ≤ |Real.log ‖z‖| + |Real.log R| := by
      intro z
      by_cases hz : z = 0
      · rw [hz, zero_mul, norm_zero, Real.log_zero, abs_zero]; positivity
      · rw [norm_mul, hrn, Real.log_mul (norm_ne_zero_iff.mpr hz) hR0.ne']
        exact abs_add_le _ _
    calc ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, |Real.log ‖z * r‖| ∂μ
        ≤ ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, (|Real.log ‖z‖| + |Real.log R|) ∂μ := by
          refine setIntegral_mono_on ?_ (hlogint.abs.add (integrableOn_const (C := |Real.log R|) hB1fin)) hball1m fun z _ => hbound z

          refine Integrable.mono' (hlogint.abs.add (integrableOn_const (C := |Real.log R|) hB1fin)) ?_ ?_
          · exact (continuous_abs.measurable.comp (Real.measurable_log.comp ((continuous_mul_right r).norm.measurable))).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_abs]; exact hbound z
      _ = Φ₁ + |Real.log R| := by
          rw [integral_add hlogint.abs (integrableOn_const (C := |Real.log R|) hB1fin),
            setIntegral_const, measureReal_def, hμ1, ENNReal.toReal_one, one_smul]

  have hGB : ‖∫ y in Bs, G y ∂μ‖ ≤ M * (R * (Φ₁ + |Real.log R|) + |Real.log R| * R) := by
    have hint : IntegrableOn (fun y : (v.adicCompletion K) => |Real.log ‖y‖|) Bs μ := (hlogint.mono_set hsub).abs
    have h1 : ‖∫ y in Bs, G y ∂μ‖ ≤ ∫ y in Bs, M * (|Real.log ‖y‖| + |Real.log R|) ∂μ := by
      refine norm_integral_le_of_norm_le ((hint.add (integrableOn_const (C := |Real.log R|) hBsfin)).const_mul M) ?_
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [G, norm_mul]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hM a a y) (abs_sub _ _) (abs_nonneg _) hM0
    refine h1.trans ?_
    have h2 : ∫ y in Bs, M * (|Real.log ‖y‖| + |Real.log R|) ∂μ = M * ((∫ y in Bs, |Real.log ‖y‖| ∂μ) + R * |Real.log R|) := by
      rw [integral_const_mul, integral_add hint (integrableOn_const (C := |Real.log R|) hBsfin), setIntegral_const, hμBs, smul_eq_mul]
    rw [h2]
    exact mul_le_mul_of_nonneg_left (add_le_add hlogBs (le_of_eq (by ring))) hM0
  clear_value R Φ₁ M
  calc ‖2 * (Module.finrank K L : ℂ) * ∫ y in Bs, G y ∂μ‖
      = 2 * (Module.finrank K L : ℝ) * ‖∫ y in Bs, G y ∂μ‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_two]
    _ ≤ 2 * (Module.finrank K L : ℝ) * (M * (R * (Φ₁ + |Real.log R|) + |Real.log R| * R)) :=
        mul_le_mul_of_nonneg_left hGB (by positivity)
    _ ≤ 2 * (Module.finrank K L : ℝ) * (M * ((Φ₁ + 2) * (R * (1 + |Real.log R|)))) := by
        have h0 : 0 ≤ |Real.log R| := abs_nonneg _
        have hineq : R * (Φ₁ + |Real.log R|) + |Real.log R| * R ≤ (Φ₁ + 2) * (R * (1 + |Real.log R|)) := by
          have : (Φ₁ + 2) * (R * (1 + |Real.log R|)) - (R * (Φ₁ + |Real.log R|) + |Real.log R| * R) = R * (Φ₁ * |Real.log R| + 2) := by ring
          have hnn : 0 ≤ R * (Φ₁ * |Real.log R| + 2) := mul_nonneg hR0.le (by positivity)
          linarith
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hineq hM0) (by positivity)
    _ = _ := by ring

end S_AutomorphicForm_exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal (solution)
