-- Prove2me | solution 1 for AutomorphicForm.lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8f58cccc-992b-5dc7-bb21-1bcffb47b2fa

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
import Theorems.Thm_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
import Theorems.Thm_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
import Theorems.Thm_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

namespace Ws46
namespace CZ

open MeasureTheory Filter NumberField IsDedekindDomain AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

theorem indicator_eq_prod_indicator_ennreal {α : Type*} {ι : Type*} {β : ι → Type*} (U : Set α) (x : α)
    (S : Finset ι) (W : ∀ i, Set (β i)) (y : ∀ i, β i)
    (h : U.indicator (fun _ => (1 : ℂ)) x = ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℂ)) (y i)) :
    U.indicator (fun _ => (1 : ℝ≥0∞)) x = ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℝ≥0∞)) (y i) := by
  classical
  by_cases hall : ∀ i ∈ S, y i ∈ W i
  · have hr : ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℝ≥0∞)) (y i) = 1 :=
      Finset.prod_eq_one fun i hi => Set.indicator_of_mem (hall i hi) _
    have hc : ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℂ)) (y i) = 1 :=
      Finset.prod_eq_one fun i hi => Set.indicator_of_mem (hall i hi) _
    rw [hr]
    rw [hc] at h
    have hx : x ∈ U := by
      by_contra hx
      rw [Set.indicator_of_notMem hx] at h
      exact zero_ne_one h
    exact Set.indicator_of_mem hx _
  · push Not at hall
    obtain ⟨i, hi, hyi⟩ := hall
    have hr : ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℝ≥0∞)) (y i) = 0 :=
      Finset.prod_eq_zero hi (Set.indicator_of_notMem hyi _)
    have hc : ∏ i ∈ S, (W i).indicator (fun _ => (1 : ℂ)) (y i) = 0 :=
      Finset.prod_eq_zero hi (Set.indicator_of_notMem hyi _)
    rw [hr]
    rw [hc] at h
    have hx : x ∉ U := by
      intro hx
      rw [Set.indicator_of_mem hx] at h
      exact one_ne_zero h
    exact Set.indicator_of_notMem hx _

theorem indicator_one_mul_eq_indicator_preimage {α β : Type*} (s : Set β) (g : α → β) (f : α → ℝ≥0∞) (a : α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) (g a) * f a = (g ⁻¹' s).indicator f a := by
  by_cases h : g a ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h), one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show a ∉ g ⁻¹' s from h), zero_mul]

theorem euler_aux (q : ℕ) (hq : 1 < q) (s : ℝ) (hs : 1 < s) :
    (1 - (q : ℝ≥0∞) ^ (-(2 * s))) ≠ 0 ∧ (1 - (q : ℝ≥0∞) ^ (-(2 * s))) ≠ ⊤ ∧
    (1 - (q : ℝ≥0∞) ^ (1 - 2 * s)) ≠ 0 ∧ (1 - (q : ℝ≥0∞) ^ (1 - 2 * s)) ≠ ⊤ := by
  have hq' : (1 : ℝ≥0∞) < (q : ℝ≥0∞) := by exact_mod_cast hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one_of_one_lt_of_neg hq' (by linarith))).ne'
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  · exact (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one_of_one_lt_of_neg hq' (by linarith))).ne'
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

theorem euler_cancel (q : ℕ) (hq : 1 < q) (s : ℝ) (hs : 1 < s) :
    ((1 - (q : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * (1 - (q : ℝ≥0∞) ^ (1 - 2 * s))⁻¹) *
      ((1 - (q : ℝ≥0∞) ^ (-(2 * s))) * (1 - (q : ℝ≥0∞) ^ (1 - 2 * s))) = 1 := by
  obtain ⟨h1, h1', h2, h2'⟩ := euler_aux q hq s hs
  rw [mul_mul_mul_comm, ENNReal.inv_mul_cancel h1 h1', ENNReal.inv_mul_cancel h2 h2', one_mul]

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem continuous_norm_algebraNorm_det :
    Continuous fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      ‖Algebra.norm (v.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  obtain ⟨-, -, h3⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  have heq : (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      ‖Algebra.norm (v.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖) =
      fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => ∏ w : v.Extension (𝓞 L),
        ‖semiLocalHomeomorph K L v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) w‖ := by
    funext g
    rw [h3, finprod_eq_prod_of_fintype]
    rfl
  rw [heq]
  exact continuous_finsetProd _ fun w _ =>
    ((continuous_apply w).comp ((semiLocalHomeomorph K L v).continuous.comp
      (Units.continuous_val.matrix_det))).norm

theorem norm_baseChangeAlgEquiv_det_eq_one (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hg : g ∈ semiLocalIntegralSet K L v) (w : v.Extension (𝓞 L)) :
    ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) w‖ = 1 := by
  have hS : ∀ M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ i j, M i j ∈ semiLocalIntegers K L v) → M.det ∈ semiLocalIntegers K L v := by
    intro M hM
    rw [Matrix.det_fin_two]
    obtain ⟨a, ha⟩ := hM 0 0
    obtain ⟨b, hb⟩ := hM 1 1
    obtain ⟨c, hc⟩ := hM 0 1
    obtain ⟨d, hd⟩ := hM 1 0
    exact ⟨a * b - c * d, by rw [map_sub, map_mul, map_mul, ha, hb, hc, hd]⟩
  have h1 : (g : Matrix (Fin 2) (Fin 2) _).det ∈ semiLocalIntegers K L v := hS _ hg.1
  have h2 : ((g⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det ∈ semiLocalIntegers K L v := hS _ hg.2
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq, piIntegers, Set.mem_univ_pi] at h1 h2
  have hy : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (g : Matrix (Fin 2) (Fin 2) _).det w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 w))
  have hy' : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((g⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 w))
  have hn : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (g : Matrix (Fin 2) (Fin 2) _).det w‖ *
      ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        ((g⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det w‖ = 1 := by
    rw [← norm_mul, ← Pi.mul_apply, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one,
      Pi.one_apply, norm_one]
  refine le_antisymm hy ?_
  calc (1 : ℝ) = _ := hn.symm
    _ ≤ ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (g : Matrix (Fin 2) (Fin 2) _).det w‖ * 1 :=
        mul_le_mul_of_nonneg_left hy' (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_algebraNorm_det_eq_one (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hg : g ∈ semiLocalIntegralSet K L v) :
    ‖Algebra.norm (v.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ = 1 := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  obtain ⟨-, -, h3⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  rw [h3, finprod_eq_prod_of_fintype]
  exact Finset.prod_eq_one fun w _ => norm_baseChangeAlgEquiv_det_eq_one K L v g hg w

theorem norm_algebraNorm_includeRight (h2 : Module.finrank K L = 2) (s : v.adicCompletion K) :
    ‖Algebra.norm (v.adicCompletion K)
        ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s)‖ = ‖s‖ ^ 2 := by
  have hfr : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  have : (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) s := rfl
  rw [this, Algebra.norm_algebraMap, hfr, norm_pow]

end Local

section LocalIntegral

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem lintegral_indicator_mul_eq_setLIntegral (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 K)) (δw : GL (Fin 2) (L ⊗[K] w.adicCompletion K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw)) (Ww : Set (GL (Fin 2) (L ⊗[K] w.adicCompletion K)))
    (hWm : MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)] Ww) (s' : ℝ) :
    ∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw), Ww.indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τ =
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) | (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ww}, ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τ := by
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) := ⟨rfl⟩
  have hmeas : MeasurableSet {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) | (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ww} := by
    letI := AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)
    haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] w.adicCompletion K)
    exact hWm.preimage continuous_subtype_val.measurable
  rw [← lintegral_indicator hmeas]
  exact lintegral_congr fun t => indicator_one_mul_eq_indicator_preimage Ww (fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) => (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)))
    (fun t => ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s')) t

theorem lintegral_indicator_mul_eq_euler (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 K))
    (δw : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw)) (hτ : τ.IsHaarMeasure) (Ww : Set (GL (Fin 2) (L ⊗[K] w.adicCompletion K)))
    (hWm : MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)] Ww)
    (hW₀ : ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw), ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ww ↔ ∀ i j, ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L w))
    (y : GL (Fin 2) (L ⊗[K] w.adicCompletion K))
    (hy : letI := AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)
      letI := AutomorphicForm.localGLBorel K w
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * y) τ =
        Measure.map (AutomorphicForm.toTensorGL K L (w.adicCompletion K)) (AutomorphicForm.localHaar K w))
    (hU : τ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L w) = 1) (s' : ℝ) (hs' : 0 < s') :
    ∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw), Ww.indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τ =
      ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ *
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by
  rw [lintegral_indicator_mul_eq_setLIntegral K L σ w δw τ Ww hWm s']
  have hset : {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) | (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ww} =
      {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) | ∀ i j, ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L w} :=
    Set.ext fun t => hW₀ t
  rw [hset]
  have hN : ∀ (t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw)) (u : (w.adicCompletion K)ˣ),
      Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) =
        Units.map (Algebra.TensorProduct.includeRight :
          w.adicCompletion K →ₐ[K] L ⊗[K] w.adicCompletion K).toRingHom.toMonoidHom u →
      (fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) => ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s')) t = ((‖(u : w.adicCompletion K)‖₊ : ℝ≥0∞) ^ (2 * s')) := by
    intro t u hdet
    have hdet' := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map] at hdet'
    have hnorm : ‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ = ‖(u : w.adicCompletion K)‖ ^ 2 := by
      rw [hdet']
      exact norm_algebraNorm_includeRight K L w h2 (u : w.adicCompletion K)
    beta_reduce
    rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_ofNat,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity), ofReal_norm, enorm_eq_nnnorm]
  have key :=
    AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
      K L σ w δw τ hτ y 1 (by rw [one_smul]; exact hy) hU (2 * s') (fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ δw) => ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s')) hN
  rw [one_mul] at key
  exact key

end LocalIntegral

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

set_option maxHeartbeats 1600000 in

theorem cz (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τa' : Measure ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ))) (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ)))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ' : Measure ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S₀ ⊆ S₁)
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))
    (hunit : ∀ v ∉ S₁,
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
        Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))
    (s' : ℝ) (hs' : 1 < s') :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (∫⁻ t, G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') ∂τ') =
      ENNReal.ofReal cτ' *
          (∫⁻ ta, G ta.1.val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ta.1.val)| ^ s') ∂τa') *
          (ENNReal.ofReal ((NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) *
            NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re) *
            ∏ v ∈ S₁, Corr v s') := by
  classical
  letI iℝ : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iℝL : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  haveI : ∀ w, (τf' w).IsHaarMeasure := hτf'
  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)) := ⟨rfl⟩
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) := ⟨rfl⟩
  haveI : ∀ w : HeightOneSpectrum (𝓞 K), BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)) := fun w => ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hq : ∀ w : HeightOneSpectrum (𝓞 K), 1 < Ideal.absNorm w.asIdeal := fun w => NumberField.HeightOneSpectrum.one_lt_absNorm w

  have h066 := AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  have hcontA : Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => Algebra.norm ℝ X.det :=
    h066.2.2.2.2.2.2
  have hvalA : Measurable fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)) =>
      ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  have hFa : Measurable fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)) => G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val)| ^ s') :=
    (hGm.comp hvalA).mul
      (((continuous_abs.measurable.comp (hcontA.measurable.comp hvalA)).pow_const _).ennreal_ofReal)

  have hFf : ∀ w : HeightOneSpectrum (𝓞 K), Measurable fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)) => (W w).indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det (((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') := by
    intro w
    letI := AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)
    haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] w.adicCompletion K)
    have hc : Measurable fun t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)) => (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) := continuous_subtype_val.measurable
    exact ((measurable_const.indicator (hWm w)).comp hc).mul
      ((((continuous_norm_algebraNorm_det K L w).measurable.comp hc).pow_const _).ennreal_ofReal)

  have hone : ∀ w ∉ S₁, ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)), (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L w →
      (W w).indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det (((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') = 1 := by
    intro w hw t ht
    have hmem : (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ W w := (hW₀ w hw t).2 (AutomorphicForm.mem_integralUnitsSet.1 ht).1
    rw [Set.indicator_of_mem hmem, one_mul, norm_algebraNorm_det_eq_one K L w _ ht, Real.one_rpow, ENNReal.ofReal_one]

  have hF : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ),
      (∀ w ∉ S, AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
        AutomorphicForm.semiLocalIntegralSet K L w) →
      G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') =
        G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))).val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))).val)| ^ s') *
          ∏ w ∈ S, ((W w).indicator (fun _ => (1 : ℝ≥0∞)) (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s')) := by
    intro S hS t ht
    have hns :=
      AutomorphicForm.ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
        K L S (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ht
    have hind := indicator_eq_prod_indicator_ennreal U _ S W
      (fun w => AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hW₁ S hS t ht)
    rw [hind, hns, Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun w _ => norm_nonneg _),
      ← Real.finsetProd_rpow _ _ (fun w _ => norm_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_prod_of_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _), Finset.prod_mul_distrib]
    ring

  obtain ⟨hU1, hlim⟩ :=
    AutomorphicForm.measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
      K L σ δ τa' hτa' τf' hτf' τ' cτ' hcτ' S₀ hτ'prod S₁ (fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => G g.val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det g.val)| ^ s')) hFa (fun (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) => (W w).indicator (fun _ => (1 : ℝ≥0∞)) g * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s')) hFf hone (fun t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) => G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s')) hF

  have hI₁ : ∀ w ∈ S₁, (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)), (W w).indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τf' w) = Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by
    intro w hw
    rw [lintegral_indicator_mul_eq_setLIntegral K L σ w _ (τf' w) (W w) (hWm w) s']
    exact hCorr w hw s' hs'.le
  have hI₂ : ∀ w ∉ S₁, (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)), (W w).indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τf' w) = ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by
    intro w hw
    obtain ⟨y, hy⟩ := hunit w hw
    exact lintegral_indicator_mul_eq_euler K L h2 σ w _ (τf' w) (hτf' w) (W w) (hWm w) (hW₀ w hw) y hy
      (hU1 w (fun h => hw (hS₁ h))) s' (by linarith)

  have h97 := NumberField.tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT K S₁
  have hpos : 0 < (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re := h97.1 s' hs'
  have htail : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => ∏ w ∈ T \ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s'))) * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))))) := h97.2.1 s' hs'
  have hb : ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s'))) * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hpos).ne'
      (Finset.prod_ne_zero_iff.2 fun w _ =>
        mul_ne_zero (euler_aux _ (hq w) s' hs').1 (euler_aux _ (hq w) s' hs').2.2.1)
  have hg := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal cτ' * (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)), G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val)| ^ s') ∂τa') * ∏ w ∈ S₁, (Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))) htail (Or.inl hb)
  have heq : (fun S : Finset (HeightOneSpectrum (𝓞 K)) => ENNReal.ofReal cτ' * (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)), G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val)| ^ s') ∂τa') * ∏ w ∈ S, (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ)), (W w).indicator (fun _ => (1 : ℝ≥0∞)) (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * ENNReal.ofReal (‖Algebra.norm (w.adicCompletion K) (Matrix.det (((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ^ s') ∂τf' w)) =ᶠ[atTop]
      (fun T : Finset (HeightOneSpectrum (𝓞 K)) => (ENNReal.ofReal cτ' * (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)), G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).val)| ^ s') ∂τa') * ∏ w ∈ S₁, (Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))) *
        ∏ w ∈ T \ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) := by
    filter_upwards [eventually_ge_atTop S₁] with T hT
    rw [← Finset.prod_sdiff hT, Finset.prod_congr rfl (fun w hw => hI₂ w (Finset.mem_sdiff.1 hw).2),
      Finset.prod_congr rfl (fun w hw => hI₁ w hw)]
    ring
  have hZ := tendsto_nhds_unique hlim (hg.congr' heq.symm)
  refine hZ.trans ?_

  have hprod : (∏ w ∈ S₁, (Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))) * (ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s'))) * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')))) =
      ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, Corr w s' := by
    calc (∏ w ∈ S₁, (Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))) * (ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s'))) * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))))
        = ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, ((Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s'))) * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')))) := by
          simp only [Finset.prod_mul_distrib]; ring
      _ = ENNReal.ofReal (NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) * NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re * ∏ w ∈ S₁, Corr w s' := by
          congr 1
          exact Finset.prod_congr rfl fun w _ => by rw [mul_assoc, euler_cancel _ (hq w) s' hs', mul_one]
  rw [mul_assoc _ (∏ w ∈ S₁, (Corr w s' * ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))), hprod]

end Main

end Ws46.CZ

set_option linter.unusedVariables false in
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
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S₀ ⊆ S₁)
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))
    (hunit : ∀ v ∉ S₁,
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
        Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))
    (hCorr₁ : ∀ v ∈ S₁, Corr v 1 ≠ ⊤ ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)))
 :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∀ s' : ℝ, 1 < s' →
      (∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ →
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
            ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
              X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
        ∃ r C : ℝ, (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s' - 1) < r ∧
          ∀ cc : Fin n₂ → ℝ, G (∑ i, cc i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖cc‖) ^ (-r))) →
      (∫⁻ t, G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') ∂τ') =
        ENNReal.ofReal cτ' *
          (∫⁻ ta, G ta.1.val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ta.1.val)| ^ s') ∂τa') *
          (ENNReal.ofReal ((NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) *
            NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re) *
            ∏ v ∈ S₁, Corr v s') := by
  intro s' hs' _
  exact Ws46.CZ.cz K L h2 σ _ τa' hτa' τf' hτf' S₀ τ' cτ' hcτ' hτ'prod v U G hGm S₁ hS₁ W hWm hW₀ hW₁
    (fun w hw => by obtain ⟨y, -, hy⟩ := hunit w hw; exact ⟨y, hy⟩) Corr hCorr s' hs'

end S_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
end P2MW
export P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg (solution)
