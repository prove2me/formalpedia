-- Prove2me | solution 1 for AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4602d28e-918c-5962-9d14-26ad7a6ca237

import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
import Theorems.Thm_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

noncomputable section

namespace Ws23
namespace V2D

open MeasureTheory
open scoped ENNReal

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

omit [MeasurableSpace G] [MeasurableMul G] in
theorem image_mul_left_eq_preimage (z : G) (A : Set G) :
    (fun x => z * x) '' A = (fun x => z⁻¹ * x) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨z⁻¹ * x, hx, by simp⟩

theorem measurableSet_image_mul_left (z : G) {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet ((fun x => z * x) '' A) := by
  rw [image_mul_left_eq_preimage]
  exact measurable_const_mul _ hA

theorem setLIntegral_image_mul_left (μ : Measure G) [μ.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (z : G) (r : ℝ≥0∞) (hr : r ≠ ∞) (hf : ∀ x, f (z * x) = r * f x)
    {A : Set G} (hA : MeasurableSet A) :
    ∫⁻ x in (fun x => z * x) '' A, f x ∂μ = r * ∫⁻ x in A, f x ∂μ := by
  have hmeas := measurableSet_image_mul_left z hA
  have hind : ∀ x, ((fun x => z * x) '' A).indicator f (z * x) = r * A.indicator f x := by
    intro x
    by_cases hx : x ∈ A
    · have hx' : z * x ∈ (fun x => z * x) '' A := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hf]
    · have hx' : z * x ∉ (fun x => z * x) '' A := by
        rintro ⟨y, hy, hyx⟩
        exact hx (mul_left_cancel hyx ▸ hy)
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  rw [← lintegral_indicator hmeas, ← lintegral_indicator hA,
    ← lintegral_mul_left_eq_self (fun x => ((fun x => z * x) '' A).indicator f x) z]
  simp only [hind]
  rw [lintegral_const_mul' _ _ hr]

omit [Group G] [MeasurableMul G] in

theorem lintegral_eq_top_of_disjoint_of_le (μ : Measure G) (f : G → ℝ≥0∞)
    (A : ℕ → Set G) (hA : ∀ m, MeasurableSet (A m))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (W : Set G) (hsub : ∀ m, A m ⊆ W)
    (I : ℝ≥0∞) (hI : I ≠ 0) (hle : ∀ m, I ≤ ∫⁻ x in A m, f x ∂μ) :
    ∫⁻ x in W, f x ∂μ = ⊤ := by
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, I := (ENNReal.tsum_const_eq_top_of_ne_zero hI).symm
    _ ≤ ∑' m : ℕ, ∫⁻ x in A m, f x ∂μ := ENNReal.tsum_le_tsum hle
    _ = ∫⁻ x in ⋃ m, A m, f x ∂μ := (lintegral_iUnion hA hdisj f).symm
    _ ≤ ∫⁻ x in W, f x ∂μ := lintegral_mono_set (Set.iUnion_subset hsub)

end Generic

end Ws23.V2D

end

noncomputable section

namespace Ws23
namespace V2D

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace
open scoped ENNReal

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem snd_pow_adele (x : AdeleRing (𝓞 F) F) (n : ℕ) : (x ^ n).2 = x.2 ^ n := rfl

theorem fst_pow_adele_apply (x : AdeleRing (𝓞 F) F) (n : ℕ) (v : InfinitePlace F) :
    (x ^ n).1 v = (x.1 v) ^ n := rfl

theorem val_archCentralUnit_pow_snd (w : InfinitePlace F) (a : (w.Completion)ˣ) (n : ℕ) :
    (((archCentralUnit F w a) ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rw [Units.val_pow_eq_pow_val, snd_pow_adele, archCentralUnit_snd, one_pow]

theorem val_archCentralUnit_pow_fst_self (w : InfinitePlace F) (a : (w.Completion)ˣ) (n : ℕ) :
    (((archCentralUnit F w a) ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = (a : w.Completion) ^ n := by
  rw [Units.val_pow_eq_pow_val, fst_pow_adele_apply, archCentralUnit_fst_self]

theorem val_archCentralUnit_pow_fst_of_ne (w : InfinitePlace F) (a : (w.Completion)ˣ) (n : ℕ)
    {v : InfinitePlace F} (hv : v ≠ w) :
    (((archCentralUnit F w a) ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = 1 := by
  rw [Units.val_pow_eq_pow_val, fst_pow_adele_apply, archCentralUnit_fst_of_ne w a hv, one_pow]

theorem val_archCentralUnit_pow_fst_ne_zero (w : InfinitePlace F) (a : (w.Completion)ˣ) (n : ℕ)
    (v : InfinitePlace F) :
    (((archCentralUnit F w a) ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v ≠ 0 := by
  by_cases hv : v = w
  · subst hv
    rw [val_archCentralUnit_pow_fst_self]
    exact pow_ne_zero _ a.ne_zero
  · rw [val_archCentralUnit_pow_fst_of_ne w a n hv]
    exact one_ne_zero

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * h = h * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

theorem archDetNorm_centralScalar_mul' (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F w * g)
      = (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (w : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem centralScalar_mul_mem_centreCutSiegelSet {c u d₁ d₂ e₁ e₂ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (hdet : ∀ v : InfinitePlace F,
      (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g ∈ Set.Icc e₁ e₂) :
    centralScalar (𝓞 F) F w * g ∈ centreCutSiegelSet F c u e₁ e₂ := by
  obtain ⟨h1, h2, h3, -⟩ := hg
  set s := centralScalar (𝓞 F) F w with hs
  have h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w := centralScalar_apply_eq w 0
  have h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 := centralScalar_apply_ne w (by decide)
  have h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := centralScalar_apply_ne w (by decide)
  have h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w := centralScalar_apply_eq w 1
  have hglFin : glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have hcomp00 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 0 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h00]
  have hcomp01 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 1 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h01]; rfl
  have hcomp10 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h10]; rfl
  have hcomp11 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 1 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h11]
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, map_mul, localHeight_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h2 v
  · rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h3 v
  · rw [hs, archDetNorm_centralScalar_mul']
    exact hdet v

theorem archDetNorm_mul (v : InfinitePlace F) (g x : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (g * x) = archDetNorm v g * archDetNorm v x := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

theorem centralScalar_pow_mul_mem_iUnion {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hd₁ : d₁ ≤ 0) (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ ≤ 1) (n : ℕ)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) :
    centralScalar (𝓞 F) F ((archCentralUnit F w a) ^ n) * g
      ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  rw [Set.mem_iUnion₂] at hg ⊢
  obtain ⟨x, hx, s, hs, rfl⟩ := hg
  refine ⟨x, hx, centralScalar (𝓞 F) F ((archCentralUnit F w a) ^ n) * s, ?_, ?_⟩
  · refine centralScalar_mul_mem_centreCutSiegelSet (val_archCentralUnit_pow_snd w a n)
      (val_archCentralUnit_pow_fst_ne_zero w a n) hs fun v => ?_
    have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 v
    have hpos := archDetNorm_pos v s
    by_cases hv : v = w
    · subst hv
      rw [val_archCentralUnit_pow_fst_self, norm_pow]
      have hle : ‖(a : v.Completion)‖ ^ n * ‖(a : v.Completion)‖ ^ n ≤ 1 :=
        mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (by positivity) (pow_le_one₀ (norm_nonneg _) ha)
      refine ⟨hd₁.trans (by positivity), ?_⟩
      calc ‖(a : v.Completion)‖ ^ n * ‖(a : v.Completion)‖ ^ n * archDetNorm v s
          ≤ 1 * archDetNorm v s := by gcongr
        _ = archDetNorm v s := one_mul _
        _ ≤ d₂ := hdet.2
    · rw [val_archCentralUnit_pow_fst_of_ne w a n hv, norm_one, one_mul, one_mul]
      exact hdet
  · show centralScalar (𝓞 F) F _ * s * x = centralScalar (𝓞 F) F _ * (s * x)
    rw [mul_assoc]

theorem archDetNorm_centralScalar_pow_mul (w : InfinitePlace F) (a : (w.Completion)ˣ) (n : ℕ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (centralScalar (𝓞 F) F ((archCentralUnit F w a) ^ n) * g)
      = (‖(a : w.Completion)‖ ^ 2) ^ n * archDetNorm w g := by
  rw [archDetNorm_centralScalar_mul', val_archCentralUnit_pow_fst_self, norm_pow]
  ring

theorem measurableSet_iUnion_centreCutSiegelSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

end Adelic

end Ws23.V2D

end

noncomputable section

namespace Ws23
namespace V2D

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicHaar MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace
open scoped ENNReal

section PlaceAlgebra

variable {F : Type} [Field F]

open NumberField.InfinitePlace.Completion in

def Xc (v : InfinitePlace F) (g : GL (Fin 2) v.Completion) : ℂ :=
  extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 0)
      * (starRingEnd ℂ) (extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 0))
    + extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 1)
      * (starRingEnd ℂ) (extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 1))

theorem lagrange_identity (α β γ δ : ℂ) :
    (‖α‖ ^ 2 + ‖β‖ ^ 2) * (‖γ‖ ^ 2 + ‖δ‖ ^ 2) - ‖α * δ - β * γ‖ ^ 2
      = ‖α * (starRingEnd ℂ) γ + β * (starRingEnd ℂ) δ‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

open NumberField.InfinitePlace.Completion in
theorem norm_extensionEmbedding (v : InfinitePlace F) (x : v.Completion) :
    ‖extensionEmbedding v x‖ = ‖x‖ :=
  (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) x

open NumberField.InfinitePlace.Completion in

theorem xWindowSq_eq_norm_Xc_sq_div (v : InfinitePlace F) (g : GL (Fin 2) v.Completion) :
    xWindowSq g = ‖Xc v g‖ ^ 2 / rowNormSq (g : Matrix (Fin 2) (Fin 2) v.Completion) ^ 2 := by
  have hR := rowNormSq_pos g
  set ι := extensionEmbedding v with hι
  have hn : ∀ x : v.Completion, ‖x‖ = ‖ι x‖ := fun x => (norm_extensionEmbedding v x).symm
  have hdet : ‖(g : Matrix (Fin 2) (Fin 2) v.Completion).det‖
      = ‖ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 0) * ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 1)
          - ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 1) * ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 0)‖ := by
    rw [Matrix.det_fin_two, hn, map_sub, map_mul, map_mul]
  have hlag := lagrange_identity (ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 0))
    (ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 1)) (ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 0))
    (ι ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 1))
  have hX : ‖Xc v g‖ ^ 2 = topNormSq (g : Matrix (Fin 2) (Fin 2) v.Completion)
      * rowNormSq (g : Matrix (Fin 2) (Fin 2) v.Completion) - ‖(g : Matrix (Fin 2) (Fin 2) v.Completion).det‖ ^ 2 := by
    unfold topNormSq rowNormSq
    rw [hn ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 0), hn ((g : Matrix (Fin 2) (Fin 2) v.Completion) 0 1),
      hn ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 0), hn ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 1), hdet, hlag]
    rfl
  unfold xWindowSq localHeight
  rw [hX, div_pow]
  field_simp

theorem ut_mul_apply {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, β; 0, 1]
        (by rw [Matrix.det_fin_two_of]; simpa using hα) * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      = if i = 0 then α * (g : Matrix (Fin 2) (Fin 2) K) 0 j + β * (g : Matrix (Fin 2) (Fin 2) K) 1 j
        else (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

end PlaceAlgebra

section PlaceUT

variable {F : Type} [Field F]

def ut {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, β; 0, 1] (by rw [Matrix.det_fin_two_of]; simpa using hα)

theorem ut_val {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) :
    ((ut α β hα : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![α, β; 0, 1] := rfl

theorem ut_mul_apply_top {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) (j : Fin 2) :
    ((ut α β hα * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 j
      = α * (g : Matrix (Fin 2) (Fin 2) K) 0 j + β * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ut_val]
  simp

theorem ut_mul_apply_bot {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) (j : Fin 2) :
    ((ut α β hα * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j = (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ut_val]
  simp

theorem rowNormSq_ut_mul {K : Type*} [NormedField K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) :
    rowNormSq ((ut α β hα * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  rw [ut_mul_apply_bot, ut_mul_apply_bot]

theorem det_ut_mul {K : Type*} [Field K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) :
    ((ut α β hα * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = α * (g : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Units.val_mul, Matrix.det_mul, ut_val, Matrix.det_fin_two_of]
  ring

theorem localHeight_ut_mul {K : Type*} [NormedField K] (α β : K) (hα : α ≠ 0) (g : GL (Fin 2) K) :
    localHeight (ut α β hα * g) = ‖α‖ * localHeight g := by
  unfold localHeight
  rw [rowNormSq_ut_mul, det_ut_mul, norm_mul, mul_div_assoc]

open NumberField.InfinitePlace.Completion in
theorem Xc_ut_mul (v : InfinitePlace F) (α β : v.Completion) (hα : α ≠ 0) (g : GL (Fin 2) v.Completion) :
    Xc v (ut α β hα * g) = extensionEmbedding v α * Xc v g
      + extensionEmbedding v β * (rowNormSq (g : Matrix (Fin 2) (Fin 2) v.Completion) : ℂ) := by
  unfold Xc rowNormSq
  rw [ut_mul_apply_top, ut_mul_apply_top, ut_mul_apply_bot, ut_mul_apply_bot]
  simp only [map_add, map_mul]
  rw [← norm_extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 0),
    ← norm_extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) 1 1)]
  simp only [Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  ring

end PlaceUT

section AdelicUT

variable {F : Type} [Field F] [NumberField F]

def utAdeleVal (α β : (v : InfinitePlace F) → v.Completion) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  !![(((α : InfiniteAdeleRing F)), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)),
      (((β : InfiniteAdeleRing F)), (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)); 0, 1]

theorem utAdeleVal_apply_00 (α β : (v : InfinitePlace F) → v.Completion) :
    utAdeleVal α β 0 0 = (((α : InfiniteAdeleRing F)), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := rfl
theorem utAdeleVal_apply_01 (α β : (v : InfinitePlace F) → v.Completion) :
    utAdeleVal α β 0 1 = (((β : InfiniteAdeleRing F)), (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := rfl
theorem utAdeleVal_apply_10 (α β : (v : InfinitePlace F) → v.Completion) : utAdeleVal α β 1 0 = 0 := rfl
theorem utAdeleVal_apply_11 (α β : (v : InfinitePlace F) → v.Completion) : utAdeleVal α β 1 1 = 1 := rfl

theorem utAdeleVal_mul (α β α' β' : (v : InfinitePlace F) → v.Completion) :
    utAdeleVal α β * utAdeleVal α' β' = utAdeleVal (α * α') (α * β' + β) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [utAdeleVal_apply_00, utAdeleVal_apply_01, utAdeleVal_apply_10, utAdeleVal_apply_11,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_zero, add_zero, zero_mul, zero_add, mul_one]
  · exact Prod.ext (funext fun v => rfl) (mul_one 1)
  · refine Prod.ext (funext fun v => ?_) ?_
    · show α v * β' v + β v = α v * β' v + β v
      rfl
    · show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 0 + 0 = 0
      rw [mul_zero, add_zero]

theorem utAdeleVal_one_zero : utAdeleVal (F := F) 1 0 = 1 := by
  rw [utAdeleVal, Matrix.one_fin_two]
  rfl

def liftUT (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0) : AdelicGL2 (𝓞 F) F where
  val := utAdeleVal α β
  inv := utAdeleVal (fun v => (α v)⁻¹) (fun v => -((α v)⁻¹ * β v))
  val_inv := by
    rw [utAdeleVal_mul]
    convert utAdeleVal_one_zero (F := F) using 2
    · exact funext fun v => mul_inv_cancel₀ (hα v)
    · funext v
      show α v * -((α v)⁻¹ * β v) + β v = 0
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ (hα v), one_mul, neg_add_cancel]
  inv_val := by
    rw [utAdeleVal_mul]
    convert utAdeleVal_one_zero (F := F) using 2
    · exact funext fun v => inv_mul_cancel₀ (hα v)
    · funext v
      show (α v)⁻¹ * β v + -((α v)⁻¹ * β v) = 0
      rw [add_neg_cancel]

theorem glFin_liftUT (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0) :
    glFin (𝓞 F) F (liftUT α β hα) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply]
  show (utAdeleVal α β i j).2 = (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j
  fin_cases i <;> fin_cases j <;>
    simp only [utAdeleVal_apply_00, utAdeleVal_apply_01, utAdeleVal_apply_10, utAdeleVal_apply_11,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true] <;> rfl

theorem aC_liftUT (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0) (v : InfinitePlace F) :
    archComponent F v (glArch (𝓞 F) F (liftUT α β hα)) = ut (α v) (β v) (hα v) := by
  apply Units.ext
  ext i j : 1
  rw [archComponent_apply, glArch_apply, ut_val]
  show (utAdeleVal α β i j).1 v = _
  fin_cases i <;> fin_cases j <;>
    simp only [utAdeleVal_apply_00, utAdeleVal_apply_01, utAdeleVal_apply_10, utAdeleVal_apply_11,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;> rfl

theorem aC_liftUT_mul (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0) (v : InfinitePlace F)
    (g : AdelicGL2 (𝓞 F) F) :
    archComponent F v (glArch (𝓞 F) F (liftUT α β hα * g))
      = ut (α v) (β v) (hα v) * archComponent F v (glArch (𝓞 F) F g) := by
  rw [map_mul, map_mul, aC_liftUT]

theorem archDetNorm_liftUT_mul (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0)
    (v : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (liftUT α β hα * g) = ‖α v‖ * archDetNorm v g := by
  unfold archDetNorm
  rw [aC_liftUT_mul, det_ut_mul, norm_mul]

theorem glFin_liftUT_mul (α β : (v : InfinitePlace F) → v.Completion) (hα : ∀ v, α v ≠ 0)
    (g : AdelicGL2 (𝓞 F) F) : glFin (𝓞 F) F (liftUT α β hα * g) = glFin (𝓞 F) F g := by
  rw [map_mul, glFin_liftUT, one_mul]

end AdelicUT

section Analysis

variable {F : Type} [Field F]

open NumberField.InfinitePlace.Completion

theorem norm_ratCast_completion (w : InfinitePlace F) (q : ℚ) :
    ‖((q : ℚ) : w.Completion)‖ = |(q : ℝ)| := by
  rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem im_extensionEmbedding_of_isReal {v : InfinitePlace F} (hv : v.IsReal) (x : v.Completion) :
    (extensionEmbedding v x).im = 0 := by
  rw [← extensionEmbeddingOfIsReal_apply hv]
  exact Complex.ofReal_im _

theorem exists_extensionEmbedding_eq (v : InfinitePlace F) (ζ : ℂ) (hζ : v.IsReal → ζ.im = 0) :
    ∃ b : v.Completion, extensionEmbedding v b = ζ := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨b, hb⟩ := surjective_extensionEmbeddingOfIsReal hv ζ.re
    refine ⟨b, ?_⟩
    rw [← extensionEmbeddingOfIsReal_apply hv, hb]
    exact Complex.ext rfl (by rw [Complex.ofReal_im, hζ hv])
  · exact surjective_extensionEmbedding_of_isComplex hv ζ

theorem im_Xc_of_isReal {v : InfinitePlace F} (hv : v.IsReal) (g : GL (Fin 2) v.Completion) : (Xc v g).im = 0 := by
  simp only [Xc, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    im_extensionEmbedding_of_isReal hv, zero_mul, mul_zero, neg_zero, add_zero]

theorem tendsto_ratCast_completion (w : InfinitePlace F) {q : ℕ → ℚ} {q₀ : ℚ}
    (h : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (q₀ : ℝ))) :
    Filter.Tendsto (fun n => ((q n : ℚ) : w.Completion)) Filter.atTop (nhds ((q₀ : ℚ) : w.Completion)) := by
  haveI : CharZero w.Completion := (extensionEmbedding w).charZero
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have : (fun n => ‖((q n : ℚ) : w.Completion) - ((q₀ : ℚ) : w.Completion)‖) = fun n => |((q n : ℚ) : ℝ) - (q₀ : ℝ)| := by
    funext n
    rw [← Rat.cast_sub, norm_ratCast_completion, Rat.cast_sub]
  rw [this]
  have h0 : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ) - (q₀ : ℝ)) Filter.atTop (nhds 0) := by
    simpa using h.sub_const (q₀ : ℝ)
  simpa using h0.abs

end Analysis

section Positivity

variable {F : Type} [Field F] [NumberField F]

open NumberField.InfinitePlace.Completion Filter Topology

theorem tendsto_liftUT {α β : ℕ → (v : InfinitePlace F) → v.Completion} (hα : ∀ n v, α n v ≠ 0)
    (hαt : ∀ v, Tendsto (fun n => α n v) atTop (𝓝 1)) (hβt : ∀ v, Tendsto (fun n => β n v) atTop (𝓝 0)) :
    Tendsto (fun n => liftUT (α n) (β n) (hα n)) atTop (𝓝 1) := by

  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  ·
    show Tendsto (fun n => utAdeleVal (α n) (β n)) atTop (𝓝 ((1 : AdelicGL2 (𝓞 F) F) : Matrix _ _ _))
    rw [show ((1 : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = utAdeleVal 1 0 from
      utAdeleVal_one_zero.symm]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    fin_cases i <;> fin_cases j
    · show Tendsto (fun n => utAdeleVal (α n) (β n) 0 0) atTop (𝓝 (utAdeleVal 1 0 0 0))
      simp only [utAdeleVal_apply_00]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun v => hαt v) tendsto_const_nhds
    · show Tendsto (fun n => utAdeleVal (α n) (β n) 0 1) atTop (𝓝 (utAdeleVal 1 0 0 1))
      simp only [utAdeleVal_apply_01]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun v => hβt v) tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  ·
    have h1 : ((1 : AdelicGL2 (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) = 1 := inv_one
    show Tendsto (fun n => MulOpposite.op ((((liftUT (α n) (β n) (hα n))⁻¹ : AdelicGL2 (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) atTop
      (𝓝 (MulOpposite.op ((((1 : AdelicGL2 (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
    rw [h1]
    refine (MulOpposite.continuous_op.tendsto _).comp ?_
    show Tendsto (fun n => utAdeleVal (fun v => (α n v)⁻¹) (fun v => -((α n v)⁻¹ * β n v))) atTop
      (𝓝 ((1 : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
    rw [show ((1 : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = utAdeleVal 1 0 from
      utAdeleVal_one_zero.symm]
    have hαi : ∀ v, Tendsto (fun n => (α n v)⁻¹) atTop (𝓝 1) := fun v => by
      simpa using (hαt v).inv₀ one_ne_zero
    have hβi : ∀ v, Tendsto (fun n => -((α n v)⁻¹ * β n v)) atTop (𝓝 0) := fun v => by
      simpa using ((hαi v).mul (hβt v)).neg
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    fin_cases i <;> fin_cases j
    · show Tendsto (fun n => utAdeleVal (fun v => (α n v)⁻¹) (fun v => -((α n v)⁻¹ * β n v)) 0 0) atTop
        (𝓝 (utAdeleVal 1 0 0 0))
      simp only [utAdeleVal_apply_00]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun v => hαi v) tendsto_const_nhds
    · show Tendsto (fun n => utAdeleVal (fun v => (α n v)⁻¹) (fun v => -((α n v)⁻¹ * β n v)) 0 1) atTop
        (𝓝 (utAdeleVal 1 0 0 1))
      simp only [utAdeleVal_apply_01]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun v => hβi v) tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds

theorem setLIntegral_enorm_sq_ne_zero {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hu : u ≠ 0) (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (hcovE : ∀ e : ℝ, 0 < e → CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e e))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    ∫⁻ g in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ 0 := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hD

  set e : ℝ := d₂ / 2 with he
  have he0 : 0 < e := by positivity
  obtain ⟨g₀, hg₀⟩ := hφ0
  obtain ⟨γ, z, hmem⟩ := hcovE e he0 g₀
  obtain ⟨x₀, hx₀, s, hs, hsx⟩ := Set.mem_iUnion₂.mp hmem
  have hsx' : s * x₀ = globalPoints (𝓞 F) F γ * g₀ * centralScalar (𝓞 F) F z := hsx
  have hφs : φ (s * x₀) ≠ 0 := by
    rw [hsx', mul_assoc, hγ, ← centralScalar_mul_comm, hω]
    exact mul_ne_zero (Units.ne_zero _) hg₀
  obtain ⟨hsfin, hsh, hsx2, hsdet⟩ := mem_centreCutSiegelSet_iff.mp hs
  have hsdet' : ∀ v, archDetNorm v s = e := fun v => le_antisymm (hsdet v).2 (hsdet v).1

  have hpre : ∀ v : InfinitePlace F, ∃ b : v.Completion,
      extensionEmbedding v b = -(Xc v (archComponent F v (glArch (𝓞 F) F s)))
        / ((rowNormSq (((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion)) : ℝ) : ℂ) := by
    intro v
    refine exists_extensionEmbedding_eq v _ fun hv => ?_
    rw [Complex.div_ofReal_im, Complex.neg_im, im_Xc_of_isReal hv, neg_zero, zero_div]
  choose cv hcv using hpre
  set εq : ℕ → ℚ := fun n => 1 / ((n : ℚ) + 4) with hεq
  have hεr : ∀ n, ((εq n : ℚ) : ℝ) = 1 / ((n : ℝ) + 4) := fun n => by rw [hεq]; push_cast; ring
  have hεq0 : ∀ n, (0 : ℝ) < (εq n : ℝ) := fun n => by rw [hεr]; positivity
  have hεq1 : ∀ n, ((εq n : ℚ) : ℝ) ≤ 1 / 4 := fun n => by
    rw [hεr]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
  set α : ℕ → (v : InfinitePlace F) → v.Completion := fun n v => ((1 + εq n : ℚ) : v.Completion) with hα
  set β : ℕ → (v : InfinitePlace F) → v.Completion :=
    fun n v => ((2 * εq n : ℚ) : v.Completion) * α n v * cv v with hβ
  have hια : ∀ n v, extensionEmbedding v (α n v) = ((1 + εq n : ℚ) : ℝ) := fun n v => by
    rw [hα]
    simp only [map_ratCast, Complex.ofReal_ratCast]
  have hnα : ∀ n v, ‖α n v‖ = 1 + εq n := fun n v => by
    rw [← norm_extensionEmbedding, hια, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    push_cast
    ring
  have hα0 : ∀ n v, α n v ≠ 0 := fun n v => by
    rw [← norm_pos_iff, hnα]; positivity

  have hεt : Tendsto (fun n => ((εq n : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
      ring
    exact h1.congr fun n => (hεr n).symm
  have hαt : ∀ v, Tendsto (fun n => α n v) atTop (𝓝 1) := fun v => by
    have : Tendsto (fun n => ((1 + εq n : ℚ) : ℝ)) atTop (𝓝 ((1 : ℚ) : ℝ)) := by
      push_cast
      simpa using hεt.const_add 1
    simpa using tendsto_ratCast_completion v this
  have hβt : ∀ v, Tendsto (fun n => β n v) atTop (𝓝 0) := fun v => by
    have h2 : Tendsto (fun n => ((2 * εq n : ℚ) : v.Completion)) atTop (𝓝 ((0 : ℚ) : v.Completion)) := by
      refine tendsto_ratCast_completion v ?_
      push_cast
      simpa using hεt.const_mul 2
    have h3 : Tendsto (fun n => ((2 * εq n : ℚ) : v.Completion) * α n v * cv v) atTop
        (𝓝 (((0 : ℚ) : v.Completion) * 1 * cv v)) := (h2.mul (hαt v)).mul_const (cv v)
    rw [Rat.cast_zero, zero_mul, zero_mul] at h3
    exact h3
  have hPt := tendsto_liftUT hα0 hαt hβt

  have hN : IsOpen {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := isOpen_ne_fun hφc continuous_const
  have hev : ∀ᶠ n in atTop, φ (liftUT (α n) (β n) (hα0 n) * (s * x₀)) ≠ 0 := by
    have hcont : Tendsto (fun n => liftUT (α n) (β n) (hα0 n) * (s * x₀)) atTop (𝓝 (1 * (s * x₀))) :=
      hPt.mul tendsto_const_nhds
    rw [one_mul] at hcont
    exact hcont.eventually (hN.mem_nhds hφs)
  obtain ⟨n, hn⟩ := hev.exists
  set P := liftUT (α n) (β n) (hα0 n) with hP

  set V : Set (AdelicGL2 (𝓞 F) F) :=
    {g | glFin (𝓞 F) F (g * x₀⁻¹) ∈ finiteIntegralGL2 (𝓞 F) F} ∩
      ⋂ v : InfinitePlace F, ({g | c < localHeight (archComponent F v (glArch (𝓞 F) F (g * x₀⁻¹)))} ∩
        ({g | xWindowSq (archComponent F v (glArch (𝓞 F) F (g * x₀⁻¹))) < u ^ 2} ∩
         {g | archDetNorm v (g * x₀⁻¹) ∈ Set.Ioo d₁ d₂})) with hV
  have hVopen : IsOpen V := by
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun v => IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
    · exact (isOpen_finiteLevelZero (𝓞 F) F top_ne_bot).preimage
        ((continuous_glFin (𝓞 F) F).comp (continuous_mul_const x₀⁻¹))
    · exact isOpen_lt continuous_const ((continuous_localHeight_place v).comp (continuous_mul_const x₀⁻¹))
    · exact isOpen_lt ((continuous_xWindowSq_place v).comp (continuous_mul_const x₀⁻¹)) continuous_const
    · exact isOpen_Ioo.preimage ((continuous_archDetNorm v).comp (continuous_mul_const x₀⁻¹))
  have hVsub : V ⊆ D := by
    intro g hg
    simp only [hV, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hg
    refine Set.mem_iUnion₂.mpr ⟨x₀, hx₀, g * x₀⁻¹, ?_, inv_mul_cancel_right g x₀⟩
    exact ⟨hg.1, fun v => (hg.2 v).1.le, fun v => (hg.2 v).2.1.le, fun v => ⟨(hg.2 v).2.2.1.le, (hg.2 v).2.2.2.le⟩⟩

  have hκ : (1 + (εq n : ℝ)) * (1 - 2 * (εq n : ℝ)) < 1 := by
    have h0 : (0 : ℝ) < εq n := hεq0 n
    nlinarith
  have hκ0 : 0 ≤ (1 + (εq n : ℝ)) * (1 - 2 * (εq n : ℝ)) := by
    have h0 : (0 : ℝ) < εq n := hεq0 n
    have h1 : (εq n : ℝ) ≤ 1 / 4 := hεq1 n
    nlinarith
  have hPmem : P * (s * x₀) ∈ V := by
    have hPs : P * (s * x₀) * x₀⁻¹ = P * s := by rw [← mul_assoc, mul_inv_cancel_right]
    simp only [hV, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, hPs]
    refine ⟨?_, fun v => ⟨?_, ?_, ?_⟩⟩
    · rw [hP, glFin_liftUT_mul]
      exact hsfin
    · rw [hP, aC_liftUT_mul, localHeight_ut_mul, hnα]
      have hh := localHeight_pos (archComponent F v (glArch (𝓞 F) F s))
      have h0 : (0 : ℝ) < εq n := hεq0 n
      calc c ≤ localHeight (archComponent F v (glArch (𝓞 F) F s)) := hsh v
        _ < (1 + (εq n : ℝ)) * localHeight (archComponent F v (glArch (𝓞 F) F s)) := by nlinarith
    · have hιβ : extensionEmbedding v (β n v) = ((2 * εq n : ℚ) : ℝ) * ((1 + εq n : ℚ) : ℝ)
          * extensionEmbedding v (cv v) := by
        rw [hβ]
        simp only [map_mul, map_ratCast, Complex.ofReal_ratCast, hια]
      rw [hP, aC_liftUT_mul, xWindowSq_eq_norm_Xc_sq_div, Xc_ut_mul, rowNormSq_ut_mul, hιβ, hcv, hια]
      have hR := rowNormSq_pos (archComponent F v (glArch (𝓞 F) F s))
      have hRne : ((rowNormSq (((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
          Matrix (Fin 2) (Fin 2) v.Completion)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      have hsimp : (((1 + εq n : ℚ) : ℝ) : ℂ) * Xc v (archComponent F v (glArch (𝓞 F) F s))
          + ((2 * εq n : ℚ) : ℝ) * ((1 + εq n : ℚ) : ℝ)
            * (-(Xc v (archComponent F v (glArch (𝓞 F) F s))) / ((rowNormSq (((archComponent F v (glArch (𝓞 F) F s) :
                GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion)) : ℝ) : ℂ))
            * ((rowNormSq (((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
                Matrix (Fin 2) (Fin 2) v.Completion)) : ℝ) : ℂ)
          = ((((1 + ((εq n : ℚ) : ℝ)) * (1 - 2 * ((εq n : ℚ) : ℝ)) : ℝ)) : ℂ) * Xc v (archComponent F v (glArch (𝓞 F) F s)) := by
        field_simp
        push_cast
        ring
      rw [hsimp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0, mul_pow, mul_div_assoc,
        ← xWindowSq_eq_norm_Xc_sq_div]
      have hx := hsx2 v
      have hu2 : 0 < u ^ 2 := by positivity
      calc ((1 + (εq n : ℝ)) * (1 - 2 * (εq n : ℝ))) ^ 2 * xWindowSq (archComponent F v (glArch (𝓞 F) F s))
          ≤ ((1 + (εq n : ℝ)) * (1 - 2 * (εq n : ℝ))) ^ 2 * u ^ 2 := by gcongr
        _ < 1 * u ^ 2 := by
            gcongr
            calc ((1 + (εq n : ℝ)) * (1 - 2 * (εq n : ℝ))) ^ 2
                < 1 ^ 2 := by gcongr
              _ = 1 := one_pow 2
        _ = u ^ 2 := one_mul _
    · rw [hP, archDetNorm_liftUT_mul, hnα, hsdet']
      have h0 : (0 : ℝ) < εq n := hεq0 n
      have h1 : (εq n : ℝ) ≤ 1 / 4 := hεq1 n
      constructor
      · calc d₁ ≤ 0 := hd₁
          _ < (1 + (εq n : ℝ)) * e := by positivity
      · calc (1 + (εq n : ℝ)) * e ≤ (1 + 1 / 4) * (d₂ / 2) := by gcongr
          _ < d₂ := by linarith

  have hNVopen : IsOpen ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩ V) := hN.inter hVopen
  have hNVpos : 0 < μ ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩ V) := hNVopen.measure_pos μ ⟨_, hn, hPmem⟩
  have hfm : Measurable fun g : AdelicGL2 (𝓞 F) F => ‖φ g‖ₑ ^ 2 := (hφc.measurable.enorm).pow_const 2
  intro h0
  have hle : ∫⁻ g in {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩ V, ‖φ g‖ₑ ^ 2 ∂μ ≤ ∫⁻ g in D, ‖φ g‖ₑ ^ 2 ∂μ :=
    lintegral_mono_set (Set.inter_subset_right.trans hVsub)
  rw [h0, nonpos_iff_eq_zero] at hle
  have hsupp : Function.support (fun g : AdelicGL2 (𝓞 F) F => ‖φ g‖ₑ ^ 2) = {g | φ g ≠ 0} := by
    ext g
    simp
  have hpos : 0 < ∫⁻ g in {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩ V, ‖φ g‖ₑ ^ 2 ∂μ := by
    rw [lintegral_pos_iff_support hfm, hsupp, Measure.restrict_apply' hNVopen.measurableSet,
      ← Set.inter_assoc, Set.inter_self]
    exact hNVpos
  exact absurd hle hpos.ne'

end Positivity

end Ws23.V2D

end

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open NumberField.AdelicVolume
open scoped ENNReal

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ < 1) :
    ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 := by
  classical

  by_cases hu : u = 0
  · subst hu
    exact absurd hcov (AutomorphicForm.not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero F c d₁ d₂ T)
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : MeasurableMul (AdelicGL2 (𝓞 F) F) :=
    ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hD
  have hDm : MeasurableSet D := Ws23.V2D.measurableSet_iUnion_centreCutSiegelSet c u d₁ d₂ T

  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ‖φ g‖ₑ ^ 2 with hf
  have hfz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      f (centralScalar (𝓞 F) F z * g) = ‖((ω z : ℂˣ) : ℂ)‖ₑ ^ 2 * f g := by
    intro z g
    simp only [hf, hω, enorm_mul, mul_pow]

  have hfin : ∫⁻ g in D, f g ∂μ < ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞)) (f := φ)
      (μ := μ.restrict D) two_ne_zero ENNReal.ofNat_ne_top hL2.eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h2
    exact h2

  have hpos : ∫⁻ g in D, f g ∂μ ≠ 0 :=
    Ws23.V2D.setLIntegral_enorm_sq_ne_zero hu hd₁ hd₂
      (fun e he => AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow F c u d₁ d₂ e e T
        he le_rfl hcov)
      φ hφc hφ0 hγ ω hω

  by_contra hge
  push Not at hge
  set ρ : ℝ := ‖(a : w.Completion)‖ ^ 2 with hρ
  have ha0 : 0 < ‖(a : w.Completion)‖ := norm_pos_iff.mpr a.ne_zero
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, sq_lt_one_iff_abs_lt_one, abs_of_nonneg (norm_nonneg _)]
    exact ha

  set M : ℝ := d₂ * ∑ x ∈ T, archDetNorm w x with hM
  have hdetD : ∀ g ∈ D, 0 < archDetNorm w g ∧ archDetNorm w g ≤ M := by
    intro g hg
    refine ⟨archDetNorm_pos w g, ?_⟩
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hg
    have hsd := ((mem_centreCutSiegelSet_iff.mp hs).2.2.2 w).2
    have hxle : archDetNorm w x ≤ ∑ x' ∈ T, archDetNorm w x' :=
      Finset.single_le_sum (fun x' _ => (archDetNorm_pos w x').le) hx
    show archDetNorm w (s * x) ≤ M
    rw [Ws23.V2D.archDetNorm_mul, hM]
    exact mul_le_mul hsd hxle (archDetNorm_pos w x).le ((archDetNorm_pos w s).le.trans hsd)

  set A : ℕ → Set (AdelicGL2 (𝓞 F) F) := fun k =>
    D ∩ {g | archDetNorm w g ∈ Set.Ioc (ρ ^ (k + 1) * M) (ρ ^ k * M)} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hDm.inter (measurableSet_Ioc.preimage (continuous_archDetNorm w).measurable)
  have hcover : D ⊆ ⋃ k, A k := by
    intro g hg
    obtain ⟨hg0, hgM⟩ := hdetD g hg
    have hM0 : 0 < M := hg0.trans_le hgM
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (div_pos hg0 hM0)
      ((div_le_one hM0).mpr hgM) hρ0 hρ1
    refine Set.mem_iUnion.mpr ⟨k, hg, ?_, ?_⟩
    · rwa [← lt_div_iff₀ hM0]
    · rwa [← div_le_iff₀ hM0]

  have htile : ∃ k, ∫⁻ g in A k, f g ∂μ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hpos
    refine le_antisymm ?_ bot_le
    calc ∫⁻ g in D, f g ∂μ ≤ ∫⁻ g in ⋃ k, A k, f g ∂μ := lintegral_mono_set hcover
      _ ≤ ∑' k, ∫⁻ g in A k, f g ∂μ := lintegral_iUnion_le _ _
      _ = 0 := by simp [hall]
  obtain ⟨k, hk⟩ := htile

  set zz : ℕ → (AdeleRing (𝓞 F) F)ˣ := fun m => (archCentralUnit F w a) ^ m with hzz
  set B : ℕ → Set (AdelicGL2 (𝓞 F) F) := fun m =>
    (fun g => centralScalar (𝓞 F) F (zz m) * g) '' A k with hB
  have hBm : ∀ m, MeasurableSet (B m) := fun m =>
    Ws23.V2D.measurableSet_image_mul_left _ (hAm k)
  have hBsub : ∀ m, B m ⊆ D := by
    rintro m _ ⟨g, hg, rfl⟩
    exact Ws23.V2D.centralScalar_pow_mul_mem_iUnion hd₁ w a ha.le m hg.1
  have hBdet : ∀ m, ∀ g ∈ B m, archDetNorm w g ∈ Set.Ioc (ρ ^ (k + m + 1) * M) (ρ ^ (k + m) * M) := by
    rintro m _ ⟨g, hg, rfl⟩
    rw [Ws23.V2D.archDetNorm_centralScalar_pow_mul, ← hρ]
    obtain ⟨h1, h2⟩ := hg.2
    constructor
    · calc ρ ^ (k + m + 1) * M = ρ ^ m * (ρ ^ (k + 1) * M) := by ring
        _ < ρ ^ m * archDetNorm w g := by gcongr
    · calc ρ ^ m * archDetNorm w g ≤ ρ ^ m * (ρ ^ k * M) := by gcongr
        _ = ρ ^ (k + m) * M := by ring
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro m m' hmm'
    have hM0 : 0 ≤ M := by
      rw [hM]
      exact mul_nonneg hd₂.le (Finset.sum_nonneg fun x _ => (archDetNorm_pos w x).le)
    have key : ∀ {m m' : ℕ}, m < m' → Disjoint (B m) (B m') := by
      intro m m' h
      refine Set.disjoint_left.mpr fun g hg hg' => ?_
      have h1 := (hBdet m g hg).1
      have h2 := (hBdet m' g hg').2
      have hle : ρ ^ (k + m') * M ≤ ρ ^ (k + m + 1) * M :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)) hM0
      exact absurd (h2.trans hle) (not_le.mpr h1)
    rcases lt_or_gt_of_ne hmm' with h | h
    · exact key h
    · exact (key h).symm

  have hge' : ∀ m, (1 : ℝ≥0∞) ≤ ‖((ω (zz m) : ℂˣ) : ℂ)‖ₑ ^ 2 := by
    intro m
    have h1 : (1 : ℝ) ≤ ‖((ω (zz m) : ℂˣ) : ℂ)‖ := by
      rw [hzz, map_pow, Units.val_pow_eq_pow_val, norm_pow]
      exact one_le_pow₀ hge
    have h2 : (1 : ℝ≥0∞) ≤ ‖((ω (zz m) : ℂˣ) : ℂ)‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.one_le_ofReal.mpr h1
    calc (1 : ℝ≥0∞) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ ‖((ω (zz m) : ℂˣ) : ℂ)‖ₑ ^ 2 := by gcongr
  have hmass : ∀ m, ∫⁻ g in A k, f g ∂μ ≤ ∫⁻ g in B m, f g ∂μ := by
    intro m
    rw [hB, Ws23.V2D.setLIntegral_image_mul_left μ f (centralScalar (𝓞 F) F (zz m)) _
      (ENNReal.pow_ne_top enorm_ne_top) (hfz (zz m)) (hAm k)]
    exact le_mul_of_one_le_left zero_le (hge' m)
  have htop := Ws23.V2D.lintegral_eq_top_of_disjoint_of_le μ f B hBm hdisj D hBsub _ hk hmass
  exact absurd htop hfin.ne

end S_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre (solution)
