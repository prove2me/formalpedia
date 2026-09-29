-- Prove2me | solution 1 for AutomorphicForm.exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/26717fe7-bac5-5a5f-b361-220f3796722e

import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

namespace KcTwistBoundedTT3

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicVolume NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell NumberField.StandardAddChar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

section General

variable (K : Type) [Field K] [NumberField K]

theorem det_unipotentGL2 (x : AdeleRing (𝓞 K) K) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_val, Matrix.det_diagonal, Units.val_pow_eq_pow_val]
  simp

theorem ideleNorm_pow (x : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) : ideleNorm K (x ^ n) = ideleNorm K x ^ n := by
  simp only [ideleNorm, map_pow, NNReal.coe_pow]

theorem ideleNorm_det_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    {s : AdelicGL2 (𝓞 K) K} (hs : s ∈ centreCutSiegelSet K c u d₁ d₂) :
    d₁ ^ (∑ w : InfinitePlace K, w.mult) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ w : InfinitePlace K, w.mult) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K s hs.1, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum]
  have hw := hs.2.2.2
  refine ⟨Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _) fun w _ => ?_,
    Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w s).le _) fun w _ => ?_⟩
  · exact pow_le_pow_left₀ hd₁.le (hw w).1 _
  · exact pow_le_pow_left₀ (archDetNorm_pos w s).le (hw w).2 _

theorem exists_pinch_finset (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ T, m ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ≤ m⁻¹ := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | insert a T ha ih =>
    obtain ⟨m, hm0, hm1, hm⟩ := ih
    set N : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det a) with hN
    have hNpos : 0 < N := ideleNorm_pos _
    refine ⟨min m (min N N⁻¹), lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos)), (min_le_left _ _).trans hm1, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · refine ⟨(min_le_right _ _).trans (min_le_left _ _), ?_⟩
      rw [← hN]
      have h1 : min m (min N N⁻¹) ≤ N⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 0 < min m (min N N⁻¹) := lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))
      calc N = (N⁻¹)⁻¹ := (inv_inv N).symm
        _ ≤ (min m (min N N⁻¹))⁻¹ := inv_anti₀ h2 h1
    · obtain ⟨h1, h2⟩ := hm x hx
      refine ⟨(min_le_left _ _).trans h1, h2.trans ?_⟩
      exact inv_anti₀ (lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))) (min_le_left _ _)

theorem exists_pinch_window {c u d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ s ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂),
      L ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧ ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ U := by
  obtain ⟨m, hm0, _, hm⟩ := exists_pinch_finset K T
  have hd₂ : 0 < d₂ := hd₁.trans hd
  refine ⟨d₁ ^ (∑ w : InfinitePlace K, w.mult) * m, d₂ ^ (∑ w : InfinitePlace K, w.mult) * m⁻¹,
    mul_pos (pow_pos hd₁ _) hm0, mul_pos (pow_pos hd₂ _) (inv_pos.2 hm0), fun s hs => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hs
  obtain ⟨x, hx, s₁, hs₁, rfl⟩ := hs
  obtain ⟨h1, h2⟩ := ideleNorm_det_mem_of_mem_centreCutSiegelSet K hd₁ hd hs₁
  obtain ⟨h3, h4⟩ := hm x hx
  rw [map_mul, ideleNorm_mul]
  exact ⟨mul_le_mul h1 h3 hm0.le (ideleNorm_pos _).le,
    mul_le_mul h2 h4 (ideleNorm_pos _).le (pow_nonneg hd₂.le _)⟩

theorem exists_norm_le_mul_ideleNorm_det_rpow
    (D : Set (AdelicGL2 (𝓞 K) K)) (hcov : CoversModCentre K D)
    (L U : ℝ) (hL : 0 < L) (_hU : 0 < U)
    (hLU : ∀ s ∈ D, L ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧ ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ U)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (C : ℝ) (hC : ∀ s ∈ D, ‖φ s‖ ≤ C)
    (hleft : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K z * g) = ((χ z : ℂˣ) : ℂ) * φ g)
    (σ : ℝ) (hσ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = ideleNorm K z ^ σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      ‖φ g‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (σ / 2) := by
  have hC0 : 0 ≤ C := by
    obtain ⟨γ, z, h1⟩ := hcov 1
    exact (norm_nonneg _).trans (hC _ h1)
  set e : ℝ := -(σ / 2) with he
  refine ⟨C * max (L ^ e) (U ^ e), mul_nonneg hC0 (le_max_of_le_left (Real.rpow_nonneg hL.le _)), fun g => ?_⟩
  obtain ⟨γ, z, hs⟩ := hcov g
  set s : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z with hsdef
  set N : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g) with hN
  set q : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det s) with hq
  have hNpos : 0 < N := ideleNorm_pos _
  have hzpos : 0 < ideleNorm K z := ideleNorm_pos _
  have hφs : φ s = ((χ z : ℂˣ) : ℂ) * φ g := by
    rw [hsdef, mul_assoc, hleft, mul_centralScalar_comm, hcentral]
  have hqN : q = N * ideleNorm K z ^ 2 := by
    rw [hq, hsdef, map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints,
      one_mul, det_centralScalar, ideleNorm_pow]
  have hz2 : ideleNorm K z ^ (2 : ℕ) = q / N := by
    rw [hqN]; field_simp
  have h1 : ‖φ g‖ = ‖φ s‖ * (ideleNorm K z ^ σ)⁻¹ := by
    rw [hφs, norm_mul, hσ]
    have : ideleNorm K z ^ σ ≠ 0 := (Real.rpow_pos_of_pos hzpos σ).ne'
    field_simp
  have h2 : (ideleNorm K z ^ σ)⁻¹ = (q / N) ^ e := by
    rw [← hz2, he, ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le, ← Real.rpow_neg hzpos.le]
    congr 1
    push_cast
    ring
  have hqmem := hLU s hs
  have hqpos : 0 < q := hL.trans_le hqmem.1
  have h3 : (q / N) ^ e = q ^ e * N ^ (σ / 2) := by
    rw [Real.div_rpow hqpos.le hNpos.le, he, Real.rpow_neg hNpos.le, div_inv_eq_mul]
  have h4 : q ^ e ≤ max (L ^ e) (U ^ e) := by
    rcases le_total 0 e with he0 | he0
    · exact le_max_of_le_right (Real.rpow_le_rpow hqpos.le hqmem.2 he0)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hL hqmem.1 he0)
  rw [h1, h2, h3]
  calc ‖φ s‖ * (q ^ e * N ^ (σ / 2)) ≤ C * (max (L ^ e) (U ^ e) * N ^ (σ / 2)) :=
        mul_le_mul (hC s hs) (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hNpos.le _)) (by positivity) hC0
    _ = C * max (L ^ e) (U ^ e) * N ^ (σ / 2) := by ring

theorem norm_whittaker_integral_le (ν : Measure (AdeleRing (𝓞 K) K)) [IsProbabilityMeasure ν]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (M r : ℝ)
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, ‖φ g‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (a : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    ‖∫ x, φ (unipotentGL2 x * g) * ψ (-(a * x)) ∂ν‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r := by
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x : AdeleRing (𝓞 K) K => φ (unipotentGL2 x * g) * ψ (-(a * x)))
    (C := M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r)
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, hψ1, mul_one]
      have := hφ (unipotentGL2 x * g)
      rwa [map_mul, det_unipotentGL2, one_mul] at this)
  rwa [probReal_univ, mul_one] at h

end General

section Rat

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  unfold psiPadicFun
  set a : ℤ := (exists_pPow_approx x).choose
  set k : ℕ := (exists_pPow_approx x).choose_spec.choose
  have h : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k) =
      ((-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩ in
theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  rw [psiV_apply, psiPadic_apply, norm_psiPadicFun]

theorem norm_psiFin (t : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin t‖ = 1 := by
  rw [psiFin_apply, finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_psiV_finite t).toFinset)
    (by simp), norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiV v _

theorem norm_psiArchPlace (v : InfinitePlace ℚ) (x : v.Completion) : ‖psiArchPlace v x‖ = 1 := by
  rw [psiArchPlace_apply]
  have h : (2 * (Real.pi : ℂ) * Complex.I) *
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℂ) =
      ((2 * Real.pi * (InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℝ) : ℂ) *
        Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiArch (x : InfiniteAdeleRing ℚ) : ‖psiArch x‖ = 1 := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiArchPlace v _

theorem norm_psiQ (t : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ t‖ = 1 := by
  rw [psiQ_apply, norm_mul, norm_psiArch, norm_psiFin, one_mul]

theorem ratArchGL2_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  simp only [ratArchGL2, map_mul]

theorem ratArchGL2_of_mem {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  simp only [ratArchGL2, (mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one]

theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = m := by
  have h := archRealProjAt_archRealGLAt (F := ℚ) (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m
  refine Eq.trans ?_ h
  exact Units.ext (Matrix.ext fun i j => rfl)

theorem finFactor_mul_coe (Y : AdelicGL2 (𝓞 ℚ) ℚ) (X : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) = RSCarrier.finFactor Y * X := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ))))⁻¹ *
      (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 Y))⁻¹ * Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [ratArchGL2_mul, ratArchGL2_of_mem X.2, mul_one, mul_assoc]

theorem finFactor_archRealGLAt (m : GL (Fin 2) ℝ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m)))⁻¹ *
      archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m = 1
  rw [ratArchGL2_archRealGLAt, inv_mul_cancel]

theorem ratArchGL2_coe (x : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (x : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  ratArchGL2_of_mem x.2

theorem ratArchGL2_archRealGLAt_mul_coe (h₀ : GL (Fin 2) ℝ) (x : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ)) = h₀ := by
  rw [ratArchGL2_mul, ratArchGL2_coe, ratArchGL2_archRealGLAt, mul_one]

theorem finFactor_archRealGLAt_mul_coe (h₀ : GL (Fin 2) ℝ) (x : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ)) = x := by
  rw [finFactor_mul_coe, finFactor_archRealGLAt, one_mul]

theorem whittakerCoefficient_productionPinsGeneral_eq (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (a : ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ a =
      fun g => ∫ x, φ (unipotentGL2 x * g) * psiQ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x))
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)) := rfl

scoped instance isProbabilityMeasure_cond_adelicBox_rat :
    IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)) :=
  isProbabilityMeasure_cond_adelicBox ℚ

theorem norm_whittakerCoefficient_le (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (M r : ℝ)
    (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ r)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ 1 g‖ ≤
      M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ r := by
  rw [whittakerCoefficient_productionPinsGeneral_eq]
  exact norm_whittaker_integral_le ℚ _ φ M r hφ psiQ norm_psiQ _ g

set_option maxHeartbeats 1600000 in

theorem main
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (h6 : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) =
      ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g)
    (h9 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (RSCarrier.finFactor g)) :
    ∃ B₁ : ℝ, ∀ x : finiteAdelicGL2Subgroup ℚ,
      ‖Wf₁ x * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (-σ₀ / 2) : ℝ) : ℂ)‖ ≤ B₁ := by

  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

  obtain ⟨α, hα, hconv⟩ := h4b
  have hbdd : IsBoundedOnSiegelWindows ℚ φ₁ := by
    have h := AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
      ℚ (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξ φ₁ h4 h3 α hα
    rwa [hconv] at h
  obtain ⟨CD, hCD⟩ := hbdd (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num)

  have hLs : IsLsXiFunction (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).Z ξ φ₁ :=
    ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z ξ
      (productionPinsGeneral ℚ).D φ₁).1 h4.1).1

  obtain ⟨L, U, hL, hU, hLU⟩ := exists_pinch_window ℚ (c := (1 / 2 : ℝ)) (u := (1 : ℝ)) (classRepTranslates ℚ)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 2)
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_mul_ideleNorm_det_rpow ℚ _ hcov L U hL hU hLU φ₁ CD hCD
    hLs.left_invariant (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) h6 σ₀ hσ₀

  have hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ₁ 1 g‖ ≤
      M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (σ₀ / 2) :=
    norm_whittakerCoefficient_le φ₁ M (σ₀ / 2) hM

  obtain ⟨h₀, hh₀⟩ := hWA₀

  generalize hA₀ : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ = A₀
  have hNApos : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) := ideleNorm_pos _
  have hWApos : 0 < ‖WA₀ h₀‖ := norm_pos_iff.2 hh₀
  refine ⟨M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ (σ₀ / 2) / ‖WA₀ h₀‖, fun x => ?_⟩
  have hNxpos : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) := ideleNorm_pos _
  have hr : ratArchGL2 (A₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ)) = h₀ := by
    rw [← hA₀]
    exact ratArchGL2_archRealGLAt_mul_coe h₀ x
  have hf : RSCarrier.finFactor (A₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ)) = x := by
    rw [← hA₀]
    exact finFactor_archRealGLAt_mul_coe h₀ x
  have hkey : whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ₁ 1 (A₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ)) =
      WA₀ h₀ * Wf₁ x := by
    rw [h9, hr, hf]
  have h2 := hW (A₀ * (x : AdelicGL2 (𝓞 ℚ) ℚ))
  rw [hkey, norm_mul, map_mul, ideleNorm_mul, Real.mul_rpow hNApos.le hNxpos.le] at h2

  have h3' : ‖Wf₁ x‖ ≤ M * (ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ (σ₀ / 2) *
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (σ₀ / 2)) / ‖WA₀ h₀‖ :=
    (le_div_iff₀' hWApos).2 h2

  have hnorm : ‖Wf₁ x * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (-σ₀ / 2) : ℝ) : ℂ)‖ =
      ‖Wf₁ x‖ * (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (σ₀ / 2))⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hNxpos _), neg_div,
      Real.rpow_neg hNxpos.le]
  rw [hnorm, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hNxpos _)]
  calc ‖Wf₁ x‖ ≤ M * (ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ (σ₀ / 2) *
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (σ₀ / 2)) / ‖WA₀ h₀‖ := h3'
    _ = M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ (σ₀ / 2) / ‖WA₀ h₀‖ *
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (σ₀ / 2) := by ring

end Rat

end KcTwistBoundedTT3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat.KcTwistBoundedTT3"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat.KcTwistBoundedTT3"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁))
    (h6 : (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g))
    (h9 : (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (finFactor g))) :
    ∃ B₁ : ℝ, ∀ x : finiteAdelicGL2Subgroup ℚ,
      ‖Wf₁ x * ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (-σ₀ / 2) : ℝ) : ℂ)‖ ≤ B₁ :=
  KcTwistBoundedTT3.main ξ σ₀ hσ₀ φ₁ WA₀ Wf₁ hWA₀ h3 h4 h4b h6 h9

end S_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat (solution)
