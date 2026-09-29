-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.analyticOnNhd_integral_archTorus_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5733739a-f8fc-5922-ac94-72c91045a049

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
import Theorems.Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace PairHoloKit

variable (K : Type) [Field K] [NumberField K]

theorem continuous_diagOne :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => (diagOne t : AdelicGL2 (𝓞 K) K) := by
  have hmat : ∀ s : (AdeleRing (𝓞 K) K)ˣ → AdeleRing (𝓞 K) K, Continuous s →
      Continuous fun t => (Matrix.diagonal ![s t, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hs, continuous_const]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hmat _ Units.continuous_val
  · exact hmat _ Units.continuous_coe_inv

theorem glFin_ext {a b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (h : ∀ v, finComponent (𝓞 K) K v a = finComponent (𝓞 K) K v b) : a = b := by
  apply Units.ext
  ext i j v : 2
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.adicCompletion K) =>
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) (h v)) i) j
  beta_reduce at this
  rwa [finComponent_apply, finComponent_apply] at this

theorem glFin_eq_one_of_mem {m : AdelicGL2 (𝓞 K) K} (hmK : m ∈ maximalCompactAt K ∅) :
    glFin (𝓞 K) K m = 1 :=
  glFin_ext K fun v => by rw [map_one]; exact (mem_maximalCompactAt_iff.1 hmK).2 v (Finset.notMem_empty v)

theorem isRowIsometry_of_mem {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ maximalCompactAt K ∅)
    (w : InfinitePlace K) : IsRowIsometry (archComponent K w (glArch (𝓞 K) K g)) :=
  (mem_adelicMaximalCompact_iff.1 (mem_maximalCompactAt_iff.1 hg).1).2 w

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem norm_fst_pos (a : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
  have h := congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.mul_inv
  change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
  exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)

theorem rpow_le_add {N t c₁ c₂ : ℝ} (hN : 0 < N) (h₁ : c₁ ≤ t) (h₂ : t ≤ c₂) :
    N ^ t ≤ N ^ c₁ + N ^ c₂ := by
  rcases le_total 1 N with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg hN.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hN h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg hN.le _))

theorem pair_small (w c : ℝ) {X Y : ℂ} {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    {Cx Cy δx δy : ℝ}
    (hX : ‖X‖ ≤ Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
      (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
    (hY : ‖Y‖ ≤ Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
      (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)) :
    ‖(((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * (X * (starRingEnd ℂ) Y)‖ ≤
      (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ c *
        ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by
  set r : InfinitePlace K → ℝ := fun pl => ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ with hr
  have hr0 : ∀ pl, 0 < r pl := fun pl => norm_fst_pos K a pl
  set N : ℝ := NumberField.TateGlobal.ideleNorm K a with hN
  have hN0 : 0 < N := NumberField.TateGlobal.ideleNorm_pos a
  have hNprod : N = ∏ pl, r pl ^ pl.mult := by
    rw [hN, NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha]
  have hm0 : ∀ pl, 0 < min 1 (r pl) := fun pl => lt_min one_pos (hr0 pl)
  set Px : ℝ := ∏ pl, (r pl ^ ((pl.mult : ℝ) * w / 2) * (min 1 (r pl)) ^ δx) with hPx
  set Py : ℝ := ∏ pl, (r pl ^ ((pl.mult : ℝ) * w / 2) * (min 1 (r pl)) ^ δy) with hPy
  have hCxP : 0 ≤ Cx * Px := (norm_nonneg X).trans hX
  have hw : ‖(((N ^ (c - w) : ℝ)) : ℂ)‖ = N ^ (c - w) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
  have hkey : N ^ (c - w) * (Px * Py) = N ^ c * ∏ pl, (min 1 (r pl)) ^ (δx + δy) := by
    have h1 : Px * Py = (∏ pl, r pl ^ ((pl.mult : ℝ) * w)) * ∏ pl, (min 1 (r pl)) ^ (δx + δy) := by
      rw [hPx, hPy, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun pl _ => ?_
      rw [Real.rpow_add (hm0 pl), show (pl.mult : ℝ) * w = (pl.mult : ℝ) * w / 2 + (pl.mult : ℝ) * w / 2 by ring,
        Real.rpow_add (hr0 pl)]
      ring
    have h2 : (∏ pl, r pl ^ ((pl.mult : ℝ) * w)) = N ^ w := by
      rw [hNprod, ← Real.finsetProd_rpow _ _ (fun pl _ => pow_nonneg (hr0 pl).le _)]
      exact Finset.prod_congr rfl fun pl _ => Real.rpow_natCast_mul (hr0 pl).le _ _
    rw [h1, h2, ← mul_assoc, ← Real.rpow_add hN0, sub_add_cancel]
  calc ‖(((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * (X * (starRingEnd ℂ) Y)‖
      = N ^ (c - w) * (‖X‖ * ‖Y‖) := by rw [norm_mul, norm_mul, RCLike.norm_conj, hw]
    _ ≤ N ^ (c - w) * ((Cx * Px) * (Cy * Py)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hX hY (norm_nonneg Y) hCxP) (Real.rpow_nonneg hN0.le _)
    _ = (Cx * Cy) * (N ^ (c - w) * (Px * Py)) := by ring
    _ = (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ c *
        ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by rw [hkey, ← mul_assoc]

theorem pair_large (w c : ℝ) {X Y : ℂ} {a : (AdeleRing (𝓞 K) K)ˣ} (pl : InfinitePlace K)
    {Cx Cy : ℝ} {M : ℕ}
    (hX : ‖X‖ ≤ Cx * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))
    (hY : ‖Y‖ ≤ Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-((0 : ℕ) : ℝ))) :
    ‖(((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * (X * (starRingEnd ℂ) Y)‖ ≤
      (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ c * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
  set N : ℝ := NumberField.TateGlobal.ideleNorm K a with hN
  have hN0 : 0 < N := NumberField.TateGlobal.ideleNorm_pos a
  set rp : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ with hrp
  rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hY
  have hCx0 : 0 ≤ Cx * N ^ (w / 2) * rp ^ (-(M : ℝ)) := (norm_nonneg X).trans hX
  have hw' : ‖(((N ^ (c - w) : ℝ)) : ℂ)‖ = N ^ (c - w) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
  have hkey : N ^ (c - w) * (N ^ (w / 2) * N ^ (w / 2)) = N ^ c := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1; ring
  calc ‖(((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * (X * (starRingEnd ℂ) Y)‖
      = N ^ (c - w) * (‖X‖ * ‖Y‖) := by rw [norm_mul, norm_mul, RCLike.norm_conj, hw']
    _ ≤ N ^ (c - w) * ((Cx * N ^ (w / 2) * rp ^ (-(M : ℝ))) * (Cy * N ^ (w / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hX hY (norm_nonneg Y) hCx0) (Real.rpow_nonneg hN0.le _)
    _ = (Cx * Cy) * (N ^ (c - w) * (N ^ (w / 2) * N ^ (w / 2))) * rp ^ (-(M : ℝ)) := by ring
    _ = (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ c * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
        rw [hkey]

end PairHoloKit

end

local notation3 "Wc[" K ";" D₀ "]" => whittakerCoefficient K (productionPinsOf K D₀
  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
  (NumberField.StandardAddChar.stdAddChar K)

open PairHoloKit in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K)) (w : ℝ)
    (x₀ y finf : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀) (_hyc : Continuous y) (_hfc : Continuous finf)
    (Bf : ℝ) (_hBf : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) → ‖finf k‖ ≤ Bf)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1) (κ : AdelicGL2 (𝓞 K) K) (_hκ : glArch (𝓞 K) K κ = 1)
    (δx Cx : ℝ) (_hδx : 0 < δx)
    (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
        (diagOne a * k * (diagOne t₀ * κ))‖ ≤
          Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
    (δy Cy : ℝ) (_hδy : 0 < δy)
    (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
        (diagOne a * k * (diagOne t₀))‖ ≤
          Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy))
    (_hxlarge : ∀ M : ℕ, ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
          Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))
    (_hylarge : ∀ M : ℕ, ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
          Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅))
      {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} := by
  classical
  set δ : ℝ := δx + δy with hδdef
  set U : Set ℂ := {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hψc : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
  have hWcont : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → Continuous fun g => Wc[K;D₀] φ 1 g :=
    fun φ hφ => AutomorphicForm.continuous_whittakerCoefficient K D₀ _ _ _ hψc φ hφ 1
  haveI : Nonempty ↥(maximalCompactAt K ∅) := ⟨1⟩
  haveI := secondCountableTopology_idele K
  choose CxL hCxL using _hxlarge
  obtain ⟨Cy0, hCy0⟩ := _hylarge 0

  obtain ⟨core, hcore⟩ : ∃ core : (AdeleRing (𝓞 K) K)ˣ → ↥(maximalCompactAt K ∅) → ℂ, ∀ a k, core a k =
      Wc[K;D₀] x₀ 1 (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (Wc[K;D₀] y 1 (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)) := ⟨_, fun _ _ => rfl⟩
  have hcorec : Continuous (Function.uncurry core) := by
    have hfun : Function.uncurry core = fun p : (AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅) =>
        Wc[K;D₀] x₀ 1 (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
          (starRingEnd ℂ) (Wc[K;D₀] y 1 (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K) * diagOne t₀)) := by
      funext p; exact hcore _ _
    rw [hfun]
    have h1 : Continuous fun p : (AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅) =>
        diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ) :=
      (((continuous_diagOne K).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const
    have h2 : Continuous fun p : (AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅) =>
        diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K) * diagOne t₀ :=
      (((continuous_diagOne K).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const
    exact ((hWcont x₀ _hx₀c).comp h1).mul (Complex.continuous_conj.comp ((hWcont y _hyc).comp h2))

  have hwc : ∀ c : ℝ, Continuous fun a : (AdeleRing (𝓞 K) K)ˣ =>
      (((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) := fun c =>
    Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).rpow_const
      fun t => Or.inl (NumberField.TateGlobal.ideleNorm_pos t).ne')
  have hHc : ∀ c : ℝ, Continuous (Function.uncurry fun (a : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(maximalCompactAt K ∅)) =>
      (((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * core a k) := fun c =>
    ((hwc c).comp continuous_fst).mul hcorec
  set Hvec : ℝ → (AdeleRing (𝓞 K) K)ˣ → C(↥(maximalCompactAt K ∅), ℂ) := fun c a =>
    (⟨Function.uncurry fun (a : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(maximalCompactAt K ∅)) =>
      (((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * core a k, hHc c⟩ :
        C((AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅), ℂ)).curry a with hHvec
  have hHvec_apply : ∀ c a k, Hvec c a k = (((NumberField.TateGlobal.ideleNorm K a ^ (c - w) : ℝ)) : ℂ) * core a k :=
    fun c a k => rfl
  have hHvec_cont : ∀ c, Continuous (Hvec c) := fun c => ContinuousMap.continuous _

  have hHint : ∀ c : ℝ, 0 < δ + c → 0 < δ + 2 * c → Integrable (Hvec c) (NumberField.Idele.sPartMeasure K ∅) := by
    intro c hc1 hc2
    refine NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
      K (Hvec c) (hHvec_cont c).aestronglyMeasurable δ c (Cx * Cy) hc1 hc2 ?_ ?_
    · intro a ha
      refine (ContinuousMap.norm_le_of_nonempty _).2 fun k => ?_
      rw [hHvec_apply, hcore]
      exact pair_small K w c ha (_hCx k (glFin_eq_one_of_mem K k.2) (isRowIsometry_of_mem K k.2) a ha)
        (_hCy k (glFin_eq_one_of_mem K k.2) (isRowIsometry_of_mem K k.2) a ha)
    · intro M
      refine ⟨CxL M * Cy0, fun a ha pl => (ContinuousMap.norm_le_of_nonempty _).2 fun k => ?_⟩
      rw [hHvec_apply, hcore]
      exact pair_large K w c pl (hCxL M k (glFin_eq_one_of_mem K k.2) (isRowIsometry_of_mem K k.2) a ha pl)
        (hCy0 k (glFin_eq_one_of_mem K k.2) (isRowIsometry_of_mem K k.2) a ha pl)

  obtain ⟨F, hF⟩ : ∃ F : ℂ → ↥(maximalCompactAt K ∅) → (AdeleRing (𝓞 K) K)ˣ → ℂ, ∀ s k a, F s k a =
      ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
        ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) * core a k := ⟨_, fun _ _ _ => rfl⟩
  have hFnorm : ∀ s k a, ‖F s k a‖ =
      NumberField.TateGlobal.ideleNorm K a ^ ((s.re - 1 / 2) - w) * ‖core a k‖ := by
    intro s k a
    have hN0 := NumberField.TateGlobal.ideleNorm_pos a
    rw [hF, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hN0 _), ← Real.rpow_add hN0]
    congr 2
    have hre : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
    rw [hre]; ring
  have hHnorm : ∀ c a k, ‖Hvec c a k‖ = NumberField.TateGlobal.ideleNorm K a ^ (c - w) * ‖core a k‖ := by
    intro c a k
    rw [hHvec_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos a) _)]

  have hFdom : ∀ (c₁ c₂ : ℝ) (s : ℂ), c₁ ≤ s.re - 1 / 2 → s.re - 1 / 2 ≤ c₂ → ∀ k a,
      ‖F s k a‖ ≤ ‖Hvec c₁ a‖ + ‖Hvec c₂ a‖ := by
    intro c₁ c₂ s h1 h2 k a
    have hN0 := NumberField.TateGlobal.ideleNorm_pos a
    rw [hFnorm]
    calc NumberField.TateGlobal.ideleNorm K a ^ ((s.re - 1 / 2) - w) * ‖core a k‖
        ≤ (NumberField.TateGlobal.ideleNorm K a ^ (c₁ - w) + NumberField.TateGlobal.ideleNorm K a ^ (c₂ - w)) *
            ‖core a k‖ :=
          mul_le_mul_of_nonneg_right (rpow_le_add hN0 (by linarith) (by linarith)) (norm_nonneg _)
      _ = ‖Hvec c₁ a k‖ + ‖Hvec c₂ a k‖ := by rw [hHnorm, hHnorm]; ring
      _ ≤ ‖Hvec c₁ a‖ + ‖Hvec c₂ a‖ := add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)

  have hFcont : ∀ s k, Continuous (F s k) := by
    intro s k
    have hfun : F s k = fun a => ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
        ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) * core a k := funext fun a => hF s k a
    rw [hfun]
    refine ((Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K))
      continuous_const fun a => Or.inl ?_).mul (Complex.continuous_ofReal.comp
        ((NumberField.TateGlobal.continuous_ideleNorm K).rpow_const fun t =>
          Or.inl (NumberField.TateGlobal.ideleNorm_pos t).ne'))).mul (hcorec.comp (Continuous.prodMk_left k))
    exact_mod_cast NumberField.TateGlobal.ideleNorm_pos a
  have hstrip : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ 0 < δ + (z₀.re - ε - 1 / 2) ∧ 0 < δ + 2 * (z₀.re - ε - 1 / 2) ∧
      ∀ z ∈ Metric.ball z₀ ε, z₀.re - ε - 1 / 2 ≤ z.re - 1 / 2 ∧ z.re - 1 / 2 ≤ z₀.re + ε - 1 / 2 := by
    intro z₀ hz₀
    have hz₀' : 1 / 2 - (δx + δy) / 2 < z₀.re := hz₀
    refine ⟨(z₀.re - (1 / 2 - (δx + δy) / 2)) / 2, by linarith, ?_, ?_, ?_⟩
    · rw [hδdef]; linarith
    · rw [hδdef]; linarith
    · intro z hz
      have habs : |z.re - z₀.re| < (z₀.re - (1 / 2 - (δx + δy) / 2)) / 2 := by
        have h := Metric.mem_ball.1 hz
        rw [Complex.dist_eq] at h
        exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z₀)) h
      rw [abs_lt] at habs
      constructor <;> linarith [habs.1, habs.2]

  have hinner : ∀ k : ↥(maximalCompactAt K ∅),
      DifferentiableOn ℂ (fun s => ∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅)) U := by
    intro k
    refine MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
      (NumberField.Idele.sPartMeasure K ∅) hUo (fun s a => F s k a) (fun s _ => (hFcont s k).aestronglyMeasurable)
      (fun a => ?_) (fun z₀ hz₀ => ?_)
    · have hfun : (fun z => F z k a) = fun z => ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (z + 1 / 2) *
          (((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) * core a k) := by
        funext z; rw [hF, mul_assoc]
      rw [hfun]
      refine DifferentiableOn.mul_const (fun z _ => (DifferentiableAt.const_cpow (differentiableAt_id.add_const _)
        (Or.inl ?_)).differentiableWithinAt) _
      exact_mod_cast (NumberField.TateGlobal.ideleNorm_pos a).ne'
    · obtain ⟨ε, hε, hc1, hc2, hball⟩ := hstrip z₀ hz₀
      refine ⟨ε, hε, fun a => ‖Hvec (z₀.re - ε - 1 / 2) a‖ + ‖Hvec (z₀.re + ε - 1 / 2) a‖,
        (hHint _ hc1 hc2).norm.add (hHint _ (by linarith) (by linarith)).norm, fun z hz a => ?_⟩
      exact hFdom _ _ z (hball z hz).1 (hball z hz).2 k a

  have hinner_cont : ∀ s ∈ U, Continuous fun k : ↥(maximalCompactAt K ∅) =>
      ∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅) := by
    intro s hs
    obtain ⟨ε, hε, hc1, hc2, hball⟩ := hstrip s hs
    have hFc2 : Continuous (Function.uncurry fun (a : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(maximalCompactAt K ∅)) => F s k a) := by
      have hfun : (Function.uncurry fun (a : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(maximalCompactAt K ∅)) => F s k a) =
          fun p : (AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅) =>
            ((NumberField.TateGlobal.ideleNorm K p.1 : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K p.1 ^ (-w - 1) : ℝ) : ℂ) * core p.1 p.2 := by
        funext p; exact hF _ _ _
      rw [hfun]
      refine ((Continuous.cpow (Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).comp
        continuous_fst)) continuous_const fun p => Or.inl ?_).mul (Complex.continuous_ofReal.comp
          (((NumberField.TateGlobal.continuous_ideleNorm K).comp continuous_fst).rpow_const fun p =>
            Or.inl (NumberField.TateGlobal.ideleNorm_pos p.1).ne'))).mul hcorec
      exact_mod_cast NumberField.TateGlobal.ideleNorm_pos p.1
    set Fvec : (AdeleRing (𝓞 K) K)ˣ → C(↥(maximalCompactAt K ∅), ℂ) := fun a =>
      (⟨Function.uncurry fun (a : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(maximalCompactAt K ∅)) => F s k a, hFc2⟩ :
        C((AdeleRing (𝓞 K) K)ˣ × ↥(maximalCompactAt K ∅), ℂ)).curry a with hFvec
    have hFvec_apply : ∀ a k, Fvec a k = F s k a := fun a k => rfl
    have hFvec_int : Integrable Fvec (NumberField.Idele.sPartMeasure K ∅) := by
      refine Integrable.mono' ((hHint _ hc1 hc2).norm.add (hHint _ (by linarith) (by linarith)).norm)
        (ContinuousMap.continuous _).aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
      refine (ContinuousMap.norm_le_of_nonempty _).2 fun k => ?_
      rw [hFvec_apply]
      exact hFdom _ _ s (by linarith [(hball s (Metric.mem_ball_self hε)).1]) (by linarith [(hball s (Metric.mem_ball_self hε)).2]) k a
    set I : C(↥(maximalCompactAt K ∅), ℂ) := ∫ a, Fvec a ∂(NumberField.Idele.sPartMeasure K ∅) with hI
    have hIk : ∀ k, I k = ∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅) := by
      intro k
      show (ContinuousMap.evalCLM ℂ k) I = _
      rw [hI, ← (ContinuousMap.evalCLM ℂ k).integral_comp_comm hFvec_int]
      rfl
    have : (fun k : ↥(maximalCompactAt K ∅) => ∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅)) = fun k => I k :=
      funext fun k => (hIk k).symm
    rw [this]
    exact I.continuous

  have houter : DifferentiableOn ℂ (fun s => ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
      (∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅)) ∂(maximalCompactAtHaar K ∅)) U := by
    refine MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
      (maximalCompactAtHaar K ∅) hUo (fun s k => finf (k : AdelicGL2 (𝓞 K) K) *
        ∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅)) (fun s hs => ?_) (fun k => ?_) (fun z₀ hz₀ => ?_)
    · exact ((_hfc.comp continuous_subtype_val).mul (hinner_cont s hs)).aestronglyMeasurable
    · exact (hinner k).const_mul _
    · obtain ⟨ε, hε, hc1, hc2, hball⟩ := hstrip z₀ hz₀
      set J : ℝ := ∫ a, (‖Hvec (z₀.re - ε - 1 / 2) a‖ + ‖Hvec (z₀.re + ε - 1 / 2) a‖)
        ∂(NumberField.Idele.sPartMeasure K ∅) with hJ
      refine ⟨ε, hε, fun _ => |Bf| * J, integrable_const _, fun z hz k => ?_⟩
      have hbd : ‖∫ a, F z k a ∂(NumberField.Idele.sPartMeasure K ∅)‖ ≤ J := by
        refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => norm_nonneg _)
          ((hHint _ hc1 hc2).norm.add (hHint _ (by linarith) (by linarith)).norm)
          (Filter.Eventually.of_forall fun a => hFdom _ _ z (hball z hz).1 (hball z hz).2 k a))
      rw [norm_mul]
      exact mul_le_mul ((_hBf k (glFin_eq_one_of_mem K k.2) (isRowIsometry_of_mem K k.2)).trans (le_abs_self _))
        hbd (norm_nonneg _) (abs_nonneg _)

  have hfun : (fun s : ℂ => ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
      (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
        ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
        (Wc[K;D₀] x₀ 1 (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
          (starRingEnd ℂ) (Wc[K;D₀] y 1 (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
        ∂(NumberField.Idele.sPartMeasure K ∅)) ∂(maximalCompactAtHaar K ∅)) =
      fun s => ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
        (∫ a, F s k a ∂(NumberField.Idele.sPartMeasure K ∅)) ∂(maximalCompactAtHaar K ∅) := by
    funext s
    simp only [hF, hcore]
  rw [hfun]
  exact houter.analyticOnNhd hUo

end S_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair (solution)
