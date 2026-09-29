-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1ebd2824-489c-5577-970d-db6e7081264a

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
import Theorems.Thm_AutomorphicForm_RankinSelberg_lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq
import Theorems.Thm_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery
import Theorems.Thm_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
import Theorems.Thm_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))

      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hctop : c ≠ ∞)
      (_hc : ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
            c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                  f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
                ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hD : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (e₁ e₂ : ℝ) (_he₁ : 0 < e₁) (_he : e₁ < e₂)
      (C : ℝ≥0∞) (_hC0 : C ≠ 0) (_hCtop : C ≠ ∞)
      (_hC : ∀ r : ℝ, 0 < r →
        (NumberField.Idele.idelicHaar K) (D ∩ {z | NumberField.TateGlobal.ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂}) = C)
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)
      (_hxsmall : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ))
      (_hxlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxc : Continuous x)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ) (_hyc : Continuous y)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)
      (_hysmall : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ))
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφcong : ∀ (s : ℂ) (k k' : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        k' ∈ finiteAdelicGL2Subgroup K → glFin (𝓞 K) K k' ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ s (k * k') = φ s k)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)

      (_hβ : (∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
          (∫ t, whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)) *
              ((NumberField.TateGlobal.ideleNorm K t ^ (-w) : ℝ) : ℂ)
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅)) ≠ 0),
    ∃ a : ℝ, a < 1 / 2 ∧
      (∀ s : ℂ, a < s.re →
        (∫⁻ t, ∫⁻ k,
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ₑ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) < ∞) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) x y (φ s) w e₁ e₂) {s : ℂ | a < s.re} ∧
      RankinSelberg.sPartIntegral K S (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) x y (φ (1 / 2)) w e₁ e₂ ≠ 0 := by

  intro α hα c hc0 hctop hc S D hD hDF e₁ e₂ he₁ he C hC0 hCtop hC D₀ ωx ωy w hωx hωy ν hων x₀ hx₀c nb hnb hx₀cong
    hxsmall hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxc hxG hxZ hxKS n hn hxlow
    y hyc hyG hyZ hyKS hycong hylow hysmall hylarge finf hfc φ hφ hφjc hφhol hφKS hφcong hφsupp hφval hβ
  set ψ : AddChar (AdeleRing (𝓞 K) K) ℂ := NumberField.StandardAddChar.stdAddChar K with hψdef
  have hψG : IsGlobalAddChar K ψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K

  have hg₀arch : glArch (𝓞 K) K (diagOne t₀ : AdelicGL2 (𝓞 K) K) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glArch_apply, diagOne_coe_apply, Units.val_one]
    fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, Matrix.one_apply, ht₀inf]) <;> rfl
  have hκarch : glArch (𝓞 K) K κ = 1 := by rw [hκ]; exact AdelicDock.glArch_finEmbed _ _ _
  have hg₀κarch : glArch (𝓞 K) K (diagOne t₀ * κ : AdelicGL2 (𝓞 K) K) = 1 := by rw [map_mul, hg₀arch, hκarch, mul_one]
  obtain ⟨δx, hδx, Cx, hCx⟩ := hxsmall (diagOne t₀ * κ) hg₀κarch
  obtain ⟨δy, hδy, Cy, hCy⟩ := hysmall (diagOne t₀) hg₀arch

  have hfin := AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery K hα S D₀ ωx ωy w hωx hωy ν hων x₀
    nb hnb hx₀cong hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxG hxZ hxKS n hn hxlow
    y hyG hyZ hyKS hycong hylow hylarge finf φ hφ hφjc hφKS hφsupp hφval δx Cx hδx hCx δy Cy hδy hCy
  obtain ⟨κ₀, hκ₀, hEval⟩ :=
    AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery K hα S D₀ ωx ωy w hωx hωy
      ν hων x₀ hx₀c nb hnb hx₀cong hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxc hxG
      hxZ hxKS n hn hxlow y hyc hyG hyZ hyKS hycong hylow hylarge finf hfc φ hφ hφjc hφKS hφsupp hφval δx Cx hδx hCx δy Cy hδy hCy

  have hBf : ∃ Bf : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) → ‖finf k‖ ≤ Bf := by
    obtain ⟨Bf, hBf⟩ := (isCompact_maximalCompactAt K ∅).exists_bound_of_continuousOn (hfc.continuousOn)
    refine ⟨Bf, fun k hkf hki => hBf k ?_⟩
    rw [SetLike.mem_coe, mem_maximalCompactAt_iff, mem_adelicMaximalCompact_iff]
    refine ⟨⟨by rw [hkf]; exact one_mem _, hki⟩, fun v _ => by rw [hkf, map_one]⟩
  obtain ⟨Bf, hBf⟩ := hBf
  have hHolo := AutomorphicForm.RankinSelberg.analyticOnNhd_integral_archTorus_pair K D₀ w x₀ y finf hx₀c hyc hfc Bf hBf t₀ ht₀inf
    κ hκarch δx Cx hδx hCx δy Cy hδy hCy (hxlarge (diagOne t₀ * κ) hg₀κarch) (hylarge (diagOne t₀) hg₀arch)

  have hU1 : IsUnitaryChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun z => by simp
  have hνu : IsUnitaryChar (𝓞 K) K ν := by
    intro z
    have h0 := NumberField.TateGlobal.ideleNorm_pos (F := K) z
    have h := congrArg (fun u : ℂ => ‖u‖) (hων z)
    simp only [norm_mul, RCLike.norm_conj, hωx z, hωy z, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _)] at h
    rw [two_mul, Real.rpow_add h0] at h
    have hpos : 0 < NumberField.TateGlobal.ideleNorm K z ^ w * NumberField.TateGlobal.ideleNorm K z ^ w :=
      mul_pos (Real.rpow_pos_of_pos h0 _) (Real.rpow_pos_of_pos h0 _)
    exact mul_left_cancel₀ hpos.ne' (h.trans (mul_one _).symm)
  have hZ' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) *
      (((1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ) := fun z => by
    rw [MonoidHom.one_apply, Units.val_one, mul_one]; exact hων z
  have hφc : ∀ s, Continuous (φ s) := fun s => hφjc.comp (Continuous.prodMk continuous_const continuous_id)
  have hSPART := fun s : ℂ =>
    AutomorphicForm.RankinSelberg.lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq K hα c hc S D hD hDF
      e₁ e₂ he₁ he C hC D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ψ hψG 1 ν ωx ωy
      w hU1 hνu hZ' x y hxG hyG hxc hyc hxZ hyZ s (φ s) (hφ s) (hφc s)

  have hsPart : ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      RankinSelberg.sPartIntegral K S (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ψ x y (φ s) w e₁ e₂ =
      (c.toReal : ℂ) * (C.toReal : ℂ) * ((κ₀ : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) *
            ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅)) := by
    intro s hs
    rw [(hSPART s).2 (hfin s hs), hEval s hs]
  refine ⟨1 / 2 - (δx + δy) / 2, by linarith, hfin, ?_, ?_⟩
  ·
    have hopen : IsOpen {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have ht0pos : 0 < NumberField.TateGlobal.ideleNorm K t₀ := NumberField.TateGlobal.ideleNorm_pos (F := K) t₀
    have hcpow : AnalyticOnNhd ℂ (fun s : ℂ => ((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2))
        {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} :=
      (analyticOnNhd_const.cpow (analyticOnNhd_id.add analyticOnNhd_const)
        (fun z _ => Complex.ofReal_mem_slitPlane.mpr ht0pos))
    have hprod : AnalyticOnNhd ℂ (fun s : ℂ => (c.toReal : ℂ) * (C.toReal : ℂ) * ((κ₀ : ℂ) *
        (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅)))
        {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} :=
      analyticOnNhd_const.mul ((analyticOnNhd_const.mul (hcpow.mul analyticOnNhd_const)).mul hHolo)
    exact hprod.congr hopen fun s hs => (hsPart s hs).symm
  ·
    have hhalf : (1 / 2 - (δx + δy) / 2 : ℝ) < (1 / 2 : ℂ).re := by norm_num; linarith
    rw [hsPart (1 / 2) hhalf]
    have ht0pos : 0 < NumberField.TateGlobal.ideleNorm K t₀ := NumberField.TateGlobal.ideleNorm_pos (F := K) t₀
    have hI : ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅) =
        ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
          (∫ t, whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)) *
              ((NumberField.TateGlobal.ideleNorm K t ^ (-w) : ℝ) : ℂ)
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only []
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      have ha := NumberField.TateGlobal.ideleNorm_pos (F := K) a
      have h1 : ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + 1 / 2) = ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) := by
        norm_num
      have h2 : ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K a ^ (-w) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        have h3 := Real.rpow_add ha 1 (-w - 1)
        rw [Real.rpow_one] at h3
        rw [← h3]
        congr 1
        ring
      simp only []
      rw [h1, h2]
      ring
    rw [hI]
    have hc' : (c.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hc0 hctop).ne'
    have hC' : (C.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hC0 hCtop).ne'
    have hκ' : (κ₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ₀.ne'
    have hN1 : ((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + 1 / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ht0pos.ne'))
    have hN2 : ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht0pos _).ne'
    exact mul_ne_zero (mul_ne_zero hc' hC') (mul_ne_zero (mul_ne_zero hκ' (mul_ne_zero hN1 hN2)) hβ)

end S_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery (solution)
