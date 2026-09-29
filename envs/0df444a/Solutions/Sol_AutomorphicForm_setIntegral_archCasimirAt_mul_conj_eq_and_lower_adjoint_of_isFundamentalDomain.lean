-- Prove2me | solution 1 for AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b5fd6930-5191-5bc3-9045-101234a4d97d

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace UnitSymAlg25

variable {K : Type} [Field K] [NumberField K]

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

private theorem norm_mul_conj_le {a b : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) : ‖a * conj b‖ ≤ B * B := by
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg a).trans ha)

theorem integrable_mul_conj {a b : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K a b) (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤)
    {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u) (hv : Continuous v) {B : ℝ}
    (hbu : ∀ g ∈ slab K a b, ‖u g‖ ≤ B) (hbv : ∀ g ∈ slab K a b, ‖v g‖ ≤ B) :
    Integrable (fun g => u g * conj (v g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) :=
  Measure.integrableOn_of_bounded (M := B * B) hfin.ne (hu.mul (Complex.continuous_conj.comp hv)).aestronglyMeasurable
    ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg =>
      norm_mul_conj_le (hbu g (h𝓕s hg)) (hbv g (h𝓕s hg))))

theorem integral_lincomb {α : Type*} [MeasurableSpace α] (ν : Measure α) {f₁ f₂ f₃ : α → ℂ}
    (h₁ : Integrable f₁ ν) (h₂ : Integrable f₂ ν) (h₃ : Integrable f₃ ν) (a b c : ℂ) :
    ∫ g, (a * f₁ g + b * f₂ g + c * f₃ g) ∂ν = a * ∫ g, f₁ g ∂ν + b * ∫ g, f₂ g ∂ν + c * ∫ g, f₃ g ∂ν := by
  have h₁' : Integrable (fun g => a * f₁ g) ν := h₁.const_mul a
  have h₂' : Integrable (fun g => b * f₂ g) ν := h₂.const_mul b
  have h₃' : Integrable (fun g => c * f₃ g) ν := h₃.const_mul c
  have h12 : Integrable (fun g => a * f₁ g + b * f₂ g) ν := h₁'.add h₂'
  rw [integral_add h12 h₃', integral_add h₁' h₂', integral_const_mul, integral_const_mul, integral_const_mul]

theorem archDerivAt_globalPoints_mul {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x g := by
  intro γ g
  have h := archDerivAt_comp_mul_left hw d x (globalPoints (𝓞 K) K γ)
  have hfun : (fun g => x (globalPoints (𝓞 K) K γ * g)) = x := funext (hx γ)
  rw [hfun] at h
  exact (congrFun h g).symm

theorem main
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x)) (hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d x'))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B ∧ ‖archDerivAt hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B ∧ ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B)) :
    (∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, (archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)) g * conj (x' g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj ((archDerivAt hw .H x' + Complex.I • (archDerivAt hw .E x' + archDerivAt hw .Fm x')) g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, (archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)) g * conj (x' g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj ((archDerivAt hw .H x' - Complex.I • (archDerivAt hw .E x' + archDerivAt hw .Fm x')) g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by

  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  have bx : ∀ g ∈ slab K e₁ e₂, ‖x g‖ ≤ B := fun g hg => (hB g hg).1
  have bx' : ∀ g ∈ slab K e₁ e₂, ‖x' g‖ ≤ B := fun g hg => (hB g hg).2.1
  have bD : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d x g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).1
  have bD' : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d x' g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).2
  have bDD : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').1
  have bDD' : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').2

  have iD : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x g :=
    fun d => archDerivAt_globalPoints_mul hw d hx
  have iD' : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x' (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x' g :=
    fun d => archDerivAt_globalPoints_mul hw d hx'

  have skew : ∀ (d : ArchDir) (u v : AdelicGL2 (𝓞 K) K → ℂ)
      (hu : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
      (hv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
      (huc : Continuous u) (hvc : Continuous v) (hus : IsArchSmoothAt hw u) (hvs : IsArchSmoothAt hw v)
      (hDu : Continuous (archDerivAt hw d u)) (hDv : Continuous (archDerivAt hw d v))
      (bu : ∀ g ∈ slab K e₁ e₂, ‖u g‖ ≤ B) (bv : ∀ g ∈ slab K e₁ e₂, ‖v g‖ ≤ B)
      (bDu : ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d u g‖ ≤ B) (bDv : ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d v g‖ ≤ B),
      ∫ g in 𝓕, archDerivAt hw d u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = -∫ g in 𝓕, u g * conj (archDerivAt hw d v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro d u v hu hv huc hvc hus hvs hDu hDv bu bv bDu bDv
    have h := AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain K w hw d e₁ e₂
      he₁ he 𝓕 h𝓕m h𝓕s h𝓕 u v hu hv huc hvc hus hvs hDu hDv B
      (fun g hg => ⟨bu g hg, bv g hg, bDu g hg, bDv g hg⟩)
    rw [integral_add (integrable_mul_conj h𝓕m h𝓕s hfin hDu hvc bDu bv)
      (integrable_mul_conj h𝓕m h𝓕s hfin huc hDv bu bDv)] at h
    exact eq_neg_of_add_eq_zero_left h

  have S3 := skew .H x x' hx hx' hxc hx'c hxs hx's (hD1 .H) (hD1' .H) bx bx' (bD .H) (bD' .H)
  have S6 := skew .E x x' hx hx' hxc hx'c hxs hx's (hD1 .E) (hD1' .E) bx bx' (bD .E) (bD' .E)
  have S7 := skew .Fm x x' hx hx' hxc hx'c hxs hx's (hD1 .Fm) (hD1' .Fm) bx bx' (bD .Fm) (bD' .Fm)

  have S1 := skew .H (archDerivAt hw .H x) x' (iD .H) hx' (hD1 .H) hx'c (hxs.archDerivAt .H) hx's (hD2 .H .H) (hD1' .H)
    (bD .H) bx' (bDD .H .H) (bD' .H)
  have S2 := skew .H x (archDerivAt hw .H x') hx (iD' .H) hxc (hD1' .H) hxs (hx's.archDerivAt .H) (hD1 .H) (hD2' .H .H)
    bx (bD' .H) (bD .H) (bDD' .H .H)

  have S4 := skew .E (archDerivAt hw .Fm x) x' (iD .Fm) hx' (hD1 .Fm) hx'c (hxs.archDerivAt .Fm) hx's (hD2 .E .Fm) (hD1' .E)
    (bD .Fm) bx' (bDD .E .Fm) (bD' .E)
  have S5 := skew .Fm x (archDerivAt hw .E x') hx (iD' .E) hxc (hD1' .E) hxs (hx's.archDerivAt .E) (hD1 .Fm) (hD2' .Fm .E)
    bx (bD' .E) (bD .Fm) (bDD' .Fm .E)

  have CR : ∀ g, archDerivAt hw .Fm (archDerivAt hw .E x') g = archDerivAt hw .E (archDerivAt hw .Fm x') g - (archDerivAt hw .H x') g := by
    intro g
    have h := (AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt K hw x' hx's).2.2
    have hg := congrFun h g
    simp only [Pi.sub_apply] at hg
    rw [← hg]
    ring
  have T4 : ∫ g in 𝓕, x g * conj (archDerivAt hw .Fm (archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, x g * conj (archDerivAt hw .E (archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) - ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_sub (integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .E .Fm) bx (bDD' .E .Fm))
      (integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .H) bx (bD' .H))]
    congr 1
    funext g
    rw [CR g, map_sub, mul_sub]

  have I_HHx := integrable_mul_conj h𝓕m h𝓕s hfin (hD2 .H .H) hx'c (bDD .H .H) bx'
  have I_Hx := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .H) hx'c (bD .H) bx'
  have I_Ex := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .E) hx'c (bD .E) bx'
  have I_Fx := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .Fm) hx'c (bD .Fm) bx'
  have I_EFx := integrable_mul_conj h𝓕m h𝓕s hfin (hD2 .E .Fm) hx'c (bDD .E .Fm) bx'
  have I_HHx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .H .H) bx (bDD' .H .H)
  have I_Hx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .H) bx (bD' .H)
  have I_Ex' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .E) bx (bD' .E)
  have I_Fx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .Fm) bx (bD' .Fm)
  have I_EFx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .E .Fm) bx (bDD' .E .Fm)

  have EL1 : ∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (-1/4 : ℂ) * ∫ g in 𝓕, archDerivAt hw .H (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (1/2 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-1 : ℂ) * ∫ g in 𝓕, archDerivAt hw .E (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_HHx I_Hx I_EFx]
    congr 1
    funext g
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ER1 : ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (-1/4 : ℂ) * ∫ g in 𝓕, x g * conj (archDerivAt hw .H (archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (1/2 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-1 : ℂ) * ∫ g in 𝓕, x g * conj (archDerivAt hw .E (archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_HHx' I_Hx' I_EFx']
    congr 1
    funext g
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_neg, map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat]
    ring
  have EL2 : ∫ g in 𝓕, ((archDerivAt hw .H x) - Complex.I • ((archDerivAt hw .E x) + (archDerivAt hw .Fm x))) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, (archDerivAt hw .E x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx I_Ex I_Fx]
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have EL3 : ∫ g in 𝓕, ((archDerivAt hw .H x) + Complex.I • ((archDerivAt hw .E x) + (archDerivAt hw .Fm x))) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, (archDerivAt hw .E x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx I_Ex I_Fx]
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ER2 : ∫ g in 𝓕, x g * conj (((archDerivAt hw .H x') + Complex.I • ((archDerivAt hw .E x') + (archDerivAt hw .Fm x'))) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx' I_Ex' I_Fx']
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
    ring
  have ER3 : ∫ g in 𝓕, x g * conj (((archDerivAt hw .H x') - Complex.I • ((archDerivAt hw .E x') + (archDerivAt hw .Fm x'))) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, x g * conj ((archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, x g * conj ((archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx' I_Ex' I_Fx']
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_neg, map_mul,
      Complex.conj_I]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [EL1, ER1, S1, S2, S3, S4, S5, T4]
    ring
  · rw [EL2, ER2, S3, S6, S7]
    ring
  · rw [EL3, ER3, S3, S6, S7]
    ring

end UnitSymAlg25

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x)) (hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d x'))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B ∧ ‖archDerivAt hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B ∧ ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B)) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u - Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u + Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    (∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, lower x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (raise x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, raise x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (lower x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro lower raise
  exact UnitSymAlg25.main K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c hxs hx's hD1 hD1' hD2 hD2' B hB

end S_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain (solution)
