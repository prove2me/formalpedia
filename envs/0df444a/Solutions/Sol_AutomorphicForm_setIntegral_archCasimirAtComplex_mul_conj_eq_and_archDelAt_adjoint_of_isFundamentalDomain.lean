-- Prove2me | solution 1 for AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c1b83e6a-e182-5cc1-9c05-d8b7b2c217e3

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws50U1

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

theorem integral_lincomb {α : Type*} [MeasurableSpace α] (ν : Measure α) {n : ℕ} (c : Fin n → ℂ)
    (f : Fin n → α → ℂ) (hf : ∀ i, Integrable (f i) ν) :
    ∫ g, (∑ i, c i * f i g) ∂ν = ∑ i, c i * ∫ g, f i g ∂ν := by
  rw [integral_finset_sum _ fun i _ => (hf i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem archDerivAtComplex_globalPoints_mul {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x g := by
  intro γ g
  have h := archDerivAtComplex_comp_mul_left hw d x (globalPoints (𝓞 K) K γ)
  have hfun : (fun g => x (globalPoints (𝓞 K) K γ * g)) = x := funext (hx γ)
  rw [hfun] at h
  exact (congrFun h g).symm

theorem archDerivAtComplex_lin {w : InfinitePlace K} (hw : w.IsComplex) (X : ArchDirComplex)
    {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (hv : IsArchSmoothAtComplex hw v) (a b : ℂ) :
    archDerivAtComplex hw X (a • u + b • v) = a • archDerivAtComplex hw X u + b • archDerivAtComplex hw X v := by
  rw [archDerivAtComplex_add (hu.smul a) (hv.smul b), archDerivAtComplex_smul, archDerivAtComplex_smul]

theorem archDelAt_eq {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelAt hw d u = (1 / 2 : ℂ) • archDerivAtComplex hw d.toComplex u +
      (-(Complex.I / 2)) • archDerivAtComplex hw d.toComplexI u := by
  funext g
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem archDelBarAt_eq {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw d u = (1 / 2 : ℂ) • archDerivAtComplex hw d.toComplex u +
      (Complex.I / 2) • archDerivAtComplex hw d.toComplexI u := by
  funext g
  simp only [archDelBarAt, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem main
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD1' : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x'))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (hD2' : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B ∧ ‖archDerivAtComplex hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDirComplex,
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B)) :
    let pPlus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .E u + archDelBarAt hw .Fm u
    let pMinus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .Fm u + archDelBarAt hw .E u
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pPlus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pMinus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pMinus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pPlus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro pPlus pMinus
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have hfin : μ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  have bx : ∀ g ∈ slab K e₁ e₂, ‖x g‖ ≤ B := fun g hg => (hB g hg).1
  have bx' : ∀ g ∈ slab K e₁ e₂, ‖x' g‖ ≤ B := fun g hg => (hB g hg).2.1
  have bD : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d x g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).1
  have bD' : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d x' g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).2
  have bDD : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').1
  have bDD' : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').2

  have iD : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x g :=
    fun d => archDerivAtComplex_globalPoints_mul hw d hx
  have iD' : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x' (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x' g :=
    fun d => archDerivAtComplex_globalPoints_mul hw d hx'

  have skew : ∀ (d : ArchDirComplex) (u v : AdelicGL2 (𝓞 K) K → ℂ)
      (hu : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
      (hv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
      (huc : Continuous u) (hvc : Continuous v) (hus : IsArchSmoothAtComplex hw u) (hvs : IsArchSmoothAtComplex hw v)
      (hDu : Continuous (archDerivAtComplex hw d u)) (hDv : Continuous (archDerivAtComplex hw d v))
      (bu : ∀ g ∈ slab K e₁ e₂, ‖u g‖ ≤ B) (bv : ∀ g ∈ slab K e₁ e₂, ‖v g‖ ≤ B)
      (bDu : ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d u g‖ ≤ B)
      (bDv : ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d v g‖ ≤ B),
      ∫ g in 𝓕, archDerivAtComplex hw d u g * conj (v g) ∂μ = -∫ g in 𝓕, u g * conj (archDerivAtComplex hw d v g) ∂μ := by
    intro d u v hu hv huc hvc hus hvs hDu hDv bu bv bDu bDv
    have h := AutomorphicForm.setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain K w hw d e₁ e₂
      he₁ he 𝓕 h𝓕m h𝓕s h𝓕 u v hu hv huc hvc hus hvs hDu hDv B
      (fun g hg => ⟨bu g hg, bv g hg, bDu g hg, bDv g hg⟩)
    rw [integral_add (integrable_mul_conj h𝓕m h𝓕s hfin hDu hvc bDu bv)
      (integrable_mul_conj h𝓕m h𝓕s hfin huc hDv bu bDv)] at h
    exact eq_neg_of_add_eq_zero_left h

  have RA : ∀ d : ArchDirComplex,
      ∫ g in 𝓕, archDerivAtComplex hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDerivAtComplex hw d x' g) ∂μ :=
    fun d => skew d x x' hx hx' hxc hx'c hxs hx's (hD1 d) (hD1' d) bx bx' (bD d) (bD' d)

  have RC : ∀ X Y : ArchDirComplex,
      ∫ g in 𝓕, archDerivAtComplex hw X (archDerivAtComplex hw Y x) g * conj (x' g) ∂μ =
        ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Y (archDerivAtComplex hw X x') g) ∂μ := by
    intro X Y
    have h1 := skew X (archDerivAtComplex hw Y x) x' (iD Y) hx' (hD1 Y) hx'c (hxs.archDerivAtComplex Y) hx's
      (hD2 X Y) (hD1' X) (bD Y) bx' (bDD X Y) (bD' X)
    have h2 := skew Y x (archDerivAtComplex hw X x') hx (iD' X) hxc (hD1' X) hxs (hx's.archDerivAtComplex X)
      (hD1 Y) (hD2' Y X) bx (bD' X) (bD Y) (bDD' Y X)
    rw [h1, h2, neg_neg]

  have I1 : ∀ d, Integrable (fun g => archDerivAtComplex hw d x g * conj (x' g)) (μ.restrict 𝓕) :=
    fun d => integrable_mul_conj h𝓕m h𝓕s hfin (hD1 d) hx'c (bD d) bx'
  have I1' : ∀ d, Integrable (fun g => x g * conj (archDerivAtComplex hw d x' g)) (μ.restrict 𝓕) :=
    fun d => integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' d) bx (bD' d)
  have I2 : ∀ X Y, Integrable (fun g => archDerivAtComplex hw X (archDerivAtComplex hw Y x) g * conj (x' g)) (μ.restrict 𝓕) :=
    fun X Y => integrable_mul_conj h𝓕m h𝓕s hfin (hD2 X Y) hx'c (bDD X Y) bx'
  have I2' : ∀ X Y, Integrable (fun g => x g * conj (archDerivAtComplex hw X (archDerivAtComplex hw Y x') g)) (μ.restrict 𝓕) :=
    fun X Y => integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' X Y) bx (bDD' X Y)

  have ADJ1 : ∀ d : ArchDir, ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂μ := by
    intro d
    have hL : ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw d.toComplex x g * conj (x' g),
                 fun g => archDerivAtComplex hw d.toComplexI x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw d.toComplex x' g),
                 fun g => x g * conj (archDerivAtComplex hw d.toComplexI x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelBarAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, map_add, map_mul, map_div₀, Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [RA, RA]
    ring
  have ADJ2 : ∀ d : ArchDir, ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂μ := by
    intro d
    have hL : ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw d.toComplex x g * conj (x' g),
                 fun g => archDerivAtComplex hw d.toComplexI x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelBarAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw d.toComplex x' g),
                 fun g => x g * conj (archDerivAtComplex hw d.toComplexI x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, map_add, map_mul, map_div₀, map_neg, Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [RA, RA]
    ring

  have ddx : ∀ (X Y Z : ArchDirComplex) (a b : ℂ),
      archDerivAtComplex hw X (a • archDerivAtComplex hw Y x + b • archDerivAtComplex hw Z x) =
        a • archDerivAtComplex hw X (archDerivAtComplex hw Y x) + b • archDerivAtComplex hw X (archDerivAtComplex hw Z x) :=
    fun X Y Z a b => archDerivAtComplex_lin hw X (hxs.archDerivAtComplex Y) (hxs.archDerivAtComplex Z) a b
  have ddx' : ∀ (X Y Z : ArchDirComplex) (a b : ℂ),
      archDerivAtComplex hw X (a • archDerivAtComplex hw Y x' + b • archDerivAtComplex hw Z x') =
        a • archDerivAtComplex hw X (archDerivAtComplex hw Y x') + b • archDerivAtComplex hw X (archDerivAtComplex hw Z x') :=
    fun X Y Z a b => archDerivAtComplex_lin hw X (hx's.archDerivAtComplex Y) (hx's.archDerivAtComplex Z) a b

  have hC := AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex K hw x' hx's
  have Krel : ∀ (X Y Z : ArchDirComplex) (k : ℂ),
      archDerivAtComplex hw X (archDerivAtComplex hw Y x') - archDerivAtComplex hw Y (archDerivAtComplex hw X x') =
        k • archDerivAtComplex hw Z x' → (starRingEnd ℂ) k = k →
      ∫ g in 𝓕, x g * conj (archDerivAtComplex hw X (archDerivAtComplex hw Y x') g) ∂μ -
        ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Y (archDerivAtComplex hw X x') g) ∂μ =
        k * ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Z x' g) ∂μ := by
    intro X Y Z k h hk
    rw [← integral_sub (I2' X Y) (I2' Y X), ← integral_const_mul]
    congr 1
    funext g
    have hg := congrFun h g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hg
    rw [← mul_sub, ← map_sub, hg, map_mul, hk]
    ring
  have K1 := Krel .E .Fm .H 1 hC.2.2.1 (map_one _)
  have K2 := Krel .E .iFm .iH 1 hC.2.2.2.2.2.1 (map_one _)
  have K3 := Krel .iE .Fm .iH 1 hC.2.2.2.2.2.2.1 (map_one _)
  have K4 := Krel .iE .iFm .H (-1) hC.2.2.2.2.2.2.2.2.2.2.2.1 (by simp)
  refine ⟨ADJ1, ADJ2, ?_, ?_, ?_, ?_⟩
  ·
    have hL : ∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), Complex.I/16, Complex.I/16, (1/16 : ℂ), -(1/4 : ℂ), Complex.I/4, Complex.I/4, (1/4 : ℂ), (1/4 : ℂ), -(Complex.I/4)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1, I2])]
      congr 1
      funext g
      simp only [archCasimirAtComplex, archDelAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx, Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    have hR : ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), Complex.I/16, Complex.I/16, (1/16 : ℂ), -(1/4 : ℂ), Complex.I/4, Complex.I/4, (1/4 : ℂ), (1/4 : ℂ), -(Complex.I/4)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iH x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1', I2'])]
      congr 1
      funext g
      simp only [archCasimirBarAtComplex, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx', Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_add, map_sub, map_mul, map_div₀, Complex.conj_I,
        map_one, map_ofNat, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    rw [hL, hR]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, RC, RA]
    linear_combination (1/4 : ℂ) * K1 - (Complex.I/4) * K2 - (Complex.I/4) * K3 - (1/4 : ℂ) * K4
  ·
    have hL : ∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), -(Complex.I/16), -(Complex.I/16), (1/16 : ℂ), -(1/4 : ℂ), -(Complex.I/4), -(Complex.I/4), (1/4 : ℂ), (1/4 : ℂ), (Complex.I/4)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1, I2])]
      congr 1
      funext g
      simp only [archCasimirBarAtComplex, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx, Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    have hR : ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), -(Complex.I/16), -(Complex.I/16), (1/16 : ℂ), -(1/4 : ℂ), -(Complex.I/4), -(Complex.I/4), (1/4 : ℂ), (1/4 : ℂ), (Complex.I/4)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iH x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1', I2'])]
      congr 1
      funext g
      simp only [archCasimirAtComplex, archDelAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx', Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_add, map_sub, map_mul, map_div₀, Complex.conj_I,
        map_one, map_ofNat, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    rw [hL, hR]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, RC, RA]
    linear_combination (1/4 : ℂ) * K1 + (Complex.I/4) * K2 + (Complex.I/4) * K3 - (1/4 : ℂ) * K4
  ·
    show ∫ g in 𝓕, (archDelAt hw .E x + archDelBarAt hw .Fm x) g * conj (x' g) ∂μ =
      -∫ g in 𝓕, x g * conj ((archDelAt hw .Fm x' + archDelBarAt hw .E x') g) ∂μ
    have hL : ∫ g in 𝓕, (archDelAt hw .E x + archDelBarAt hw .Fm x) g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .E x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE x g * conj (x' g),
                 fun g => archDerivAtComplex hw .Fm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iFm x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj ((archDelAt hw .Fm x' + archDelBarAt hw .E x') g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .E x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iE x' g),
                 fun g => x g * conj (archDerivAtComplex hw .Fm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iFm x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_mul, map_div₀, map_neg,
        Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    rw [RA, RA, RA, RA]
    ring
  · show ∫ g in 𝓕, (archDelAt hw .Fm x + archDelBarAt hw .E x) g * conj (x' g) ∂μ =
      -∫ g in 𝓕, x g * conj ((archDelAt hw .E x' + archDelBarAt hw .Fm x') g) ∂μ
    have hL : ∫ g in 𝓕, (archDelAt hw .Fm x + archDelBarAt hw .E x) g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .Fm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iFm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .E x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj ((archDelAt hw .E x' + archDelBarAt hw .Fm x') g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .Fm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iFm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .E x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iE x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_mul, map_div₀, map_neg,
        Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    rw [RA, RA, RA, RA]
    ring

end Ws50U1

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
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
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD1' : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x'))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (hD2' : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B ∧ ‖archDerivAtComplex hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDirComplex,
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B)) :
    let pPlus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .E u + archDelBarAt hw .Fm u
    let pMinus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .Fm u + archDelBarAt hw .E u
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pPlus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pMinus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pMinus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pPlus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro pPlus pMinus
  exact Ws50U1.main K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c hxs hx's hD1 hD1' hD2 hD2' B hB

end S_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain (solution)
