-- Prove2me | solution 1 for AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9c74eee8-5635-511e-add6-e2c629fab071

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Bessel17

open scoped InnerProductSpace ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

abbrev nuBox : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)

scoped instance : IsProbabilityMeasure (nuBox F) := isProbabilityMeasure_cond_adelicBox F

scoped instance countablePrincipal : Countable ↥(AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  refine Function.Surjective.countable (f := fun k : F =>
    (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : ↥(AdeleRing.principalSubgroup (𝓞 F) F))) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

theorem setIntegral_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u in adelicBox F, G (u + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ u in adelicBox F, G u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  have h1 : ∫ u in adelicBox F, G (u + x) ∂μ = ∫ w in (fun u => u + x) '' adelicBox F, G w ∂μ := by
    have hme : MeasurableEmbedding (fun u : AdeleRing (𝓞 F) F => u + x) :=
      (Homeomorph.addRight x).measurableEmbedding
    conv_lhs => rw [← Set.preimage_image_eq (adelicBox F) (add_left_injective x)]
    rw [← hme.setIntegral_map, map_add_right_eq_self]
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox F μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun u => u + x) '' adelicBox F) μ := by
    refine hFD.image_of_equiv (ν := μ) (Equiv.addRight x) ?_ (Equiv.refl _) ?_
    · simpa using (measurePreserving_add_right μ (-x)).quasiMeasurePreserving
    · intro γ u
      show (γ +ᵥ u) + x = γ +ᵥ (u + x)
      simp only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F), G (γ +ᵥ u) = G u := by
    rintro ⟨_, β, rfl⟩ u
    exact hG β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

theorem integral_nuBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u, G (u + x) ∂(nuBox F) = ∫ u, G u ∂(nuBox F) := by
  simp only [nuBox, ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add_right F G hG x]

variable {F}

theorem integral_addChar_mul_eq_zero {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {γ : F} (hγ : γ ≠ 0) :
    ∫ u, ψ (algebraMap F (AdeleRing (𝓞 F) F) γ * u) ∂(nuBox F) = 0 := by
  set a := algebraMap F (AdeleRing (𝓞 F) F) γ with ha
  set I := ∫ u, ψ (a * u) ∂(nuBox F) with hI
  have hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), ψ (a * (algebraMap F (AdeleRing (𝓞 F) F) β + u)) = ψ (a * u) := by
    intro β u
    rw [mul_add, AddChar.map_add_eq_mul, ha, ← (algebraMap F (AdeleRing (𝓞 F) F)).map_mul, hψ.principalInvariant, one_mul]
  have hshift : ∀ x, ψ (a * x) * I = I := by
    intro x
    have h := integral_nuBox_comp_add_right F (fun u => ψ (a * u)) hper x
    simp only [mul_add, AddChar.map_add_eq_mul] at h
    rw [integral_mul_const] at h
    rw [mul_comm]
    exact h
  by_contra hne
  have hone : ∀ x, ψ (a * x) = 1 := fun x =>
    mul_left_injective₀ hne ((hshift x).trans (one_mul I).symm)
  apply hψ.nontrivial
  ext y
  have hy : y = a * (algebraMap F (AdeleRing (𝓞 F) F) γ⁻¹ * y) := by
    rw [← mul_assoc, ha, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_mul]
  rw [hy, hone, AddChar.one_apply]

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

theorem productionPinsOf_ν_eq : (productionPinsOf F D U gen (adelicBox F)).ν = nuBox F := rfl

variable {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

def ech (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (u : AdeleRing (𝓞 F) F) : ℂ :=
  ψ (algebraMap F (AdeleRing (𝓞 F) F) α * u)

theorem continuous_ech (hψ : IsGlobalAddChar F ψ) (α : F) : Continuous (ech ψ α) :=
  hψ.continuous.comp (continuous_const.mul continuous_id)

theorem norm_ech (hψ : IsGlobalAddChar F ψ) (α : F) (u : AdeleRing (𝓞 F) F) : ‖ech ψ α u‖ = 1 :=
  NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _

theorem memLp_ech (hψ : IsGlobalAddChar F ψ) (α : F) : MemLp (ech ψ α) 2 (nuBox F) :=
  MemLp.of_bound (continuous_ech hψ α).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun u => (norm_ech hψ α u).le)

theorem conj_ech (hψ : IsGlobalAddChar F ψ) (α : F) (u : AdeleRing (𝓞 F) F) :
    conj (ech ψ α u) = ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * u)) := by
  rw [ech, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _)]

theorem memLp_of_continuous {h : AdeleRing (𝓞 F) F → ℂ} (hh : Continuous h) : MemLp h 2 (nuBox F) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hh.continuousOn
  refine MemLp.of_bound hh.aestronglyMeasurable M ?_
  have : ∀ᵐ u ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)), ‖h u‖ ≤ M :=
    (ae_restrict_iff' (measurableSet_adelicBox F)).mpr (Filter.Eventually.of_forall fun u hu => hM u (hBC hu))
  exact Measure.ae_smul_measure this _

end Bessel17
p2m_reactivate "P2MW.S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.Bessel17"

namespace Bessel17

open scoped InnerProductSpace ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

theorem inner_toLp {f g : AdeleRing (𝓞 F) F → ℂ} (hf : MemLp f 2 (nuBox F)) (hg : MemLp g 2 (nuBox F)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ u, conj (f u) * g u ∂(nuBox F) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with u hfu hgu
  rw [hfu, hgu, RCLike.inner_apply, mul_comm]

theorem norm_toLp_sq {f : AdeleRing (𝓞 F) F → ℂ} (hf : MemLp f 2 (nuBox F)) :
    ‖hf.toLp f‖ ^ 2 = ∫ u, ‖f u‖ ^ 2 ∂(nuBox F) := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toLp hf hf]
  have : (fun u => conj (f u) * f u) = fun u => ((‖f u‖ ^ 2 : ℝ) : ℂ) := funext fun u => by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [this]
  have h2 : ∫ u, ((‖f u‖ ^ 2 : ℝ) : ℂ) ∂(nuBox F) = ((∫ u, ‖f u‖ ^ 2 ∂(nuBox F) : ℝ) : ℂ) := integral_ofReal
  rw [h2]
  exact Complex.ofReal_re _

variable {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem orthonormal_ech (hψ : IsGlobalAddChar F ψ) :
    Orthonormal ℂ (fun α : F => (memLp_ech hψ α).toLp (ech ψ α)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [inner_toLp]
  have hprod : ∀ u, conj (ech ψ α u) * ech ψ β u = ψ (algebraMap F (AdeleRing (𝓞 F) F) (β - α) * u) := by
    intro u
    rw [conj_ech hψ, ech, ← AddChar.map_add_eq_mul, map_sub]
    congr 1
    ring
  simp_rw [hprod]
  by_cases h : α = β
  · subst h
    simp
  · rw [if_neg h]
    exact integral_addChar_mul_eq_zero hψ (sub_ne_zero.mpr (Ne.symm h))

theorem main (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (A : Finset F) :
    ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν := by
  set h : AdeleRing (𝓞 F) F → ℂ := fun u => φ (unipotentGL2 u * g) with hh
  have hmem : MemLp h 2 (nuBox F) := memLp_of_continuous hcont
  have hW : ∀ α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g =
      inner ℂ ((memLp_ech hψ α).toLp (ech ψ α)) (hmem.toLp h) := by
    intro α
    rw [inner_toLp]
    show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂(nuBox F)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show φ (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * u)) = conj (ech ψ α u) * h u
    rw [conj_ech hψ, mul_comm]
  show ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖h u‖ ^ 2 ∂(nuBox F)
  simp_rw [hW, ← norm_toLp_sq hmem]
  exact (orthonormal_ech hψ).sum_inner_products_le _

end Bessel17
p2m_reactivate "P2MW.S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.Bessel17"

end
p2m_reactivate "P2MW.S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.Bessel17"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (A : Finset F) :
    ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν :=
  Bessel17.main D U gen ψ hψ φ g hcont A

end S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
end P2MW
export P2MW.S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq (solution)
