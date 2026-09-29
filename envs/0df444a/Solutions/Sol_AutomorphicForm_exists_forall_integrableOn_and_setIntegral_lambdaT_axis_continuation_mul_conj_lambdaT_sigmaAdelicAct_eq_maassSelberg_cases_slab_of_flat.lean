-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3bda072f-2014-57d1-8cf2-66001f1547e4

import Mathlib
import Theorems.Thm_AutomorphicForm_isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4MsxSigma

open AutomorphicForm

section Alpha

variable (L : Type) [Field L] [NumberField L]

set_option quotPrecheck false in
local notation "αL" => ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ))

theorem cpowChar_val_add (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s₁ s₂ : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((cpowChar αL hα (s₁ + s₂) z : ℂˣ) : ℂ) =
    ((cpowChar αL hα s₁ z : ℂˣ) : ℂ) *
    ((cpowChar αL hα s₂ z : ℂˣ) : ℂ) := by
  rw [cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val]
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα z).ne')

theorem cpowChar_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (a b : ℂ) :
    cpowChar αL hα a * cpowChar αL hα b = cpowChar αL hα (a + b) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_val_add]

theorem mul_cpowChar_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (a b : ℂ) : χ * cpowChar αL hα a * cpowChar αL hα b = χ * cpowChar αL hα (a + b) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_val_add, mul_assoc]

theorem cpowChar_eq_one_of_mem_normOneIdeles (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s : ℂ)
    {z : (AdeleRing (𝓞 L) L)ˣ} (hz : z ∈ NumberField.TateGlobal.normOneIdeles L) :
    cpowChar αL hα s z = 1 := by
  apply Units.ext
  rw [cpowChar_apply_val, Units.val_one]
  have h : ((αL z : ℝˣ) : ℝ) = 1 := (NumberField.TateGlobal.mem_normOneIdeles_iff z).mp hz
  rw [h, Complex.ofReal_one, Complex.one_cpow]

theorem normPowChar_eq_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (τ : ℝ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.normPowChar L τ z = cpowChar αL hα ((τ : ℂ) * Complex.I) z := by
  apply Units.ext
  rw [NumberField.TateGlobal.coe_normPowChar_apply, cpowChar_apply_val, mul_comm Complex.I]
  rfl

theorem cpowChar_inv (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (cpowChar αL hα s z)⁻¹ = cpowChar αL hα (-s) z := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, ← cpowChar_val_add, add_neg_cancel, cpowChar_apply_val, Complex.cpow_zero, Units.val_one]

theorem etaFst_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (μ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a s : ℂ) :
    etaFst (μ * cpowChar αL hα a) αL hα s = etaFst μ αL hα (s + a) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    show s + a + 1 / 2 = a + (s + 1 / 2) by ring, cpowChar_val_add L hα a (s + 1 / 2) z, mul_assoc]

theorem etaSnd_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a s : ℂ) :
    etaSnd (ν * cpowChar αL hα (-a)) αL hα s = etaSnd ν αL hα (s + a) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    show -(s + a + 1 / 2) = -a + -(s + 1 / 2) by ring, cpowChar_val_add L hα (-a) (-(s + 1 / 2)) z, mul_assoc]

theorem isUnitaryChar_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχ : IsUnitaryChar (𝓞 L) L χ) (a : ℂ) (ha : a.re = 0) :
    IsUnitaryChar (𝓞 L) L (χ * cpowChar αL hα a) := by
  intro z
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ z, one_mul]
  exact cpowChar_isUnitaryChar_of_re_eq_zero ha z

theorem isPrincipalTrivial_alpha : IsPrincipalTrivial (R := 𝓞 L) (K := L) αL := by
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel _ _
  intro u
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap L u
  rw [← Units.val_eq_one]
  have e : ∀ w : (AdeleRing (𝓞 L) L)ˣ, ((αL w : ℝˣ) : ℝ) = ((distribHaarChar (AdeleRing (𝓞 L) L) w : ℝ≥0) : ℝ) :=
    fun w => rfl
  rw [e]
  have hu : Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom u := Units.ext rfl
  rw [hu, h, NNReal.coe_one]

theorem isIdeleClassChar_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχ : IsIdeleClassChar (𝓞 L) L χ) (a : ℂ) :
    IsIdeleClassChar (𝓞 L) L (χ * cpowChar αL hα a) := by
  intro u
  rw [MonoidHom.mul_apply, hχ u, cpowChar_isIdeleClassChar (isPrincipalTrivial_alpha L) a u, one_mul]

theorem continuous_cpowChar_val (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (a : ℂ) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((cpowChar αL hα a z : ℂˣ) : ℂ) := by
  have h : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((cpowChar αL hα a z : ℂˣ) : ℂ)) =
      fun z => ((NumberField.TateGlobal.ideleNorm L z : ℝ) : ℂ) ^ a := by
    funext z; rw [cpowChar_apply_val]; rfl
  rw [h]
  refine Continuous.cpow ?_ continuous_const fun z => ?_
  · exact Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L)
  · exact Complex.ofReal_mem_slitPlane.mpr (NumberField.TateGlobal.ideleNorm_pos z)

theorem continuous_mul_cpowChar_val (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((χ x : ℂˣ) : ℂ)) (a : ℂ) :
    Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => (((χ * cpowChar αL hα a) x : ℂˣ) : ℂ) := by
  have h : (fun x : (AdeleRing (𝓞 L) L)ˣ => (((χ * cpowChar αL hα a) x : ℂˣ) : ℂ)) =
      fun x => ((χ x : ℂˣ) : ℂ) * ((cpowChar αL hα a x : ℂˣ) : ℂ) := by
    funext x; rw [MonoidHom.mul_apply, Units.val_mul]
  rw [h]; exact hχk.mul (continuous_cpowChar_val L hα a)

end Alpha

section Translate

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

theorem unitsAct_eq_unitsMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct g z =
      Units.map ((D.act g : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z := by
  ext; rfl

theorem continuous_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct g z := by
  have h : (fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct g z) =
      Units.map ((D.act g : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) :=
    funext fun z => unitsAct_eq_unitsMap K L D g z
  rw [h]
  exact Continuous.units_map _ (D.continuous_act g)

def trChar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ :=
  χ.comp (D.unitsAct g).toMonoidHom

theorem trChar_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    trChar K L D g χ z = χ (D.unitsAct g z) := rfl

theorem isUnitaryChar_trChar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hχ : IsUnitaryChar (𝓞 L) L χ) :
    IsUnitaryChar (𝓞 L) L (trChar K L D g χ) := fun z => hχ (D.unitsAct g z)

theorem isIdeleClassChar_trChar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 L) L χ) :
    IsIdeleClassChar (𝓞 L) L (trChar K L D g χ) := by
  intro u
  rw [trChar_apply]
  have h : D.unitsAct g (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) u) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L)) (Units.map ((g : L ≃ₐ[K] L) : L →* L) u) :=
    Units.ext (D.compat g (u : L))
  rw [h]
  exact hχ _

theorem continuous_trChar_val (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hχk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((χ x : ℂˣ) : ℂ)) :
    Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((trChar K L D g χ x : ℂˣ) : ℂ) :=
  hχk.comp (continuous_unitsAct K L D g)

end Translate

section LevelBot

variable (L : Type) [Field L] [NumberField L]

theorem eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 L) L} (hx : x ∈ idealBall (𝓞 L) L ⊥) : x = 0 := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  have h := hx v
  rw [idealBound_bot] at h
  exact (map_eq_zero _).mp (le_antisymm h zero_le')

theorem eq_one_of_mem_principalLevel_bot_inf {u : AdelicGL2 (𝓞 L) L}
    (hu : u ∈ principalLevel (𝓞 L) L ⊥ ⊓ finiteAdelicGL2Subgroup L) : u = 1 := by
  obtain ⟨h12, hfin⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨h1, h2⟩ := (mem_principalLevel_iff (𝓞 L) L ⊥).mp h12
  rw [mem_finiteAdelicGL2Subgroup_iff] at hfin

  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  have e10 : ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0).2 = 0 := by
    have := eq_zero_of_mem_idealBall_bot L h1.1.lowerLeft
    rwa [glFin_apply] at this
  have e11 : ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1).2 = 1 := by
    have := eq_zero_of_mem_idealBall_bot L h1.1.lowerRight
    rw [glFin_apply] at this
    exact sub_eq_zero.mp this

  obtain ⟨h, hh, hhu⟩ := Subgroup.mem_map.mp h2
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hh
  have hconj : h = (weyl (𝓞 L) L)⁻¹ * u * weyl (𝓞 L) L := by
    rw [← hhu]
    change h = (weyl (𝓞 L) L)⁻¹ * (weyl (𝓞 L) L * h * (weyl (𝓞 L) L)⁻¹) * weyl (𝓞 L) L
    group
  have hw : ((weyl (𝓞 L) L : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      = !![0, 1; 1, 0] := rfl
  have hwi : (((weyl (𝓞 L) L)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      = !![0, 1; 1, 0] := rfl
  have hent : ∀ i j : Fin 2, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) =
      ∑ b : Fin 2, ∑ a : Fin 2, (!![(0 : AdeleRing (𝓞 L) L), 1; 1, 0]) i a *
        (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) a b * (!![(0 : AdeleRing (𝓞 L) L), 1; 1, 0]) b j := by
    intro i j
    rw [hconj, Units.val_mul, Units.val_mul, hw, hwi, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  have h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 =
      (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 := by
    rw [hent]; simp [Fin.sum_univ_two]
  have h11 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 =
      (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 := by
    rw [hent]; simp [Fin.sum_univ_two]
  have e01 : ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1).2 = 0 := by
    have := eq_zero_of_mem_idealBall_bot L hh.1.lowerLeft
    rwa [glFin_apply, h10] at this
  have e00 : ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0).2 = 1 := by
    have := eq_zero_of_mem_idealBall_bot L hh.1.lowerRight
    rw [glFin_apply, h11] at this
    exact sub_eq_zero.mp this

  have einf : ∀ i j : Fin 2, ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) := by
    intro i j
    have := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing L) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) hfin
    simpa [glArch_apply] using this
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · rw [einf i j, Units.val_one]
    fin_cases i <;> fin_cases j <;> rfl
  · rw [Units.val_one]
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11

end LevelBot

section Shift

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

set_option quotPrecheck false in
local notation "αL" => ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ))

theorem shift_family (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a : ℂ)
    (μ₁ ν₁ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hμ₁ : μ₁ = μ * cpowChar αL hα a) (hν₁ : ν₁ = ν * cpowChar αL hα (-a))
    (f : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αL hα s) (etaSnd ν αL hα s) (f s))
    (hfK : ∀ s, IsArchKFinite L (f s))
    (hff : ∀ s, IsKfSmooth L (f s))
    (hfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => f p.1 p.2))
    (hfhol : ∀ g, Differentiable ℂ (fun s => f s g))
    (hfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => f s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
    (hflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
      f s (k : AdelicGL2 (𝓞 L) L) = f 0 (k : AdelicGL2 (𝓞 L) L)) :
    (∀ s, IsInducedSection (𝓞 L) L (etaFst μ₁ αL hα s)
      (etaSnd ν₁ αL hα s) ((fun s g => f (s + a) g) s)) ∧
    (∀ s, IsArchKFinite L ((fun s g => f (s + a) g) s)) ∧
    (∀ s, IsKfSmooth L ((fun s g => f (s + a) g) s)) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => f (s + a) g) p.1 p.2) ∧
    (∀ g, Differentiable ℂ (fun s => (fun s g => f (s + a) g) s g)) ∧
    (∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => (fun s g => f (s + a) g) s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W) ∧
    (∀ (s : ℂ) (k : adelicMaximalCompact L),
      (fun s g => f (s + a) g) s (k : AdelicGL2 (𝓞 L) L) = (fun s g => f (s + a) g) 0 (k : AdelicGL2 (𝓞 L) L)) := by
  refine ⟨fun s => ?_, fun s => hfK (s + a), fun s => hff (s + a), ?_, fun g => ?_, fun w => ?_, fun s k => ?_⟩
  · rw [hμ₁, hν₁, etaFst_mul_cpowChar, etaSnd_mul_cpowChar]; exact hf (s + a)
  · exact hfjc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · exact (hfhol g).comp (differentiable_id.add_const a)
  · obtain ⟨W, hW, hmem⟩ := hfKu w
    exact ⟨W, hW, fun s g => hmem (s + a) g⟩
  · show f (s + a) k = f (0 + a) k
    rw [hflat (s + a) k, hflat (0 + a) k]

theorem shift_continuation (a : ℂ) (ha : a.re = 0)
    (f : ℂ → AdelicGL2 (𝓞 L) L → ℂ) (O : Set ℂ) (E Nn : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (h : IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => E s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nn s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => E p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nn p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        E s g = f s g + ∑' ξ : L, f s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nn s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (f s) g)) :
    IsOpen {s : ℂ | s + a ∈ O} ∧ IsPreconnected {s : ℂ | s + a ∈ O} ∧
      {s : ℂ | s.re = 0} ⊆ {s : ℂ | s + a ∈ O} ∧ {s : ℂ | 1 / 2 < s.re} ⊆ {s : ℂ | s + a ∈ O} ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => (fun s g => E (s + a) g) s g) {s : ℂ | s + a ∈ O}) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => (fun s g => Nn (s + a) g) s g) {s : ℂ | s + a ∈ O}) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => E (s + a) g) p.1 p.2) ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => Nn (s + a) g) p.1 p.2) ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        (fun s g => E (s + a) g) s g = (fun s g => f (s + a) g) s g + ∑' ξ : L, (fun s g => f (s + a) g) s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        (fun s g => Nn (s + a) g) s g =
          weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) ((fun s g => f (s + a) g) s) g) := by
  obtain ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEf, hNf⟩ := h
  have hpre : {s : ℂ | s + a ∈ O} = (Homeomorph.addRight a) ⁻¹' O := rfl
  have hre : ∀ s : ℂ, (s + a).re = s.re := fun s => by rw [Complex.add_re, ha, add_zero]
  have hmaps : Set.MapsTo (fun s : ℂ => s + a) {s : ℂ | s + a ∈ O} O := fun s hs => hs
  have hcsh : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1 + a, p.2) :=
    (continuous_fst.add continuous_const).prodMk continuous_snd
  have hmaps2 : Set.MapsTo (fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1 + a, p.2))
      ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) (O ×ˢ Set.univ) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  refine ⟨?_, ?_, fun s hs => ?_, fun s hs => ?_, fun g => ?_, fun g => ?_, ?_, ?_, fun s hs g => ?_, fun s hs g => ?_⟩
  · rw [hpre]; exact (Homeomorph.addRight a).continuous.isOpen_preimage O hO
  · rw [hpre]; exact (Homeomorph.addRight a).isPreconnected_preimage.mpr hOc
  · show s + a ∈ O
    exact hax (show (s + a).re = 0 by rw [hre]; exact hs)
  · show s + a ∈ O
    exact hhalf (show 1 / 2 < (s + a).re by rw [hre]; exact hs)
  · exact (hEan g).comp (analyticOnNhd_id.add analyticOnNhd_const) hmaps
  · exact (hNan g).comp (analyticOnNhd_id.add analyticOnNhd_const) hmaps
  · exact hEc.comp hcsh.continuousOn hmaps2
  · exact hNc.comp hcsh.continuousOn hmaps2
  · exact hEf (s + a) (by rw [hre]; exact hs) g
  · exact hNf (s + a) (by rw [hre]; exact hs) g

theorem deriv_shift (Nn : ℂ → AdelicGL2 (𝓞 L) L → ℂ) (a p q : ℂ) (hpq : p + a = q) (x : AdelicGL2 (𝓞 L) L) :
    deriv (fun s : ℂ => (fun s g => Nn (s + a) g) s x) p = deriv (fun s : ℂ => Nn s x) q := by
  show deriv (fun s : ℂ => Nn (s + a) x) p = deriv (fun s : ℂ => Nn s x) q
  rw [deriv_comp_add_const (fun s => Nn s x) a p, hpq]

end Shift

end R4MsxSigma

end

open AutomorphicForm R4MsxSigma in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ cMS : ℝ, 0 < cMS ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite L (φf s))
      (_hφff : ∀ s, IsKfSmooth L (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        φf s (k : AdelicGL2 (𝓞 L) L) = φf 0 (k : AdelicGL2 (𝓞 L) L))
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eφ s g = φf s g + ∑' ξ : L, φf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nφ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g))
      (t : ℝ) (R : ℝ) (_hR : R₀ ≤ R),
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I))
          x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
          x))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        ∀ θ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ z = ν z * cpowChar αm hαm ((θ : ℂ) * Complex.I) z) → 2 * t + θ ≠ 0 →
        (∫ x in Φ₀,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf 0 (k : AdelicGL2 (𝓞 L) L) * conj (ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
            + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θ : ℂ))) / (Complex.I * (2 * (t : ℂ) + (θ : ℂ)))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θ : ℂ)))) / (Complex.I * (2 * (t : ℂ) + (θ : ℂ))) )) ∧
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
        (∫ x in Φ₀,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf 0 (k : AdelicGL2 (𝓞 L) L) * conj (ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) )) ∧
      ((∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) →
        (∀ τ : ℝ, ¬ ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) ∧
            (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z))) →
        (∫ x in Φ₀,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0) ∧
      (∀ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z) →
        (∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) → 2 * t + τ ≠ 0 →
        (∫ x in Φ₀,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τ : ℂ))) / (Complex.I * (2 * (t : ℂ) + (τ : ℂ)))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τ : ℂ)))) / (Complex.I * (2 * (t : ℂ) + (τ : ℂ))) )) := by
  intro αm hαm

  obtain ⟨cMS, hcpos, R₀, HMS⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat
      L α β hα hαβ ΦL c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ hαm
  refine ⟨cMS, hcpos, R₀, ?_⟩
  intro μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ t R hR

  have hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
      ∀ u ∈ principalLevel (𝓞 L) L ⊥ ⊓ finiteAdelicGL2Subgroup L, ψf s (g * u) = ψf s g := by
    intro s g u hu
    rw [eq_one_of_mem_principalLevel_bot_inf L hu, mul_one]

  have hpair0 : ∀ (hflatσ : ∀ (s : ℂ) (k : adelicMaximalCompact L),
      ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) =
        ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))),
      (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) =
      (∫ k, φf 0 (k : AdelicGL2 (𝓞 L) L) * conj (ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) := by
    intro hflatσ
    congr 1
    funext k
    rw [hφflat ((t : ℂ) * Complex.I) k, hflatσ ((t : ℂ) * Complex.I) k]

  obtain ⟨S1, S2, S3, S4, S5, S6, S7, _S8, S9⟩ :=
    AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
      K L D σ ⊥ hαm μ ν (trChar K L D σ.symm μ) (trChar K L D σ.symm ν) (fun z => rfl) (fun z => rfl)
      ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
  have Ho := HMS μ ν (trChar K L D σ.symm μ) (trChar K L D σ.symm ν)
    hμ hν (isUnitaryChar_trChar K L D σ.symm μ hμ) (isUnitaryChar_trChar K L D σ.symm ν hν)
    hμF hνF (isIdeleClassChar_trChar K L D σ.symm μ hμF) (isIdeleClassChar_trChar K L D σ.symm ν hνF)
    hμk hνk (continuous_trChar_val K L D σ.symm μ hμk) (continuous_trChar_val K L D σ.symm ν hνk)
    φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
    (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) S1 S2 S3 S4 S5 S6 S7
    Oφ Eφ Nφ hEφ Oψ (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) S9 t R hR
  refine ⟨Ho.1, ?_, ?_, ?_, ?_⟩
  ·
    intro hinvμ hinvν θ hθ h2t
    obtain ⟨T1, T2, T3, T4, T5, T6, T7, _T8, T9⟩ :=
      AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
        K L D σ ⊥ hαm μ ν μ ν (fun z => (hinvμ z).symm) (fun z => (hinvν z).symm)
        ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
    have hθ' : μ = ν * cpowChar αm hαm ((θ : ℂ) * Complex.I) := MonoidHom.ext hθ
    have hare : (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)).re = 0 := by simp
    have hbre : ((((θ / 2 : ℝ) : ℂ)) * Complex.I).re = 0 := by simp

    have hμ₀1 : ν * cpowChar αm hαm ((((θ / 2 : ℝ) : ℂ)) * Complex.I) = μ * cpowChar αm hαm (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) := by
      rw [hθ', mul_cpowChar_mul_cpowChar]
      congr 2; push_cast; ring
    have hμ₀2 : ν * cpowChar αm hαm ((((θ / 2 : ℝ) : ℂ)) * Complex.I) = ν * cpowChar αm hαm (-(-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) := by
      rw [neg_neg]
    obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ :=
      shift_family L hαm μ ν (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) _ _ hμ₀1 hμ₀2 φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
    obtain ⟨B1, B2, B3, B4, B5, B6, B7⟩ :=
      shift_family L hαm μ ν (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) _ _ hμ₀1 hμ₀2 (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T1 T2 T3 T4 T5 T6 T7
    have CA := shift_continuation L (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) hare φf Oφ Eφ Nφ hEφ
    have CB := shift_continuation L (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) hare (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T9
    have u0 := isUnitaryChar_mul_cpowChar L hαm ν hν ((((θ / 2 : ℝ) : ℂ)) * Complex.I) hbre
    have F0 := isIdeleClassChar_mul_cpowChar L hαm ν hνF ((((θ / 2 : ℝ) : ℂ)) * Complex.I)
    have k0 := continuous_mul_cpowChar_val L hαm ν hνk ((((θ / 2 : ℝ) : ℂ)) * Complex.I)
    have ht' : t + θ / 2 ≠ 0 := fun h => h2t (by linarith)
    have H := (HMS _ _ _ _ u0 u0 u0 u0 F0 F0 F0 F0 k0 k0 k0 k0
      (fun s g => φf (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) g) A1 A2 A3 A4 A5 A6 A7
      (fun s g => ψf (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) B1 B2 B3 B4 B5 B6 B7
      {s : ℂ | s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) ∈ Oφ} (fun s g => Eφ (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) g) (fun s g => Nφ (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) g) CA
      {s : ℂ | s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) ∈ Oψ} (fun s g => Eψ (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) CB
      (t + θ / 2) R hR).2.1 rfl rfl rfl ht'
    have hc : (((t + θ / 2 : ℝ)) : ℂ) * Complex.I + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) = (t : ℂ) * Complex.I := by push_cast; ring
    have e1 : 2 * Complex.I * (R : ℂ) * (((t + θ / 2 : ℝ)) : ℂ) = Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θ : ℂ)) := by push_cast; ring
    have e2 : 2 * Complex.I * (((t + θ / 2 : ℝ)) : ℂ) = Complex.I * (2 * (t : ℂ) + (θ : ℂ)) := by push_cast; ring
    have hd : ∀ x : AdelicGL2 (𝓞 L) L,
        deriv (fun s : ℂ => Nψ (s + (-((((θ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) ((((t + θ / 2 : ℝ)) : ℂ) * Complex.I) =
          deriv (fun s : ℂ => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) ((t : ℂ) * Complex.I) :=
      fun x => deriv_shift L (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (-((((θ / 2 : ℝ) : ℂ)) * Complex.I)) _ _ hc x
    simp only [hc, e1, e2, hd] at H
    rw [hpair0 T7] at H
    simp only []
    exact H
  ·
    intro hinvμ hinvν hoff ht
    obtain ⟨T1, T2, T3, T4, T5, T6, T7, _T8, T9⟩ :=
      AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
        K L D σ ⊥ hαm μ ν μ ν (fun z => (hinvμ z).symm) (fun z => (hinvν z).symm)
        ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
    have H := (HMS μ ν μ ν hμ hν hμ hν hμF hνF hμF hνF hμk hνk hμk hνk
      φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
      (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T1 T2 T3 T4 T5 T6 T7
      Oφ Eφ Nφ hEφ Oψ (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T9 t R hR).2.2.1 rfl rfl hoff ht
    simp only [] at H
    rw [hpair0 T7] at H
    simp only []
    exact H
  ·
    intro hninv hnrev
    have hD1 : ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        trChar K L D σ.symm μ z ≠ μ z ∨ trChar K L D σ.symm ν z ≠ ν z := by
      by_contra hcon
      push Not at hcon
      have hμall := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D σ.symm μ (fun w hw => (hcon w hw).1)
      have hνall := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D σ.symm ν (fun w hw => (hcon w hw).2)
      obtain ⟨z, hz⟩ := hninv
      rcases hz with h | h
      · exact h (hμall z)
      · exact h (hνall z)
    have hD2 : ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        trChar K L D σ.symm μ z ≠ ν z ∨ trChar K L D σ.symm ν z ≠ μ z := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ, hτ1, hτ2⟩ := M4aHerbrand.IdeleGaloisDescent.exists_forall_apply_unitsAct_eq_mul_normPowChar_of_forall_mem_normOneIdeles_eq_swap K L D σ.symm μ ν hμ hν hμk hνk
        (fun w hw => (hcon w hw).1) (fun w hw => (hcon w hw).2)
      apply hnrev τ
      refine ⟨fun z => ?_, fun z => ?_⟩
      · rw [hτ1 z, normPowChar_eq_cpowChar L hαm τ z]
      · rw [hτ2 z, normPowChar_eq_cpowChar L hαm τ z, cpowChar_inv]
    exact Ho.2.2.2.2 hD1 hD2
  ·
    intro τ hC1 hC2 hninv h2t
    obtain ⟨T1, T2, T3, T4, T5, T6, T7, _T8, T9⟩ :=
      AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
        K L D σ ⊥ hαm μ ν (ν * cpowChar αm hαm ((τ : ℂ) * Complex.I)) (μ * cpowChar αm hαm (-((τ : ℂ) * Complex.I)))
        (fun z => by rw [MonoidHom.mul_apply]; exact (hC1 z).symm)
        (fun z => by rw [MonoidHom.mul_apply]; exact (hC2 z).symm)
        ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
    have hare : (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)).re = 0 := by simp
    have hnare : (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I))).re = 0 := by rw [Complex.neg_re, hare, neg_zero]

    obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ :=
      shift_family L hαm μ ν (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) (μ * cpowChar αm hαm (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) (ν * cpowChar αm hαm (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I)))) rfl rfl φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat

    have hB1 : ν * cpowChar αm hαm (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) =
        ν * cpowChar αm hαm ((τ : ℂ) * Complex.I) * cpowChar αm hαm (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) := by
      rw [mul_cpowChar_mul_cpowChar]
      congr 2; push_cast; ring
    have hB2 : μ * cpowChar αm hαm (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) =
        μ * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) * cpowChar αm hαm (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) := by
      rw [mul_cpowChar_mul_cpowChar]
      congr 2; push_cast; ring
    obtain ⟨B1, B2, B3, B4, B5, B6, B7⟩ :=
      shift_family L hαm (ν * cpowChar αm hαm ((τ : ℂ) * Complex.I)) (μ * cpowChar αm hαm (-((τ : ℂ) * Complex.I)))
        (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) _ _ hB1 hB2 (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T1 T2 T3 T4 T5 T6 T7
    have CA := shift_continuation L (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) hare φf Oφ Eφ Nφ hEφ
    have CB := shift_continuation L (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) hare (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T9
    have u1 := isUnitaryChar_mul_cpowChar L hαm μ hμ (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) hare
    have u2 := isUnitaryChar_mul_cpowChar L hαm ν hν (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) hnare
    have F1 := isIdeleClassChar_mul_cpowChar L hαm μ hμF (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))
    have F2 := isIdeleClassChar_mul_cpowChar L hαm ν hνF (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I)))
    have k1 := continuous_mul_cpowChar_val L hαm μ hμk (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))
    have k2 := continuous_mul_cpowChar_val L hαm ν hνk (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I)))

    have hoff : ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        (μ * cpowChar αm hαm (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) z ≠ (ν * cpowChar αm hαm (-(-((((τ / 2 : ℝ) : ℂ)) * Complex.I)))) z := by
      by_contra hcon
      push Not at hcon
      have hμν : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z = ν z := by
        intro z hz
        have h := hcon z hz
        rwa [MonoidHom.mul_apply, MonoidHom.mul_apply, cpowChar_eq_one_of_mem_normOneIdeles L hαm _ hz,
          cpowChar_eq_one_of_mem_normOneIdeles L hαm _ hz, mul_one, mul_one] at h
      have hμall := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D σ.symm μ (fun z hz => by
        rw [hC1 z, cpowChar_eq_one_of_mem_normOneIdeles L hαm _ hz, mul_one]; exact (hμν z hz).symm)
      have hνall := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D σ.symm ν (fun z hz => by
        rw [hC2 z, cpowChar_eq_one_of_mem_normOneIdeles L hαm _ hz, mul_one]; exact hμν z hz)
      obtain ⟨z, hz⟩ := hninv
      rcases hz with h | h
      · exact h (hμall z)
      · exact h (hνall z)
    have ht' : t + τ / 2 ≠ 0 := fun h => h2t (by linarith)
    have H := (HMS _ _ _ _ u1 u2 u2 u1 F1 F2 F2 F1 k1 k2 k2 k1
      (fun s g => φf (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) g) A1 A2 A3 A4 A5 A6 A7
      (fun s g => ψf (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) B1 B2 B3 B4 B5 B6 B7
      {s : ℂ | s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) ∈ Oφ} (fun s g => Eφ (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) g) (fun s g => Nφ (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) g) CA
      {s : ℂ | s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) ∈ Oψ} (fun s g => Eψ (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ (s + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) CB
      (t + τ / 2) R hR).2.2.2.1 rfl rfl hoff ht'
    have hc : (((t + τ / 2 : ℝ)) : ℂ) * Complex.I + (-((((τ / 2 : ℝ) : ℂ)) * Complex.I)) = (t : ℂ) * Complex.I := by push_cast; ring
    have e1 : 2 * Complex.I * (R : ℂ) * (((t + τ / 2 : ℝ)) : ℂ) = Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τ : ℂ)) := by push_cast; ring
    have e2 : 2 * Complex.I * (((t + τ / 2 : ℝ)) : ℂ) = Complex.I * (2 * (t : ℂ) + (τ : ℂ)) := by push_cast; ring
    simp only [hc, e1, e2] at H
    simp only []
    exact H

end S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat (solution)
