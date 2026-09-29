-- Prove2me | solution 1 for AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/09a4b9f1-b6d6-528c-922c-aa42dfbf34d2

import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField

namespace AutomorphicForm
p2m_export "AutomorphicForm" "centralCell ellipticCell AdelicGL2 globalPoints centralScalar sigmaAdelicAct_one finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport"
namespace KSideFiniteness
p2m_open "AutomorphicForm"

variable {K : Type} [Field K]

theorem conj_mem_ellipticCell {γ : GL (Fin 2) K} (hγ : γ ∈ ellipticCell K) (h : GL (Fin 2) K) :
    h⁻¹ * γ * h ∈ ellipticCell K := by
  intro a
  have hc : ((h⁻¹ * γ * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' h γ
  rw [hc]
  exact hγ a

theorem conj_mem_centralCell {γ : GL (Fin 2) K} (hγ : γ ∈ centralCell K) (h : GL (Fin 2) K) :
    h⁻¹ * γ * h ∈ centralCell K := by
  obtain ⟨c, hc⟩ := hγ
  refine ⟨c, ?_⟩
  rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem conj_mem_union {γ : GL (Fin 2) K} (hγ : γ ∈ centralCell K ∪ ellipticCell K)
    (h : GL (Fin 2) K) : h⁻¹ * γ * h ∈ centralCell K ∪ ellipticCell K := by
  rcases hγ with hγ | hγ
  · exact Or.inl (conj_mem_centralCell hγ h)
  · exact Or.inr (conj_mem_ellipticCell hγ h)

theorem mem_union_of_isConj {γ δ : GL (Fin 2) K} (hγ : γ ∈ centralCell K ∪ ellipticCell K)
    (h : IsConj γ δ) : δ ∈ centralCell K ∪ ellipticCell K := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have : δ = c⁻¹⁻¹ * γ * c⁻¹ := by rw [inv_inv, hc]
  rw [this]
  exact conj_mem_union hγ c⁻¹

section Trivial

scoped instance subsingleton_algEquiv_self : Subsingleton (K ≃ₐ[K] K) :=
  ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩

theorem hgen_one : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K) := fun τ => by
  rw [Subsingleton.elim τ 1]; exact Subgroup.one_mem _

theorem map_one_algEquiv (h : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) h = h := by
  ext i j; rfl

theorem sigmaNormPow_finrank_self (δ : GL (Fin 2) K) :
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K))
      (Module.finrank K K) δ = δ := by
  rw [Module.finrank_self, LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_one]

theorem map_algebraMap_self (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (algebraMap K K) γ = γ := by
  ext i j; rfl

theorem normClassMap_one_mk (δ : GL (Fin 2) K) :
    LT.TwistedNorm.normClassMap (hgen_one (K := K)) (LT.TwistedNorm.SigmaConjClasses.mk 1 δ) =
      ConjClasses.mk δ := by
  refine LT.TwistedNorm.normClassMap_mk_eq_of_isNormRep _ ⟨1, ?_⟩
  rw [sigmaNormPow_finrank_self, map_algebraMap_self, inv_one, one_mul, mul_one]

theorem mem_setOf_iff (δ : GL (Fin 2) K) :
    δ ∈ {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K,
        (γ ∈ ellipticCell K ∨ γ ∈ centralCell K) ∧
        LT.TwistedNorm.normClassMap (hgen_one (K := K)) (LT.TwistedNorm.SigmaConjClasses.mk 1 δ) =
          ConjClasses.mk γ} ↔ δ ∈ centralCell K ∪ ellipticCell K := by
  constructor
  · rintro ⟨γ, hγ, hN⟩
    rw [normClassMap_one_mk, ConjClasses.mk_eq_mk_iff_isConj] at hN
    exact mem_union_of_isConj (Or.symm hγ) hN.symm
  · intro hδ
    exact ⟨δ, Or.symm hδ, normClassMap_one_mk δ⟩

end Trivial

end AutomorphicForm.KSideFiniteness
p2m_reactivate "P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport.AutomorphicForm P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport.AutomorphicForm.KSideFiniteness"
p2m_reactivate "P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport.AutomorphicForm"

open AutomorphicForm.KSideFiniteness in
theorem solution
    (K : Type) [Field K] [NumberField K]
    {E : Type*} [Zero E]
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → E) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) K))
    (hRsub : R ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ R ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ),
        γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    {γ₀ ∈ R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ≠ 0}.Finite := by
  classical

  set φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ := (Function.support f).indicator fun _ => 1 with hφ
  have hφc : HasCompactSupport φ := by
    refine hfc.mono ?_
    intro g hg
    by_contra h
    exact hg (Set.indicator_of_notMem h _)
  have hφne : ∀ g, φ g ≠ 0 ↔ f g ≠ 0 := by
    intro g
    rw [hφ]
    by_cases h : g ∈ Function.support f
    · rw [Set.indicator_of_mem h]; exact ⟨fun _ => h, fun _ => one_ne_zero⟩
    · rw [Set.indicator_of_notMem h]; exact ⟨fun h0 => absurd rfl h0, fun h1 => absurd h1 h⟩
  have hfin := AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
    K K 1 hgen_one (M4aHerbrand.identityDescent (𝓞 K) K K) φ hφc R
    (fun δ hδ => (mem_setOf_iff δ).mpr (hRsub hδ))
    (fun δ hδ => by
      simp only [map_one_algEquiv]
      exact hR δ ((mem_setOf_iff δ).mp hδ))
  rw [AutomorphicForm.sigmaAdelicAct_one] at hfin
  refine hfin.subset ?_
  rintro γ₀ ⟨hγ₀, x, z, hne⟩
  exact ⟨hγ₀, x, z, (hφne _).mpr hne⟩

end S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport (solution)
