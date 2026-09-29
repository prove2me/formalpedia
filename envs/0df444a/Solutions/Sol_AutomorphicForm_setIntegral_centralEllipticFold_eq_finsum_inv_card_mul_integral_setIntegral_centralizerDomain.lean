-- Prove2me | solution 1 for AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0104f063-1049-56fd-b333-61682fc498c9

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_TwistedNormClasses
import Mathlib.Tactic.Group
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open Polynomial
open Function Set
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace GeoEllUnfolding

section Cells

variable {K : Type*} [Field K]

private theorem coe_scalar (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 2) (a : K) :=
  rfl

private theorem scalar_mem_center (a : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalar]
  exact (Matrix.scalar_commute (a : K) (fun _ => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) K)).eq.symm

private theorem disjoint_centralCell_ellipticCell :
    Disjoint (AutomorphicForm.centralCell K) (AutomorphicForm.ellipticCell K) := by
  rw [Set.disjoint_left]
  rintro γ ⟨c, hc⟩ hell
  refine hell c ?_
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly, hc, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply,
    sub_self]
  exact Matrix.det_zero

private theorem scalar_mem_centralCell (a : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ AutomorphicForm.centralCell K :=
  ⟨(a : K), by rw [coe_scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]⟩

private theorem coe_scalar_mul_conj (a : Kˣ) (γ h : GL (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ * h) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (a : K) • ((h⁻¹ : GL (Fin 2) K).val * (γ : Matrix (Fin 2) (Fin 2) K) * (h : GL (Fin 2) K).val) := by
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

private theorem conj_scalar (c : K) (h : GL (Fin 2) K) :
    (h⁻¹ : GL (Fin 2) K).val * Matrix.scalar (Fin 2) c * (h : GL (Fin 2) K).val = Matrix.scalar (Fin 2) c := by
  rw [mul_assoc, (Matrix.scalar_commute c (fun _ => Commute.all _ _) (h : GL (Fin 2) K).val).eq, ← mul_assoc,
    Units.inv_mul, one_mul]

private theorem scalar_mul_conj_mem_centralCell {γ : GL (Fin 2) K} (hγ : γ ∈ AutomorphicForm.centralCell K)
    (a : Kˣ) (h : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ * h) ∈ AutomorphicForm.centralCell K := by
  obtain ⟨c, hc⟩ := hγ
  refine ⟨(a : K) * c, ?_⟩
  rw [coe_scalar_mul_conj, hc, Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, conj_scalar,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_smul]

private theorem scalar_mul_conj_mem_ellipticCell {γ : GL (Fin 2) K} (hγ : γ ∈ AutomorphicForm.ellipticCell K)
    (a : Kˣ) (h : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ * h) ∈ AutomorphicForm.ellipticCell K := by
  intro b hb
  set N : Matrix (Fin 2) (Fin 2) K :=
    (h⁻¹ : GL (Fin 2) K).val * (γ : Matrix (Fin 2) (Fin 2) K) * (h : GL (Fin 2) K).val with hN
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly, coe_scalar_mul_conj] at hb
  have hsc : Matrix.scalar (Fin 2) b - (a : K) • N = (a : K) • (Matrix.scalar (Fin 2) ((a : K)⁻¹ * b) - N) := by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    funext _
    rw [Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ (Units.ne_zero a)]
  rw [hsc, Matrix.det_smul, mul_eq_zero] at hb
  rcases hb with hb | hb
  · exact pow_ne_zero _ (Units.ne_zero a) hb

  have hconj : Matrix.scalar (Fin 2) ((a : K)⁻¹ * b) - N =
      (h⁻¹ : GL (Fin 2) K).val * (Matrix.scalar (Fin 2) ((a : K)⁻¹ * b) - (γ : Matrix (Fin 2) (Fin 2) K)) *
        (h : GL (Fin 2) K).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, conj_scalar]
  rw [hconj, Matrix.det_units_conj'] at hb
  exact hγ ((a : K)⁻¹ * b) (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hb)

private theorem finite_scalarStab (γ₀ : GL (Fin 2) K) :
    {a : Kˣ | ∃ h : GL (Fin 2) K, Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h}.Finite := by
  refine (Set.toFinite ({1, -1} : Set Kˣ)).subset ?_
  rintro a ⟨h, hh⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hh
  simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have h1 : (Matrix.GeneralLinearGroup.det h)⁻¹ * Matrix.GeneralLinearGroup.det γ₀ *
      Matrix.GeneralLinearGroup.det h = Matrix.GeneralLinearGroup.det γ₀ := by
    rw [mul_comm _ (Matrix.GeneralLinearGroup.det γ₀), mul_assoc, inv_mul_cancel, mul_one]
  rw [h1] at hdet
  have h2 : a ^ 2 = 1 := mul_right_cancel (hdet.trans (one_mul _).symm)
  have h3 : (a : K) * (a : K) = 1 := by
    have := congrArg Units.val h2
    simpa [sq] using this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_self_eq_one_iff.mp h3 with h4 | h4
  · exact Or.inl (Units.ext h4)
  · exact Or.inr (Units.ext (by simpa using h4))

end Cells

section Fibration

variable {G A : Type*} [Group G] [CommGroup A] (sc : A →* G) (γ₀ : G)

private def conjOrbit : Set G := {γ' | ∃ h : G, γ' = h⁻¹ * γ₀ * h}

private def scalarFamily : Set G := {γ | ∃ (h : G) (a : A), γ = sc a * (h⁻¹ * γ₀ * h)}

private def scalarStab : Set A := {a | ∃ h : G, sc a * γ₀ = h⁻¹ * γ₀ * h}

private def scalarFibre (γ : G) : Set (A × G) := {p | p.2 ∈ conjOrbit γ₀ ∧ sc p.1 * p.2 = γ}

variable {sc γ₀}

private theorem one_mem_scalarStab : (1 : A) ∈ scalarStab sc γ₀ := ⟨1, by simp⟩

section central

variable (hsc : ∀ a : A, sc a ∈ Subgroup.center G)
include hsc

private theorem sc_mul_comm (a : A) (g : G) : sc a * g = g * sc a :=
  ((Subgroup.mem_center_iff.mp (hsc a)) g).symm

private theorem conj_sc_mul' (b : A) (h X : G) : h * (sc b * X) * h⁻¹ = sc b * (h * X * h⁻¹) := by
  rw [← mul_assoc, ← sc_mul_comm hsc b h]
  group

private theorem conj_sc_mul (a : A) (h : G) : h⁻¹ * (sc a * γ₀) * h = sc a * (h⁻¹ * γ₀ * h) := by
  have := conj_sc_mul' hsc a h⁻¹ γ₀
  rwa [inv_inv] at this

private theorem inv_mem_scalarStab {b : A} (hb : b ∈ scalarStab sc γ₀) : b⁻¹ ∈ scalarStab sc γ₀ := by
  obtain ⟨k, hk⟩ := hb
  refine ⟨k⁻¹, ?_⟩
  have h2 : sc b * (k * γ₀ * k⁻¹) = γ₀ := by
    have := conj_sc_mul hsc (γ₀ := γ₀) b k⁻¹
    rw [inv_inv, hk] at this
    rw [← this]
    group
  rw [inv_inv]
  calc sc b⁻¹ * γ₀ = sc b⁻¹ * (sc b * (k * γ₀ * k⁻¹)) := by rw [h2]
    _ = k * γ₀ * k⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem sc_mul_mem_orbit {b : A} (hb : b ∈ scalarStab sc γ₀) {γ' : G} (hγ' : γ' ∈ conjOrbit γ₀) :
    sc b * γ' ∈ conjOrbit γ₀ := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨h, rfl⟩ := hγ'
  refine ⟨k * h, ?_⟩
  rw [← conj_sc_mul hsc, hk]
  group

private noncomputable def fibreEquiv (a₀ : A) {γ₀' : G} (hγ₀' : γ₀' ∈ conjOrbit γ₀) :
    scalarStab sc γ₀ ≃ scalarFibre sc γ₀ (sc a₀ * γ₀') where
  toFun b := ⟨(a₀ * (b : A)⁻¹, sc b * γ₀'), sc_mul_mem_orbit hsc b.2 hγ₀', by
    rw [← mul_assoc, ← map_mul, mul_assoc a₀, inv_mul_cancel, mul_one]⟩
  invFun p := ⟨(p : A × G).1⁻¹ * a₀, by
    obtain ⟨⟨a, γ'⟩, hγ', hp⟩ := p
    obtain ⟨h, hh⟩ := hγ'
    obtain ⟨h₀, hh₀⟩ := hγ₀'
    refine ⟨h * h₀⁻¹, ?_⟩
    have h2 : sc (a⁻¹ * a₀) * γ₀' = γ' := by
      rw [map_mul, mul_assoc, ← hp, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    calc sc (a⁻¹ * a₀) * γ₀
        = sc (a⁻¹ * a₀) * (h₀ * γ₀' * h₀⁻¹) := by rw [hh₀]; group
      _ = h₀ * (sc (a⁻¹ * a₀) * γ₀') * h₀⁻¹ := (conj_sc_mul' hsc _ _ _).symm
      _ = h₀ * γ' * h₀⁻¹ := by rw [h2]
      _ = (h * h₀⁻¹)⁻¹ * γ₀ * (h * h₀⁻¹) := by rw [show γ' = h⁻¹ * γ₀ * h from hh]; group⟩
  left_inv b := Subtype.ext (by simp [mul_assoc])
  right_inv p := by
    obtain ⟨⟨a, γ'⟩, hγ', hp⟩ := p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simp
    · show sc (a⁻¹ * a₀) * γ₀' = γ'
      rw [map_mul, mul_assoc, ← hp, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem card_fibre (a₀ : A) {γ₀' : G} (hγ₀' : γ₀' ∈ conjOrbit γ₀) :
    Nat.card (scalarFibre sc γ₀ (sc a₀ * γ₀')) = Nat.card (scalarStab sc γ₀) :=
  (Nat.card_congr (fibreEquiv hsc a₀ hγ₀')).symm

private theorem finsum_mem_family_eq_inv_card_mul [Finite (scalarStab sc γ₀)] (u : G → ℂ)
    (hu : (scalarFamily sc γ₀ ∩ support u).Finite) :
    ∑ᶠ γ ∈ scalarFamily sc γ₀, u γ =
      ((Nat.card (scalarStab sc γ₀) : ℕ) : ℂ)⁻¹ *
        ∑ᶠ p ∈ (univ : Set A) ×ˢ conjOrbit γ₀, u (sc p.1 * p.2) := by
  classical
  have hcard : ((Nat.card (scalarStab sc γ₀) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (scalarStab sc γ₀) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, one_mem_scalarStab⟩⟩, inferInstance⟩
    exact_mod_cast this.ne'

  have hIfin : (scalarFamily sc γ₀ ∩ support u).Finite := hu
  have hfib_fin : ∀ γ ∈ scalarFamily sc γ₀ ∩ support u, (scalarFibre sc γ₀ γ).Finite := by
    intro γ hγ
    obtain ⟨h, a, rfl⟩ := hγ.1
    have : Finite (scalarFibre sc γ₀ (sc a * (h⁻¹ * γ₀ * h))) :=
      Finite.of_equiv _ (fibreEquiv hsc a ⟨h, rfl⟩)
    exact Set.toFinite _
  have hdisj : (scalarFamily sc γ₀ ∩ support u).PairwiseDisjoint (scalarFibre sc γ₀) := by
    intro γ _ γ' _ hne
    refine Set.disjoint_left.mpr fun p hp hp' => hne ?_
    exact hp.2.symm.trans hp'.2

  have hset : ((univ : Set A) ×ˢ conjOrbit γ₀) ∩ support (fun p : A × G => u (sc p.1 * p.2)) =
      ⋃ γ ∈ scalarFamily sc γ₀ ∩ support u, scalarFibre sc γ₀ γ := by
    ext ⟨a, γ'⟩
    constructor
    · rintro ⟨⟨-, hγ'⟩, hsupp⟩
      obtain ⟨h, rfl⟩ := hγ'
      exact Set.mem_biUnion (x := sc a * (h⁻¹ * γ₀ * h)) ⟨⟨h, a, rfl⟩, hsupp⟩ ⟨⟨h, rfl⟩, rfl⟩
    · intro hp
      obtain ⟨γ, hγ, hpγ⟩ := Set.mem_iUnion₂.mp hp
      refine ⟨⟨Set.mem_univ _, hpγ.1⟩, ?_⟩
      show u (sc a * γ') ≠ 0
      rw [hpγ.2]
      exact hγ.2
  have hpair : ∑ᶠ p ∈ (univ : Set A) ×ˢ conjOrbit γ₀, u (sc p.1 * p.2) =
      ∑ᶠ γ ∈ scalarFamily sc γ₀ ∩ support u, ∑ᶠ p ∈ scalarFibre sc γ₀ γ, u (sc p.1 * p.2) := by
    rw [← finsum_mem_inter_support, hset, finsum_mem_biUnion hdisj hIfin hfib_fin]

  have hconst : ∀ γ ∈ scalarFamily sc γ₀ ∩ support u,
      ∑ᶠ p ∈ scalarFibre sc γ₀ γ, u (sc p.1 * p.2) = ((Nat.card (scalarStab sc γ₀) : ℕ) : ℂ) * u γ := by
    intro γ hγ
    have hf : (scalarFibre sc γ₀ γ).Finite := hfib_fin γ hγ
    have hf' : (scalarFibre sc γ₀ γ ∩ support (fun _ : A × G => u γ)).Finite := hf.inter_of_left _
    have hne : u γ ≠ 0 := hγ.2
    have hsupp : scalarFibre sc γ₀ γ ∩ support (fun _ : A × G => u γ) = scalarFibre sc γ₀ γ := by
      ext p
      exact ⟨fun hp => hp.1, fun hp => ⟨hp, hne⟩⟩
    rw [finsum_mem_congr rfl (fun p hp => by rw [hp.2]), finsum_mem_eq_sum _ hf', Finset.sum_const,
      nsmul_eq_mul]
    congr 2
    rw [← Set.ncard_eq_toFinset_card _ hf', hsupp, ← Nat.card_coe_set_eq]
    obtain ⟨h, a, rfl⟩ := hγ.1
    exact card_fibre hsc a ⟨h, rfl⟩
  rw [hpair, finsum_mem_congr rfl hconst, ← mul_finsum_mem u ((Nat.card (scalarStab sc γ₀) : ℕ) : ℂ),
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul, finsum_mem_inter_support]

private theorem finsum_mem_family_eq_inv_card_mul_finsum_finsum [Finite (scalarStab sc γ₀)] (u : G → ℂ)
    (hu : (scalarFamily sc γ₀ ∩ support u).Finite) :
    ∑ᶠ γ ∈ scalarFamily sc γ₀, u γ =
      ((Nat.card (scalarStab sc γ₀) : ℕ) : ℂ)⁻¹ *
        ∑ᶠ (a : A) (γ' : G) (_ : γ' ∈ conjOrbit γ₀), u (sc a * γ') := by
  rw [finsum_mem_family_eq_inv_card_mul hsc u hu]
  congr 1

  have hfin : HasFiniteSupport (((univ : Set A) ×ˢ conjOrbit γ₀).indicator fun p : A × G => u (sc p.1 * p.2)) := by
    have hsub : support (((univ : Set A) ×ˢ conjOrbit γ₀).indicator fun p : A × G => u (sc p.1 * p.2)) ⊆
        ⋃ γ ∈ scalarFamily sc γ₀ ∩ support u, scalarFibre sc γ₀ γ := by
      intro p hp
      rw [Function.mem_support, Set.indicator_apply_ne_zero] at hp
      obtain ⟨⟨-, hγ'⟩, hsupp⟩ := hp
      obtain ⟨h, hh⟩ := hγ'
      exact Set.mem_biUnion (x := sc p.1 * p.2) ⟨⟨h, p.1, by rw [hh]⟩, hsupp⟩ ⟨⟨h, hh⟩, rfl⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion hu fun γ hγ => ?_
    obtain ⟨h, a, rfl⟩ := hγ.1
    have : Finite (scalarFibre sc γ₀ (sc a * (h⁻¹ * γ₀ * h))) :=
      Finite.of_equiv _ (fibreEquiv hsc a ⟨h, rfl⟩)
    exact Set.toFinite _
  rw [finsum_mem_def, finsum_curry _ hfin]
  refine finsum_congr fun a => ?_
  rw [finsum_mem_def]
  refine finsum_congr fun γ' => ?_
  by_cases hγ' : γ' ∈ conjOrbit γ₀
  · rw [Set.indicator_of_mem (Set.mk_mem_prod (Set.mem_univ a) hγ'), Set.indicator_of_mem hγ']
  · rw [Set.indicator_of_notMem (fun hp => hγ' (Set.mem_prod.mp hp).2), Set.indicator_of_notMem hγ']

omit hsc in

private theorem finsum_mem_biUnion_of_finite_support {ι : Type*} {I : Set ι} {t : ι → Set G} (u : G → ℂ)
    (hdisj : I.PairwiseDisjoint t) (hfin : ((⋃ i ∈ I, t i) ∩ support u).Finite) :
    ∑ᶠ γ ∈ ⋃ i ∈ I, t i, u γ = ∑ᶠ i ∈ I, ∑ᶠ γ ∈ t i, u γ := by
  classical

  set J : Set ι := {i ∈ I | (t i ∩ support u).Nonempty} with hJ
  have hJI : J ⊆ I := fun i hi => hi.1

  have hJfin : J.Finite := by
    have hinj : ∀ i ∈ J, ∀ j ∈ J, ∀ γ, γ ∈ t i → γ ∈ t j → i = j := by
      intro i hi j hj γ hγi hγj
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hi.1 hj.1 hne) hγi hγj
    choose! pt hpt using fun i (hi : i ∈ J) => hi.2
    refine Set.Finite.of_finite_image (f := pt) (hfin.subset ?_) ?_
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨Set.mem_iUnion₂.mpr ⟨i, hi.1, (hpt i hi).1⟩, (hpt i hi).2⟩
    · intro i hi j hj hij
      exact hinj i hi j hj (pt i) (hpt i hi).1 (hij ▸ (hpt j hj).1)
  have hpiece : ∀ i ∈ J, (t i ∩ support u).Finite := fun i hi =>
    hfin.subset (Set.inter_subset_inter_left _ (Set.subset_biUnion_of_mem hi.1))
  have hdisjJ : J.PairwiseDisjoint fun i => t i ∩ support u := fun i hi j hj hne =>
    (hdisj hi.1 hj.1 hne).mono Set.inter_subset_left Set.inter_subset_left

  have hcut : (⋃ i ∈ I, t i) ∩ support u = ⋃ i ∈ J, (t i ∩ support u) := by
    ext γ
    constructor
    · rintro ⟨hγ, hsupp⟩
      obtain ⟨i, hi, hγi⟩ := Set.mem_iUnion₂.mp hγ
      exact Set.mem_iUnion₂.mpr ⟨i, ⟨hi, ⟨γ, hγi, hsupp⟩⟩, hγi, hsupp⟩
    · intro hγ
      obtain ⟨i, hi, hγi, hsupp⟩ := Set.mem_iUnion₂.mp hγ
      exact ⟨Set.mem_iUnion₂.mpr ⟨i, hi.1, hγi⟩, hsupp⟩
  rw [← finsum_mem_inter_support, hcut, finsum_mem_biUnion hdisjJ hJfin hpiece]

  have houter : ∀ i ∈ I, i ∉ J → ∑ᶠ γ ∈ t i, u γ = 0 := by
    intro i hi hiJ
    rw [← finsum_mem_inter_support]
    have : t i ∩ support u = ∅ := by
      by_contra hne
      exact hiJ ⟨hi, Set.nonempty_iff_ne_empty.mpr hne⟩
    rw [this, finsum_mem_empty]
  calc ∑ᶠ i ∈ J, ∑ᶠ γ ∈ t i ∩ support u, u γ
      = ∑ᶠ i ∈ J, ∑ᶠ γ ∈ t i, u γ := finsum_mem_congr rfl fun i _ => finsum_mem_inter_support _ _
    _ = ∑ᶠ i ∈ I, ∑ᶠ γ ∈ t i, u γ := by
      rw [← finsum_mem_inter_support (s := J), ← finsum_mem_inter_support (s := I)]
      refine finsum_mem_congr ?_ fun _ _ => rfl
      ext i
      refine ⟨fun hi => ⟨hJI hi.1, hi.2⟩, fun hi => ⟨?_, hi.2⟩⟩
      by_contra hiJ
      exact hi.2 (houter i hi.1 hiJ)

end central

end Fibration

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem coe_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 F) F z : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) :=
  rfl

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.centralScalar (𝓞 F) F z * g = g * AutomorphicForm.centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_centralScalar]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _)
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).eq

private theorem inv_mul_mul_centralScalar_mul (x g : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    x⁻¹ * g * (AutomorphicForm.centralScalar (𝓞 F) F z * x) =
      x⁻¹ * g * x * AutomorphicForm.centralScalar (𝓞 F) F z := by
  rw [centralScalar_mul_comm, ← mul_assoc]

private theorem globalPoints_scalar (a : Fˣ) :
    AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      AutomorphicForm.centralScalar (𝓞 F) F
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]
  · simp [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

private def normBand (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private theorem globalPoints_mul_mem_band {α β : ℝ} (γ : GL (Fin 2) F) {x : AutomorphicForm.AdelicGL2 (𝓞 F) F}
    (hx : x ∈ normBand F α β) : AutomorphicForm.globalPoints (𝓞 F) F γ * x ∈ normBand F α β := by
  simp only [normBand, Set.mem_setOf_eq, map_mul] at hx ⊢
  rwa [NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

private theorem finite_support_kernel_summand (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (Function.support fun γ : GL (Fin 2) F =>
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y)).Finite :=
  (AutomorphicForm.adelicKernelLocalFiniteness F (tsupport f) hfc x y).subset fun _ hγ =>
    subset_tsupport f hγ

private theorem centralPart_add_ellipticPart (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.adelicKernelCentralPart F f x y + AutomorphicForm.adelicKernelEllipticPart F f x y =
      ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y) := by
  unfold AutomorphicForm.adelicKernelCentralPart AutomorphicForm.adelicKernelEllipticPart
  have hfin := finite_support_kernel_summand F f hfc x y
  rw [finsum_mem_union' disjoint_centralCell_ellipticCell (hfin.subset Set.inter_subset_right)
    (hfin.subset Set.inter_subset_right)]

section instances

private theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
  borelSpace_glBorel (Fin 2) (𝓞 F) F

private theorem isHaarMeasure_adelicGL2 : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

private theorem measurableConstSMul_globalPoints :
    MeasurableConstSMul (AutomorphicForm.globalPoints (𝓞 F) F).range (AutomorphicForm.AdelicGL2 (𝓞 F) F) := by
  haveI := borelSpace_adelicGL2 F
  exact ⟨fun g => measurable_const_mul (g : AutomorphicForm.AdelicGL2 (𝓞 F) F)⟩

private theorem smulInvariantMeasure_band_globalPoints (α β : ℝ) :
    SMulInvariantMeasure (AutomorphicForm.globalPoints (𝓞 F) F).range (AutomorphicForm.AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
  haveI := borelSpace_adelicGL2 F
  haveI := isHaarMeasure_adelicGL2 F
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨γ, hγ⟩ := g.2
  have hsmul : (fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F => g • x) =
      fun x => (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) * x := by
    funext x
    rfl
  have hpre : (fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F => (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) * x) ⁻¹' s ∩
      normBand F α β =
      (fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F => (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) * x) ⁻¹'
        (s ∩ normBand F α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxs, hxb⟩
      refine ⟨hxs, ?_⟩
      rw [← hγ]
      exact globalPoints_mul_mem_band F γ hxb
    · rintro ⟨hxs, hxb⟩
      refine ⟨hxs, ?_⟩
      have := globalPoints_mul_mem_band F γ⁻¹ hxb
      rwa [map_inv, hγ, ← mul_assoc, inv_mul_cancel, one_mul] at this
  rw [hsmul, Measure.restrict_apply (measurable_const_mul (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) hs), hpre,
    measure_preimage_mul, Measure.restrict_apply hs]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

private theorem measurableConstSMul_principal :
    MeasurableConstSMul
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range (AdeleRing (𝓞 F) F)ˣ :=
  ⟨fun g => measurable_const_mul (g : (AdeleRing (𝓞 F) F)ˣ)⟩

private theorem smulInvariantMeasure_principal (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] :
    SMulInvariantMeasure
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range (AdeleRing (𝓞 F) F)ˣ νZ :=
  ⟨fun g s _ => measure_preimage_mul νZ (g : (AdeleRing (𝓞 F) F)ˣ) s⟩

end instances

end Adelic

section Regroup

variable (F : Type) [Field F] [NumberField F]

private noncomputable def stabCard (γ₀ : GL (Fin 2) F) : ℂ :=
  ((Nat.card {a : Fˣ // ∃ h : GL (Fin 2) F,
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)

private noncomputable def orbitSum (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (γ₀ : GL (Fin 2) F)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (w : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ∑ᶠ γ' ∈ conjOrbit γ₀,
    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' * (AutomorphicForm.centralScalar (𝓞 F) F w * x))

private noncomputable def princ (a : Fˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a

variable {F}

private theorem kernelSummand_scalar_mul (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (a : Fˣ) (γ' : GL (Fin 2) F)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) =
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
        (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z) * x)) := by
  rw [map_mul, globalPoints_scalar, centralScalar_mul_comm, map_mul]
  simp only [princ, mul_assoc]

omit [NumberField F] in

private theorem cells_eq_biUnion_family (R : Set (GL (Fin 2) F))
    (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F =
      ⋃ γ₀ ∈ R, scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀ := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨γ₀, ⟨hγ₀R, h, a, rfl⟩, -⟩ := hR γ hγ
    exact Set.mem_biUnion hγ₀R ⟨h, a, rfl⟩
  · intro hγ
    obtain ⟨γ₀, hγ₀R, h, a, rfl⟩ := Set.mem_iUnion₂.mp hγ
    rcases hRsub hγ₀R with hc | he
    · exact Or.inl (scalar_mul_conj_mem_centralCell hc a h)
    · exact Or.inr (scalar_mul_conj_mem_ellipticCell he a h)

omit [NumberField F] in

private theorem pairwiseDisjoint_family (R : Set (GL (Fin 2) F))
    (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    R.PairwiseDisjoint (scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2))) := by
  intro γ₁ hγ₁ γ₂ hγ₂ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro γ ⟨h₁, a₁, rfl⟩ ⟨h₂, a₂, hγ⟩
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) a₁ * (h₁⁻¹ * γ₁ * h₁) ∈
      AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F := by
    rcases hRsub hγ₁ with hc | he
    · exact Or.inl (scalar_mul_conj_mem_centralCell hc a₁ h₁)
    · exact Or.inr (scalar_mul_conj_mem_ellipticCell he a₁ h₁)
  obtain ⟨γ₀, -, huniq⟩ := hR _ hmem
  exact hne ((huniq γ₁ ⟨hγ₁, h₁, a₁, rfl⟩).trans (huniq γ₂ ⟨hγ₂, h₂, a₂, hγ⟩).symm)

private theorem kernelParts_eq_finsum_families (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    AutomorphicForm.adelicKernelCentralPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x) +
        AutomorphicForm.adelicKernelEllipticPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x) =
      ∑ᶠ γ₀ ∈ R, (stabCard F γ₀)⁻¹ * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) := by
  classical
  have hTfin := finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)
  rw [centralPart_add_ellipticPart F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x),
    cells_eq_biUnion_family R hRsub hR,
    finsum_mem_biUnion_of_finite_support _ (pairwiseDisjoint_family R hRsub hR)
      (hTfin.subset Set.inter_subset_right)]
  refine finsum_mem_congr rfl fun γ₀ _ => ?_
  haveI : Finite (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) := (finite_scalarStab γ₀).to_subtype
  rw [finsum_mem_family_eq_inv_card_mul_finsum_finsum (fun a => scalar_mem_center a) _
    (hTfin.subset Set.inter_subset_right)]
  have hcard : stabCard F γ₀ =
      ((Nat.card (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) : ℕ) : ℂ) := rfl
  rw [hcard]
  congr 1
  refine finsum_congr fun a => ?_
  unfold orbitSum
  exact finsum_mem_congr rfl fun γ' _ => kernelSummand_scalar_mul f a γ' x z

end Regroup

section GenericUnfolding

variable {G X E : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable G]
  [MeasurableConstSMul G X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [SMulInvariantMeasure G X μ] {Φ : Set X}

private theorem integral_eq_setIntegral_tsum_smul (hΦ : IsFundamentalDomain G Φ μ) (F : X → E)
    (hF : Integrable F μ) :
    ∫ x, F x ∂μ = ∫ x in Φ, ∑' g : G, F (g • x) ∂μ := by
  have h1 : ∫ x, F x ∂μ = ∑' g : G, ∫ x in Φ, F (g⁻¹ • x) ∂μ := hΦ.integral_eq_tsum' F hF
  have h2 := (Equiv.inv G).tsum_eq (fun g : G => ∫ x in Φ, F (g • x) ∂μ)
  simp only [Equiv.inv_apply] at h2
  have hmeas : ∀ g : G, AEStronglyMeasurable (fun x => F (g • x)) (μ.restrict Φ) := fun g =>
    (hF.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul g μ)).restrict
  have hsum : (∑' g : G, ∫⁻ x in Φ, ‖F (g • x)‖ₑ ∂μ) ≠ ⊤ := by
    have h3 : ∫⁻ x, ‖F x‖ₑ ∂μ = ∑' g : G, ∫⁻ x in Φ, ‖F (g⁻¹ • x)‖ₑ ∂μ :=
      hΦ.lintegral_eq_tsum' (fun x => ‖F x‖ₑ)
    have h4 := (Equiv.inv G).tsum_eq (fun g : G => ∫⁻ x in Φ, ‖F (g • x)‖ₑ ∂μ)
    simp only [Equiv.inv_apply] at h4
    rw [← h4, ← h3]
    exact hF.hasFiniteIntegral.ne
  rw [h1, h2, integral_tsum hmeas hsum]

variable (H : Subgroup G)

private theorem ae_forall_existsUnique_smul_mem {Ψ : Set X} (hΨ : IsFundamentalDomain H Ψ μ) :
    ∀ᵐ x ∂μ, ∀ g : G, ∃! h : H, h • (g • x) ∈ Ψ := by

  have hex : ∀ᵐ y ∂μ, ∃ h : H, h • y ∈ Ψ := hΨ.ae_covers

  have huniq : ∀ᵐ y ∂μ, ∀ h h' : H, h • y ∈ Ψ → h' • y ∈ Ψ → h = h' := by
    rw [ae_all_iff]; intro h
    rw [ae_all_iff]; intro h'
    by_cases hne : h = h'
    · exact Filter.Eventually.of_forall (fun _ _ _ => hne)
    · have hd : μ (h⁻¹ • Ψ ∩ h'⁻¹ • Ψ) = 0 := hΨ.aedisjoint (inv_injective.ne hne)
      have hz : ∀ᵐ y ∂μ, y ∉ (h⁻¹ • Ψ ∩ h'⁻¹ • Ψ) := by
        rw [ae_iff]; simpa using hd
      filter_upwards [hz] with y hy hy1 hy2
      exact absurd ⟨Set.mem_inv_smul_set_iff.mpr hy1, Set.mem_inv_smul_set_iff.mpr hy2⟩ hy
  have hone : ∀ᵐ y ∂μ, ∃! h : H, h • y ∈ Ψ := by
    filter_upwards [hex, huniq] with y ⟨h, hh⟩ hu
    exact ⟨h, hh, fun h' hh' => hu h' h hh' hh⟩

  rw [ae_all_iff]
  intro g
  exact (measurePreserving_smul g μ).quasiMeasurePreserving.ae hone

omit [NormedSpace ℝ E] in

private theorem integrableOn_tsum_smul (hΦ : IsFundamentalDomain G Φ μ) (F : X → E) (hF : Integrable F μ)
    (hmeas : AEStronglyMeasurable (fun x => ∑' g : G, F (g • x)) (μ.restrict Φ)) :
    IntegrableOn (fun x => ∑' g : G, F (g • x)) Φ μ := by
  refine ⟨hmeas, ?_⟩
  have hmeas' : ∀ g : G, AEMeasurable (fun x => ‖F (g • x)‖ₑ) (μ.restrict Φ) := fun g =>
    ((hF.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul g μ)).restrict).enorm
  have hsum : ∑' g : G, ∫⁻ x in Φ, ‖F (g • x)‖ₑ ∂μ = ∫⁻ x, ‖F x‖ₑ ∂μ :=
    (hΦ.lintegral_eq_tsum'' (fun x => ‖F x‖ₑ)).symm
  show ∫⁻ x in Φ, ‖∑' g : G, F (g • x)‖ₑ ∂μ < ⊤
  calc ∫⁻ x in Φ, ‖∑' g : G, F (g • x)‖ₑ ∂μ ≤ ∫⁻ x in Φ, ∑' g : G, ‖F (g • x)‖ₑ ∂μ :=
        lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' g : G, ∫⁻ x in Φ, ‖F (g • x)‖ₑ ∂μ := lintegral_tsum hmeas'
    _ = ∫⁻ x, ‖F x‖ₑ ∂μ := hsum
    _ < ⊤ := lt_top_iff_ne_top.mpr hF.hasFiniteIntegral.ne

private theorem isFundamentalDomain_subgroupOf {Y : Type*} [Group Y] [MeasurableSpace Y] {ν : Measure Y}
    {G K : Subgroup Y} (hK : K ≤ G) {Ψ : Set Y} (hΨ : IsFundamentalDomain K Ψ ν) :
    IsFundamentalDomain (K.subgroupOf G) Ψ ν where
  nullMeasurableSet := hΨ.nullMeasurableSet
  ae_covers := hΨ.ae_covers.mono fun x ⟨c, hc⟩ => ⟨⟨⟨(c : Y), hK c.2⟩, c.2⟩, hc⟩
  aedisjoint := by
    intro g g' hne
    have hne' : (⟨((g : G) : Y), g.2⟩ : K) ≠ ⟨((g' : G) : Y), g'.2⟩ := fun h =>
      hne (Subtype.ext (Subtype.ext (congrArg (fun c : K => (c : Y)) h)))
    exact hΨ.aedisjoint hne'

end GenericUnfolding

section FibreFinite

variable {G A : Type*} [Group G] [CommGroup A] {sc : A →* G} {γ₀ : G}
  (hsc : ∀ a : A, sc a ∈ Subgroup.center G)
include hsc

private theorem finite_scalarFibre [Finite (scalarStab sc γ₀)] (γ : G) : (scalarFibre sc γ₀ γ).Finite := by
  by_cases h : ∃ a₀ : A, ∃ γ₀' ∈ conjOrbit γ₀, γ = sc a₀ * γ₀'
  · obtain ⟨a₀, γ₀', hγ₀', rfl⟩ := h
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (fibreEquiv hsc a₀ hγ₀'))
  · have hempty : scalarFibre sc γ₀ γ = ∅ := by
      ext ⟨a, γ'⟩
      simp only [scalarFibre, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hγ' hγ
      exact h ⟨a, γ', hγ', hγ.symm⟩
    rw [hempty]
    exact Set.finite_empty

end FibreFinite

section Continuity

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 F) F) := by
  refine Continuous.units_map _ ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

private theorem finite_contributing (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    {N M : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hN : IsCompact N) (hM : IsCompact M) :
    {γ : GL (Fin 2) F | ∃ x ∈ N, ∃ y ∈ M, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y) ≠ 0}.Finite := by
  refine (AutomorphicForm.adelicKernelLocalFiniteness F (N * tsupport f * M⁻¹) ((hN.mul hfc).mul hM.inv)
    1 1).subset ?_
  rintro γ ⟨x, hx, y, hy, hne⟩
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  exact Set.mem_mul.mpr ⟨x * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y),
    Set.mem_mul.mpr ⟨x, hx, _, subset_tsupport f hne, rfl⟩, y⁻¹, Set.inv_mem_inv.mpr hy, by group⟩

private theorem continuous_finsum_mem_kernelSummand (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (S : Set (GL (Fin 2) F)) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      ∑ᶠ γ ∈ S, f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hMc, hM⟩ := exists_compact_mem_nhds y₀
  have hS := finite_contributing f hfc hNc hMc
  have heq : ∀ p ∈ N ×ˢ M,
      (∑ᶠ γ ∈ S, f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2)) =
        ∑ γ ∈ hS.toFinset.filter (· ∈ S), f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2) := by
    intro p hp
    rw [finsum_mem_eq_sum_of_subset _ (t := hS.toFinset.filter (· ∈ S)) ?_ ?_]
    · rintro γ ⟨hγS, hγs⟩
      rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨p.1, hp.1, p.2, hp.2, hγs⟩, hγS⟩
    · intro γ hγ
      rw [Finset.mem_coe, Finset.mem_filter] at hγ
      exact hγ.2
  have hcont : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      ∑ γ ∈ hS.toFinset.filter (· ∈ S), f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2) :=
    continuous_finsetSum _ fun γ _ =>
      hf.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  have hNM : N ×ˢ M ∈ nhds (x₀, y₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hN hM
  exact hcont.continuousAt.congr (Filter.eventuallyEq_of_mem hNM fun p hp => (heq p hp).symm)

private theorem continuous_orbitSum (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ => orbitSum F f γ₀ p.1 p.2 := by
  have h := (continuous_finsum_mem_kernelSummand f hf hfc (conjOrbit γ₀)).comp
    (continuous_fst.prodMk ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  exact h.congr fun p => by simp only [Function.comp_apply, Pi.mul_apply, orbitSum]

end Continuity

section Unfold

variable {F : Type} [Field F] [NumberField F]

private theorem principal_injective :
    Function.Injective (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)

private theorem countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm

private theorem countable_range_principal :
    Countable (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range := by
  haveI := countable_numberField (F := F)
  haveI : Countable Fˣ := Function.Injective.countable (Units.val_injective (α := F))
  exact Countable.of_equiv _ (MonoidHom.ofInjective (principal_injective (F := F))).toEquiv

private theorem finite_support_orbitSum_princ (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (γ₀ : GL (Fin 2) F) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    (Function.support fun a : Fˣ => orbitSum F f γ₀ x (princ F a * z)).Finite := by
  classical
  have hTfin := finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)
  haveI : Finite (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) := (finite_scalarStab γ₀).to_subtype
  refine ((hTfin.biUnion fun γ _ =>
    (finite_scalarFibre (fun a => scalar_mem_center a) (sc := Matrix.GeneralLinearGroup.scalar (Fin 2))
      (γ₀ := γ₀) γ).image Prod.fst)).subset ?_
  intro a ha
  rw [Function.mem_support] at ha
  unfold orbitSum at ha
  have hex : ∃ γ' ∈ conjOrbit γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
      (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z) * x)) ≠ 0 := by
    by_contra h
    refine ha (finsum_mem_of_eqOn_zero fun γ' hγ' => ?_)
    by_contra hne
    exact h ⟨γ', hγ', hne⟩
  obtain ⟨γ', hγ', hne⟩ := hex
  rw [← kernelSummand_scalar_mul f a γ' x z] at hne
  refine Set.mem_biUnion (x := Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') hne ?_
  exact ⟨(a, γ'), ⟨hγ', rfl⟩, rfl⟩

private theorem finsum_orbitSum_princ_eq (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (γ₀ : GL (Fin 2) F) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) =
      stabCard F γ₀ * ∑ᶠ γ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀,
        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x)) := by
  classical
  have hTfin := finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)
  haveI : Finite (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) := (finite_scalarStab γ₀).to_subtype
  rw [finsum_mem_family_eq_inv_card_mul_finsum_finsum (fun a => scalar_mem_center a) _
    (hTfin.subset Set.inter_subset_right)]
  have hcard : stabCard F γ₀ =
      ((Nat.card (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) : ℕ) : ℂ) := rfl
  have hne : stabCard F γ₀ ≠ 0 := by
    rw [hcard]
    have hpos : 0 < Nat.card (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀) :=
      Nat.card_pos_iff.mpr ⟨⟨1, one_mem_scalarStab⟩, inferInstance⟩
    exact_mod_cast hpos.ne'
  rw [hcard] at hne ⊢
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  refine finsum_congr fun a => ?_
  unfold orbitSum
  exact finsum_mem_congr rfl fun γ' _ => (kernelSummand_scalar_mul f a γ' x z).symm

private theorem continuous_finsum_orbitSum_princ (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ∑ᶠ a : Fˣ, orbitSum F f γ₀ p.1 (princ F a * p.2) := by
  have h := (continuous_finsum_mem_kernelSummand f hf hfc
    (scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀)).comp
    (continuous_fst.prodMk ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  have h2 : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      stabCard F γ₀ * ∑ᶠ γ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2)) γ₀,
        f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F p.2 * p.1)) :=
    continuous_const.mul h
  exact h2.congr fun p => (finsum_orbitSum_princ_eq f hfc γ₀ p.1 p.2).symm

private theorem setIntegral_finsum_princ_eq_integral
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (γ₀ : GL (Fin 2) F) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun w : (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) νZ) :
    IntegrableOn (fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z)) Ω νZ ∧
      ∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) ∂νZ =
        ∫ w, ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w ∂νZ := by
  classical
  haveI := measurableConstSMul_principal F
  haveI := smulInvariantMeasure_principal F νZ
  haveI := countable_range_principal (F := F)

  have hfold : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      (∑' g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range,
        ((ξ ⟨g • z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x (g • z)) =
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) := by
    intro z
    have hval : ∀ g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range,
        ((ξ ⟨g • z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro g
      have h1 : (⟨g • z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) =
          ⟨(g : (AdeleRing (𝓞 F) F)ˣ), Subgroup.mem_top _⟩ * ⟨z, Subgroup.mem_top z⟩ := rfl
      rw [h1, map_mul, hξt _ g.2, one_mul]
    simp_rw [hval]
    rw [tsum_mul_left]
    congr 1

    have hre := (MonoidHom.ofInjective (principal_injective (F := F))).toEquiv.tsum_eq
      fun g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range =>
        orbitSum F f γ₀ x (g • z)
    rw [← hre]
    have hterm : ∀ a : Fˣ, orbitSum F f γ₀ x
        (((MonoidHom.ofInjective (principal_injective (F := F))).toEquiv a) • z) =
          orbitSum F f γ₀ x (princ F a * z) := fun a => rfl
    exact (tsum_congr hterm).trans (tsum_eq_finsum (finite_support_orbitSum_princ f hfc γ₀ x z))
  have hmeas : AEStronglyMeasurable (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z))
      (νZ.restrict Ω) :=
    (hξc.mul ((continuous_finsum_orbitSum_princ f hf hfc γ₀).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · have h := integrableOn_tsum_smul hΩ
      (fun w => ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) hint
      (by simpa only [hfold] using hmeas)
    simpa only [hfold] using h
  · rw [integral_eq_setIntegral_tsum_smul hΩ
      (fun w => ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) hint]
    exact setIntegral_congr_fun₀ hΩ.nullMeasurableSet fun z _ => (hfold z).symm

end Unfold

section Xunfold

variable {F : Type} [Field F] [NumberField F]

private theorem countable_GL : Countable (GL (Fin 2) F) := by
  haveI := countable_numberField (F := F)
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact Function.Injective.countable (Units.val_injective (α := Matrix (Fin 2) (Fin 2) F))

private theorem globalPoints_injective : Function.Injective (AutomorphicForm.globalPoints (𝓞 F) F) := by
  intro a b h
  have h' : (a : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (AdeleRing (𝓞 F) F)) =
      (b : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (AdeleRing (𝓞 F) F)) := congrArg Units.val h
  apply Units.ext
  ext i j
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (by simpa using congrFun (congrFun h' i) j)

private theorem countable_range_globalPoints : Countable (AutomorphicForm.globalPoints (𝓞 F) F).range := by
  haveI := countable_GL (F := F)
  exact Countable.of_equiv _ (MonoidHom.ofInjective (globalPoints_injective (F := F))).toEquiv

private theorem measurableConstSMul_subgroup (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F)) :
    MeasurableConstSMul H (AutomorphicForm.AdelicGL2 (𝓞 F) F) := by
  haveI := borelSpace_adelicGL2 F
  exact ⟨fun g => measurable_const_mul (g : AutomorphicForm.AdelicGL2 (𝓞 F) F)⟩

private theorem smulInvariantMeasure_band_of_le (α β : ℝ) {H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F)}
    (hH : H ≤ (AutomorphicForm.globalPoints (𝓞 F) F).range) :
    SMulInvariantMeasure H (AutomorphicForm.AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
  haveI := smulInvariantMeasure_band_globalPoints F α β
  exact ⟨fun h s hs => SMulInvariantMeasure.measure_preimage_smul
    (⟨(h : AutomorphicForm.AdelicGL2 (𝓞 F) F), hH h.2⟩ : (AutomorphicForm.globalPoints (𝓞 F) F).range) hs⟩

private noncomputable def kernelTerm (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (γ₀ : GL (Fin 2) F)
    (w : (AdeleRing (𝓞 F) F)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 F) F) : ℂ :=
  f (y⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ * (AutomorphicForm.centralScalar (𝓞 F) F w * y))

private theorem kernelTerm_globalPoints_mul (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (γ₀ k : GL (Fin 2) F)
    (w : (AdeleRing (𝓞 F) F)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    kernelTerm f γ₀ w (AutomorphicForm.globalPoints (𝓞 F) F k * y) = kernelTerm f (k⁻¹ * γ₀ * k) w y := by
  unfold kernelTerm
  congr 1
  rw [map_mul, map_mul, map_inv, ← mul_assoc (AutomorphicForm.centralScalar (𝓞 F) F w),
    centralScalar_mul_comm F w]
  group

private theorem kernelTerm_centralizer (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (γ₀ : GL (Fin 2) F)
    (w : (AdeleRing (𝓞 F) F)ˣ)
    (c : (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F))
    (y : AutomorphicForm.AdelicGL2 (𝓞 F) F) : kernelTerm f γ₀ w (c • y) = kernelTerm f γ₀ w y := by
  obtain ⟨_, k, hk, rfl⟩ := c
  have hk' : γ₀ * k = k * γ₀ := Subgroup.mem_centralizer_iff.mp hk γ₀ (Set.mem_singleton γ₀)
  have h1 : k⁻¹ * γ₀ * k = γ₀ := by rw [mul_assoc, hk', ← mul_assoc, inv_mul_cancel, one_mul]
  show kernelTerm f γ₀ w (AutomorphicForm.globalPoints (𝓞 F) F k * y) = kernelTerm f γ₀ w y
  rw [kernelTerm_globalPoints_mul, h1]

private theorem continuous_kernelTerm (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (γ₀ : GL (Fin 2) F) (w : (AdeleRing (𝓞 F) F)ˣ) : Continuous (kernelTerm f γ₀ w) := by
  unfold kernelTerm
  exact hf.comp ((continuous_id.inv.mul continuous_const).mul (continuous_const.mul continuous_id))

private theorem tsum_indicator_kernelTerm_eq_orbitSum (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
    (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F) (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (w : (AdeleRing (𝓞 F) F)ˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F)
    (hU : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
      ∃! c : ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
          (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf (AutomorphicForm.globalPoints (𝓞 F) F).range,
        c • (g • x) ∈ Ψ) :
    ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x =
      orbitSum F f γ₀ x w := by
  classical
  haveI := countable_range_globalPoints (F := F)

  have hind : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
      (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x = Ψ.indicator (kernelTerm f γ₀ w) (g⁻¹ • x) := by
    intro g
    simp only [Set.indicator, Set.mem_smul_set_iff_inv_smul_mem]

  set ψ : GL (Fin 2) F → ℂ := fun h =>
    Ψ.indicator (kernelTerm f γ₀ w) (AutomorphicForm.globalPoints (𝓞 F) F h * x) with hψ

  set T : GL (Fin 2) F → ℂ := fun γ' =>
    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' * (AutomorphicForm.centralScalar (𝓞 F) F w * x)) with hT
  have hTfin : (Function.support T).Finite :=
    finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F w * x)
  have hψT : ∀ h : GL (Fin 2) F, AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ → ψ h = T (h⁻¹ * γ₀ * h) := by
    intro h hh
    simp only [hψ, Set.indicator_of_mem hh]
    exact kernelTerm_globalPoints_mul f γ₀ h w x
  have hψ0 : ∀ h : GL (Fin 2) F, AutomorphicForm.globalPoints (𝓞 F) F h * x ∉ Ψ → ψ h = 0 := by
    intro h hh
    simp only [hψ, Set.indicator_of_notMem hh]

  set S₀ : Set (GL (Fin 2) F) :=
    {h | AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ ∧ T (h⁻¹ * γ₀ * h) ≠ 0} with hS₀
  have hsupp : Function.support ψ ⊆ S₀ := by
    intro h hh
    rw [Function.mem_support] at hh
    by_cases hmem : AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ
    · exact ⟨hmem, by rwa [hψT h hmem] at hh⟩
    · exact absurd (hψ0 h hmem) hh

  have hinj : Set.InjOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) S₀ := by
    intro h₁ hh₁ h₂ hh₂ heq
    dsimp only at heq
    have hk : h₂ * h₁⁻¹ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hmem
      rw [Set.mem_singleton_iff.mp hmem]
      have h3 : γ₀ * h₂ = h₂ * (h₁⁻¹ * γ₀ * h₁) := by rw [heq]; group
      calc γ₀ * (h₂ * h₁⁻¹) = γ₀ * h₂ * h₁⁻¹ := by group
        _ = h₂ * (h₁⁻¹ * γ₀ * h₁) * h₁⁻¹ := by rw [h3]
        _ = h₂ * h₁⁻¹ * γ₀ := by group
    obtain ⟨c, hc, hcu⟩ := hU ⟨AutomorphicForm.globalPoints (𝓞 F) F h₁, h₁, rfl⟩
    have h1 : (1 : ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
        (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf (AutomorphicForm.globalPoints (𝓞 F) F).range) =
        ⟨⟨AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹), h₂ * h₁⁻¹, rfl⟩, ⟨h₂ * h₁⁻¹, hk, rfl⟩⟩ := by
      refine (hcu 1 ?_).trans (hcu _ ?_).symm
      · simp only [one_smul]
        exact hh₁.1
      · show AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹) * (AutomorphicForm.globalPoints (𝓞 F) F h₁ * x) ∈ Ψ
        rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
        exact hh₂.1
    have h2 : AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹) = 1 :=
      (congrArg Subtype.val (congrArg Subtype.val h1)).symm
    have h3 : h₂ * h₁⁻¹ = 1 := globalPoints_injective (F := F) (by rw [h2, map_one])
    exact (mul_inv_eq_one.mp h3).symm
  have himage : (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) '' S₀ ⊆ Function.support T := by
    rintro _ ⟨h, hh, rfl⟩
    exact hh.2
  have hS₀fin : S₀.Finite := Set.Finite.of_finite_image (hTfin.subset himage) hinj

  have hbij : Set.BijOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) S₀ (conjOrbit γ₀ ∩ Function.support T) := by
    refine ⟨fun h hh => ⟨⟨h, rfl⟩, hh.2⟩, hinj, ?_⟩
    rintro γ' ⟨⟨h₀, rfl⟩, hT'⟩
    obtain ⟨c, hc, -⟩ := hU ⟨AutomorphicForm.globalPoints (𝓞 F) F h₀, h₀, rfl⟩
    obtain ⟨⟨_, k, rfl⟩, hcC⟩ := c
    obtain ⟨k', hk', hkk'⟩ := (Subgroup.mem_subgroupOf.mp hcC :
      AutomorphicForm.globalPoints (𝓞 F) F k ∈ (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
        (AutomorphicForm.globalPoints (𝓞 F) F))
    have hc' : AutomorphicForm.globalPoints (𝓞 F) F k' * (AutomorphicForm.globalPoints (𝓞 F) F h₀ * x) ∈ Ψ := by
      rw [hkk']
      exact hc
    have hk'' : k'⁻¹ * γ₀ * k' = γ₀ := by
      have := Subgroup.mem_centralizer_iff.mp hk' γ₀ (Set.mem_singleton γ₀)
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    have hconj : (k' * h₀)⁻¹ * γ₀ * (k' * h₀) = h₀⁻¹ * γ₀ * h₀ := by
      rw [mul_inv_rev, show h₀⁻¹ * k'⁻¹ * γ₀ * (k' * h₀) = h₀⁻¹ * (k'⁻¹ * γ₀ * k') * h₀ by group, hk'']
    refine ⟨k' * h₀, ⟨?_, ?_⟩, hconj⟩
    · show AutomorphicForm.globalPoints (𝓞 F) F (k' * h₀) * x ∈ Ψ
      rw [map_mul, mul_assoc]
      exact hc'
    · show T ((k' * h₀)⁻¹ * γ₀ * (k' * h₀)) ≠ 0
      rw [hconj]
      exact hT'

  calc ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x
      = ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range, Ψ.indicator (kernelTerm f γ₀ w) (g⁻¹ • x) :=
        tsum_congr hind
    _ = ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range, Ψ.indicator (kernelTerm f γ₀ w) (g • x) :=
        (Equiv.inv (AutomorphicForm.globalPoints (𝓞 F) F).range).tsum_eq
          fun g => Ψ.indicator (kernelTerm f γ₀ w) (g • x)
    _ = ∑' h : GL (Fin 2) F, ψ h :=
        ((MonoidHom.ofInjective (globalPoints_injective (F := F))).toEquiv.tsum_eq
          fun g : (AutomorphicForm.globalPoints (𝓞 F) F).range => Ψ.indicator (kernelTerm f γ₀ w) (g • x)).symm
    _ = ∑ᶠ h : GL (Fin 2) F, ψ h := tsum_eq_finsum (hS₀fin.subset hsupp)
    _ = ∑ᶠ h ∈ (Set.univ : Set (GL (Fin 2) F)), ψ h := (finsum_mem_univ ψ).symm
    _ = ∑ᶠ h ∈ S₀, ψ h :=
        finsum_mem_inter_support_eq' ψ Set.univ S₀ fun h hh => ⟨fun _ => hsupp hh, fun _ => Set.mem_univ h⟩
    _ = ∑ᶠ γ' ∈ conjOrbit γ₀ ∩ Function.support T, T γ' :=
        finsum_mem_eq_of_bijOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) hbij fun h hh => hψT h hh.1
    _ = ∑ᶠ γ' ∈ conjOrbit γ₀, T γ' := finsum_mem_inter_support T (conjOrbit γ₀)
    _ = orbitSum F f γ₀ x w := rfl

private theorem setIntegral_orbitSum_eq_setIntegral_centralizerDomain (α β : ℝ)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (γ₀ : GL (Fin 2) F) (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΨs : Ψ ⊆ normBand F α β)
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (w : (AdeleRing (𝓞 F) F)ˣ)
    (hint : IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ * (AutomorphicForm.centralScalar (𝓞 F) F w * x))) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    ∫ x in Φ, orbitSum F f γ₀ x w ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F w * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  classical
  haveI := borelSpace_adelicGL2 F
  haveI := measurableConstSMul_subgroup (F := F) (AutomorphicForm.globalPoints (𝓞 F) F).range
  haveI := smulInvariantMeasure_band_globalPoints F α β
  haveI := countable_range_globalPoints (F := F)
  have hCΓ : (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F) ≤
      (AutomorphicForm.globalPoints (𝓞 F) F).range :=
    Subgroup.map_le_range _ _

  rw [← Measure.restrict_restrict_of_subset hΦs, ← Measure.restrict_restrict_of_subset hΨs]
  change ∫ x in Φ, orbitSum F f γ₀ x w ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) =
    ∫ x in Ψ, kernelTerm f γ₀ w x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))
  have hint' : IntegrableOn (kernelTerm f γ₀ w) Ψ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := hint
  have hT₀cont := continuous_kernelTerm f hf γ₀ w

  have hgΨ : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range, NullMeasurableSet (g • Ψ)
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)).restrict Φ) := fun g =>
    (hΨ.nullMeasurableSet.smul g).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

  have h1 := hΦ.setIntegral_eq_tsum' hint'

  have h2 : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
      ∫ x in g • Ψ ∩ Φ, kernelTerm f γ₀ w (g⁻¹ • x) ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) =
        ∫ x in Φ, (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
    intro g
    rw [integral_indicator₀ (hgΨ g), Measure.restrict_restrict₀ (hgΨ g)]

  have h3 : ∫ x in Φ, ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) =
      ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range, ∫ x in Φ,
        (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
    refine integral_tsum (fun g => ?_) ?_
    · exact ((hT₀cont.comp (continuous_const_smul g⁻¹)).aestronglyMeasurable).indicator₀ (hgΨ g)
    · have hterm : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
          ∫⁻ x in Φ, ‖(g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x‖ₑ
              ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) =
            ∫⁻ x in g • Ψ ∩ Φ, ‖kernelTerm f γ₀ w (g⁻¹ • x)‖ₑ
              ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
        intro g
        simp_rw [enorm_indicator_eq_indicator_enorm]
        rw [lintegral_indicator₀ (hgΨ g), Measure.restrict_restrict₀ (hgΨ g)]
      simp_rw [hterm]
      rw [← hΦ.setLIntegral_eq_tsum' (fun x => ‖kernelTerm f γ₀ w x‖ₑ) Ψ]
      exact hint'.2.ne

  have hΨ' := isFundamentalDomain_subgroupOf hCΓ hΨ
  have h4 := ae_forall_existsUnique_smul_mem _ hΨ'
  have h5 : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)), x ∈ Φ →
      orbitSum F f γ₀ x w = ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => kernelTerm f γ₀ w (g⁻¹ • y)) x :=
    h4.mono fun x hx _ => (tsum_indicator_kernelTerm_eq_orbitSum f hfc γ₀ Ψ w x hx).symm
  rw [setIntegral_congr_ae₀ hΦ.nullMeasurableSet h5, h3, h1]
  exact tsum_congr fun g => (h2 g).symm

end Xunfold

open scoped ENNReal NNReal

section GenericComp

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_finsum_mem_comp_kernelSummand {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] (φ : ℂ → E) (hφ0 : φ 0 = 0) (hφ : Continuous φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (S : Set (GL (Fin 2) F)) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      ∑ᶠ γ ∈ S, φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2)) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hMc, hM⟩ := exists_compact_mem_nhds y₀
  have hS := finite_contributing f hfc hNc hMc
  have heq : ∀ p ∈ N ×ˢ M,
      (∑ᶠ γ ∈ S, φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2))) =
        ∑ γ ∈ hS.toFinset.filter (· ∈ S),
          φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2)) := by
    intro p hp
    rw [finsum_mem_eq_sum_of_subset _ (t := hS.toFinset.filter (· ∈ S)) ?_ ?_]
    · rintro γ ⟨hγS, hγs⟩
      rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨p.1, hp.1, p.2, hp.2, fun h0 => hγs ?_⟩, hγS⟩
      show φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2)) = 0
      rw [h0, hφ0]
    · intro γ hγ
      rw [Finset.mem_coe, Finset.mem_filter] at hγ
      exact hγ.2
  have hcont : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      ∑ γ ∈ hS.toFinset.filter (· ∈ S),
        φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * p.2)) :=
    continuous_finsetSum _ fun γ _ =>
      hφ.comp (hf.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd))
  have hNM : N ×ˢ M ∈ nhds (x₀, y₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hN hM
  exact hcont.continuousAt.congr (Filter.eventuallyEq_of_mem hNM fun p hp => (heq p hp).symm)

private theorem continuous_finsum_mem_orbit_comp {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] (φ : ℂ → E) (hφ0 : φ 0 = 0) (hφ : Continuous φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (S : Set (GL (Fin 2) F)) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ∑ᶠ γ ∈ S, φ (f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F p.2 * p.1))) := by
  have h := (continuous_finsum_mem_comp_kernelSummand φ hφ0 hφ f hf hfc S).comp
    (continuous_fst.prodMk ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  exact h.congr fun p => by simp only [Function.comp_apply, Pi.mul_apply]

private theorem continuous_finsum_mem_orbit_comp_snd {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] (φ : ℂ → E) (hφ0 : φ 0 = 0) (hφ : Continuous φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (S : Set (GL (Fin 2) F)) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∑ᶠ γ ∈ S, φ (f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x))) := by
  have h := (continuous_finsum_mem_comp_kernelSummand φ hφ0 hφ f hf hfc S).comp
    ((continuous_const : Continuous fun _ : (AdeleRing (𝓞 F) F)ˣ => x).prodMk
      (continuous_centralScalar.mul (continuous_const : Continuous fun _ : (AdeleRing (𝓞 F) F)ˣ => x)))
  exact h.congr fun z => by simp only [Function.comp_apply, Pi.mul_apply]

private theorem tsum_indicator_comp_kernelTerm_eq_finsum_orbit {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] (φ : ℂ → E) (hφ0 : φ 0 = 0)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (w : (AdeleRing (𝓞 F) F)ˣ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F)
    (hU : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
      ∃! c : ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
          (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf (AutomorphicForm.globalPoints (𝓞 F) F).range,
        c • (g • x) ∈ Ψ) :
    ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => φ (kernelTerm f γ₀ w (g⁻¹ • y))) x =
      ∑ᶠ γ' ∈ conjOrbit γ₀, φ (f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
        (AutomorphicForm.centralScalar (𝓞 F) F w * x))) := by
  classical
  haveI := countable_range_globalPoints (F := F)
  have hind : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
      (g • Ψ).indicator (fun y => φ (kernelTerm f γ₀ w (g⁻¹ • y))) x =
        Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (g⁻¹ • x) := by
    intro g
    simp only [Set.indicator, Set.mem_smul_set_iff_inv_smul_mem]
  set ψ : GL (Fin 2) F → E := fun h =>
    Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (AutomorphicForm.globalPoints (𝓞 F) F h * x) with hψ
  set T : GL (Fin 2) F → E := fun γ' =>
    φ (f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' * (AutomorphicForm.centralScalar (𝓞 F) F w * x)))
    with hT
  have hTfin : (Function.support T).Finite := by
    refine (finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F w * x)).subset ?_
    intro γ' hγ' h0
    apply hγ'
    show φ (f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
      (AutomorphicForm.centralScalar (𝓞 F) F w * x))) = 0
    rw [show f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
      (AutomorphicForm.centralScalar (𝓞 F) F w * x)) = 0 from h0, hφ0]
  have hψT : ∀ h : GL (Fin 2) F, AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ → ψ h = T (h⁻¹ * γ₀ * h) := by
    intro h hh
    simp only [hψ, Set.indicator_of_mem hh]
    exact congrArg φ (kernelTerm_globalPoints_mul f γ₀ h w x)
  have hψ0 : ∀ h : GL (Fin 2) F, AutomorphicForm.globalPoints (𝓞 F) F h * x ∉ Ψ → ψ h = 0 := by
    intro h hh
    simp only [hψ, Set.indicator_of_notMem hh]
  set S₀ : Set (GL (Fin 2) F) :=
    {h | AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ ∧ T (h⁻¹ * γ₀ * h) ≠ 0} with hS₀
  have hsupp : Function.support ψ ⊆ S₀ := by
    intro h hh
    rw [Function.mem_support] at hh
    by_cases hmem : AutomorphicForm.globalPoints (𝓞 F) F h * x ∈ Ψ
    · exact ⟨hmem, by rwa [hψT h hmem] at hh⟩
    · exact absurd (hψ0 h hmem) hh
  have hinj : Set.InjOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) S₀ := by
    intro h₁ hh₁ h₂ hh₂ heq
    dsimp only at heq
    have hk : h₂ * h₁⁻¹ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hmem
      rw [Set.mem_singleton_iff.mp hmem]
      have h3 : γ₀ * h₂ = h₂ * (h₁⁻¹ * γ₀ * h₁) := by rw [heq]; group
      calc γ₀ * (h₂ * h₁⁻¹) = γ₀ * h₂ * h₁⁻¹ := by group
        _ = h₂ * (h₁⁻¹ * γ₀ * h₁) * h₁⁻¹ := by rw [h3]
        _ = h₂ * h₁⁻¹ * γ₀ := by group
    obtain ⟨c, hc, hcu⟩ := hU ⟨AutomorphicForm.globalPoints (𝓞 F) F h₁, h₁, rfl⟩
    have h1 : (1 : ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
        (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf (AutomorphicForm.globalPoints (𝓞 F) F).range) =
        ⟨⟨AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹), h₂ * h₁⁻¹, rfl⟩, ⟨h₂ * h₁⁻¹, hk, rfl⟩⟩ := by
      refine (hcu 1 ?_).trans (hcu _ ?_).symm
      · simp only [one_smul]
        exact hh₁.1
      · show AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹) *
          (AutomorphicForm.globalPoints (𝓞 F) F h₁ * x) ∈ Ψ
        rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
        exact hh₂.1
    have h2 : AutomorphicForm.globalPoints (𝓞 F) F (h₂ * h₁⁻¹) = 1 :=
      (congrArg Subtype.val (congrArg Subtype.val h1)).symm
    have h3 : h₂ * h₁⁻¹ = 1 := globalPoints_injective (F := F) (by rw [h2, map_one])
    exact (mul_inv_eq_one.mp h3).symm
  have himage : (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) '' S₀ ⊆ Function.support T := by
    rintro _ ⟨h, hh, rfl⟩
    exact hh.2
  have hS₀fin : S₀.Finite := Set.Finite.of_finite_image (hTfin.subset himage) hinj
  have hbij : Set.BijOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) S₀ (conjOrbit γ₀ ∩ Function.support T) := by
    refine ⟨fun h hh => ⟨⟨h, rfl⟩, hh.2⟩, hinj, ?_⟩
    rintro γ' ⟨⟨h₀, rfl⟩, hT'⟩
    obtain ⟨c, hc, -⟩ := hU ⟨AutomorphicForm.globalPoints (𝓞 F) F h₀, h₀, rfl⟩
    obtain ⟨⟨_, k, rfl⟩, hcC⟩ := c
    obtain ⟨k', hk', hkk'⟩ := (Subgroup.mem_subgroupOf.mp hcC :
      AutomorphicForm.globalPoints (𝓞 F) F k ∈ (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map
        (AutomorphicForm.globalPoints (𝓞 F) F))
    have hc' : AutomorphicForm.globalPoints (𝓞 F) F k' * (AutomorphicForm.globalPoints (𝓞 F) F h₀ * x) ∈ Ψ := by
      rw [hkk']
      exact hc
    have hk'' : k'⁻¹ * γ₀ * k' = γ₀ := by
      have := Subgroup.mem_centralizer_iff.mp hk' γ₀ (Set.mem_singleton γ₀)
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    have hconj : (k' * h₀)⁻¹ * γ₀ * (k' * h₀) = h₀⁻¹ * γ₀ * h₀ := by
      rw [mul_inv_rev, show h₀⁻¹ * k'⁻¹ * γ₀ * (k' * h₀) = h₀⁻¹ * (k'⁻¹ * γ₀ * k') * h₀ by group, hk'']
    refine ⟨k' * h₀, ⟨?_, ?_⟩, hconj⟩
    · show AutomorphicForm.globalPoints (𝓞 F) F (k' * h₀) * x ∈ Ψ
      rw [map_mul, mul_assoc]
      exact hc'
    · show T ((k' * h₀)⁻¹ * γ₀ * (k' * h₀)) ≠ 0
      rw [hconj]
      exact hT'
  calc ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (g • Ψ).indicator (fun y => φ (kernelTerm f γ₀ w (g⁻¹ • y))) x
      = ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
          Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (g⁻¹ • x) := tsum_congr hind
    _ = ∑' g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
          Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (g • x) :=
        (Equiv.inv (AutomorphicForm.globalPoints (𝓞 F) F).range).tsum_eq
          fun g => Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (g • x)
    _ = ∑' h : GL (Fin 2) F, ψ h :=
        ((MonoidHom.ofInjective (globalPoints_injective (F := F))).toEquiv.tsum_eq
          fun g : (AutomorphicForm.globalPoints (𝓞 F) F).range =>
            Ψ.indicator (fun y => φ (kernelTerm f γ₀ w y)) (g • x)).symm
    _ = ∑ᶠ h : GL (Fin 2) F, ψ h := tsum_eq_finsum (hS₀fin.subset hsupp)
    _ = ∑ᶠ h ∈ (Set.univ : Set (GL (Fin 2) F)), ψ h := (finsum_mem_univ ψ).symm
    _ = ∑ᶠ h ∈ S₀, ψ h :=
        finsum_mem_inter_support_eq' ψ Set.univ S₀ fun h hh => ⟨fun _ => hsupp hh, fun _ => Set.mem_univ h⟩
    _ = ∑ᶠ γ' ∈ conjOrbit γ₀ ∩ Function.support T, T γ' :=
        finsum_mem_eq_of_bijOn (fun h : GL (Fin 2) F => h⁻¹ * γ₀ * h) hbij fun h hh => hψT h hh.1
    _ = ∑ᶠ γ' ∈ conjOrbit γ₀, T γ' := finsum_mem_inter_support T (conjOrbit γ₀)

end GenericComp

section ScalarCells

variable {K : Type*} [Field K]

private theorem glScalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL (Fin 2) K) := by
  intro a b hab
  have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hab
  simp only [coe_scalar] at h
  exact Units.ext (Matrix.scalar_inj.mp h)

private theorem mem_centralCell_iff_exists_scalar (γ : GL (Fin 2) K) :
    γ ∈ AutomorphicForm.centralCell K ↔ ∃ a : Kˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hu : IsUnit (γ : Matrix (Fin 2) (Fin 2) K).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)
      rw [hc, zero_smul, Matrix.det_zero] at hu
      exact not_isUnit_zero hu
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [coe_scalar, Units.val_mk0, hc, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  · rintro ⟨a, rfl⟩
    exact scalar_mem_centralCell a

private theorem centralCell_eq_range_scalar :
    AutomorphicForm.centralCell K = Set.range (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL (Fin 2) K) := by
  ext γ
  rw [Set.mem_range, mem_centralCell_iff_exists_scalar]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

private theorem finsum_mem_centralCell {E : Type*} [AddCommMonoid E] (u : GL (Fin 2) K → E) :
    ∑ᶠ γ ∈ AutomorphicForm.centralCell K, u γ = ∑ᶠ a : Kˣ, u (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  rw [centralCell_eq_range_scalar, finsum_mem_range glScalar_injective]

private theorem bijOn_scalar_mul_ellipticCell (a : Kˣ) :
    Set.BijOn (fun γ : GL (Fin 2) K => Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ)
      (AutomorphicForm.ellipticCell K) (AutomorphicForm.ellipticCell K) := by
  refine ⟨fun γ hγ => ?_, fun γ₁ _ γ₂ _ h => mul_left_cancel h, fun γ hγ => ?_⟩
  · have h := scalar_mul_conj_mem_ellipticCell hγ a 1
    simpa only [inv_one, one_mul, mul_one] using h
  · refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * γ, ?_, ?_⟩
    · have h := scalar_mul_conj_mem_ellipticCell hγ a⁻¹ 1
      simpa only [inv_one, one_mul, mul_one] using h
    · show Matrix.GeneralLinearGroup.scalar (Fin 2) a * (Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * γ) = γ
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem finsum_mem_ellipticCell_scalar_mul {E : Type*} [AddCommMonoid E] (u : GL (Fin 2) K → E) (a : Kˣ) :
    ∑ᶠ γ ∈ AutomorphicForm.ellipticCell K, u (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ) =
      ∑ᶠ γ ∈ AutomorphicForm.ellipticCell K, u γ :=
  finsum_mem_eq_of_bijOn _ (bijOn_scalar_mul_ellipticCell a) fun _ _ => rfl

private theorem finsum_mem_prod_eq_finsum_mem_family_nsmul {G A : Type*} [Group G] [CommGroup A] {sc : A →* G}
    {γ₀ : G} (hsc : ∀ a : A, sc a ∈ Subgroup.center G) [Finite (scalarStab sc γ₀)] {E : Type*}
    [AddCommMonoid E] (u : G → E) (hu : (scalarFamily sc γ₀ ∩ support u).Finite) :
    ∑ᶠ p ∈ (univ : Set A) ×ˢ conjOrbit γ₀, u (sc p.1 * p.2) =
      ∑ᶠ γ ∈ scalarFamily sc γ₀, Nat.card (scalarStab sc γ₀) • u γ := by
  classical
  have hfib_fin : ∀ γ ∈ scalarFamily sc γ₀ ∩ support u, (scalarFibre sc γ₀ γ).Finite := by
    intro γ hγ
    obtain ⟨h, a, rfl⟩ := hγ.1
    have : Finite (scalarFibre sc γ₀ (sc a * (h⁻¹ * γ₀ * h))) :=
      Finite.of_equiv _ (fibreEquiv hsc a ⟨h, rfl⟩)
    exact Set.toFinite _
  have hdisj : (scalarFamily sc γ₀ ∩ support u).PairwiseDisjoint (scalarFibre sc γ₀) := by
    intro γ _ γ' _ hne
    refine Set.disjoint_left.mpr fun p hp hp' => hne ?_
    exact hp.2.symm.trans hp'.2
  have hset : ((univ : Set A) ×ˢ conjOrbit γ₀) ∩ support (fun p : A × G => u (sc p.1 * p.2)) =
      ⋃ γ ∈ scalarFamily sc γ₀ ∩ support u, scalarFibre sc γ₀ γ := by
    ext ⟨a, γ'⟩
    constructor
    · rintro ⟨⟨-, hγ'⟩, hsupp⟩
      obtain ⟨h, rfl⟩ := hγ'
      exact Set.mem_biUnion (x := sc a * (h⁻¹ * γ₀ * h)) ⟨⟨h, a, rfl⟩, hsupp⟩ ⟨⟨h, rfl⟩, rfl⟩
    · intro hp
      obtain ⟨γ, hγ, hpγ⟩ := Set.mem_iUnion₂.mp hp
      refine ⟨⟨Set.mem_univ _, hpγ.1⟩, ?_⟩
      show u (sc a * γ') ≠ 0
      rw [hpγ.2]
      exact hγ.2
  have hpair : ∑ᶠ p ∈ (univ : Set A) ×ˢ conjOrbit γ₀, u (sc p.1 * p.2) =
      ∑ᶠ γ ∈ scalarFamily sc γ₀ ∩ support u, ∑ᶠ p ∈ scalarFibre sc γ₀ γ, u (sc p.1 * p.2) := by
    rw [← finsum_mem_inter_support, hset, finsum_mem_biUnion hdisj hu hfib_fin]
  have hconst : ∀ γ ∈ scalarFamily sc γ₀ ∩ support u,
      ∑ᶠ p ∈ scalarFibre sc γ₀ γ, u (sc p.1 * p.2) = Nat.card (scalarStab sc γ₀) • u γ := by
    intro γ hγ
    have hf : (scalarFibre sc γ₀ γ).Finite := hfib_fin γ hγ
    have hf' : (scalarFibre sc γ₀ γ ∩ support (fun _ : A × G => u γ)).Finite := hf.inter_of_left _
    have hne : u γ ≠ 0 := hγ.2
    have hsupp : scalarFibre sc γ₀ γ ∩ support (fun _ : A × G => u γ) = scalarFibre sc γ₀ γ := by
      ext p
      exact ⟨fun hp => hp.1, fun hp => ⟨hp, hne⟩⟩
    rw [finsum_mem_congr rfl (fun p hp => by rw [hp.2]), finsum_mem_eq_sum _ hf', Finset.sum_const]
    congr 1
    rw [← Set.ncard_eq_toFinset_card _ hf', hsupp, ← Nat.card_coe_set_eq]
    obtain ⟨h, a, rfl⟩ := hγ.1
    exact card_fibre hsc a ⟨h, rfl⟩
  rw [hpair, finsum_mem_congr rfl hconst]
  exact finsum_mem_inter_support_eq' _ _ _ fun γ hγ => ⟨fun h => h.1,
    fun h => ⟨h, fun h0 => hγ (by simp only [h0, smul_zero])⟩⟩

private theorem finsum_finsum_mem_orbit_eq_finsum_mem_family_nsmul {G A : Type*} [Group G] [CommGroup A]
    {sc : A →* G} {γ₀ : G} (hsc : ∀ a : A, sc a ∈ Subgroup.center G) [Finite (scalarStab sc γ₀)]
    {E : Type*} [AddCommMonoid E] (u : G → E) (hu : (scalarFamily sc γ₀ ∩ support u).Finite) :
    ∑ᶠ (a : A) (γ' : G) (_ : γ' ∈ conjOrbit γ₀), u (sc a * γ') =
      ∑ᶠ γ ∈ scalarFamily sc γ₀, Nat.card (scalarStab sc γ₀) • u γ := by
  rw [← finsum_mem_prod_eq_finsum_mem_family_nsmul hsc u hu]
  have hfin : HasFiniteSupport (((univ : Set A) ×ˢ conjOrbit γ₀).indicator fun p : A × G => u (sc p.1 * p.2)) := by
    have hsub : support (((univ : Set A) ×ˢ conjOrbit γ₀).indicator fun p : A × G => u (sc p.1 * p.2)) ⊆
        ⋃ γ ∈ scalarFamily sc γ₀ ∩ support u, scalarFibre sc γ₀ γ := by
      intro p hp
      rw [Function.mem_support, Set.indicator_apply_ne_zero] at hp
      obtain ⟨⟨-, hγ'⟩, hsupp⟩ := hp
      obtain ⟨h, hh⟩ := hγ'
      exact Set.mem_biUnion (x := sc p.1 * p.2) ⟨⟨h, p.1, by rw [hh]⟩, hsupp⟩ ⟨⟨h, hh⟩, rfl⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion hu fun γ hγ => ?_
    obtain ⟨h, a, rfl⟩ := hγ.1
    have : Finite (scalarFibre sc γ₀ (sc a * (h⁻¹ * γ₀ * h))) :=
      Finite.of_equiv _ (fibreEquiv hsc a ⟨h, rfl⟩)
    exact Set.toFinite _
  rw [finsum_mem_def, finsum_curry _ hfin]
  refine finsum_congr fun a => ?_
  rw [finsum_mem_def]
  refine finsum_congr fun γ' => ?_
  by_cases hγ' : γ' ∈ conjOrbit γ₀
  · rw [Set.indicator_of_mem (Set.mk_mem_prod (Set.mem_univ a) hγ'), Set.indicator_of_mem hγ']
  · rw [Set.indicator_of_notMem (fun hp => hγ' (Set.mem_prod.mp hp).2), Set.indicator_of_notMem hγ']

end ScalarCells

section MeasureGlue

variable {F : Type} [Field F] [NumberField F]

private theorem sigmaCompactSpace_adelicGL2 : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 F) F) := by
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).symm.isClosedEmbedding
      |>.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem sigmaCompactSpace_ideles : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 F) F)).symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem secondCountableTopology_adelicGL2 : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

private theorem measurableSet_band (α β : ℝ) : MeasurableSet (normBand F α β) := by
  haveI := borelSpace_adelicGL2 F
  exact (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det F)).measurableSet

private theorem nullMeasurableSet_of_isFundamentalDomain_band (α β : ℝ)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := borelSpace_adelicGL2 F
  have h := (nullMeasurableSet_restrict (measurableSet_band α β).nullMeasurableSet).mp hΦ.nullMeasurableSet
  rwa [Set.inter_eq_left.mpr hΦs] at h

private theorem isFiniteMeasure_restrict_of_isFundamentalDomain_band (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have h : adelicGLHaar (Fin 2) (𝓞 F) F (Φ ∩ normBand F α β) < ⊤ :=
    AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      F α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_left.mpr hΦs] at h

private theorem kernelSummand_scalar_eq (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) (a : Fˣ) :
    x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x) =
      AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z) := by
  unfold princ
  rw [globalPoints_scalar, inv_mul_mul_centralScalar_mul,
    ← centralScalar_mul_comm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) x⁻¹,
    mul_assoc (AutomorphicForm.centralScalar (𝓞 F) F _) x⁻¹ x, inv_mul_cancel, mul_one, ← map_mul]

private theorem hasCompactSupport_comp_centralScalar (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
    (hfc : HasCompactSupport f) :
    HasCompactSupport fun z : (AdeleRing (𝓞 F) F)ˣ => f (AutomorphicForm.centralScalar (𝓞 F) F z) := by
  have hKc : IsCompact (tsupport f) := hfc
  set π : AutomorphicForm.AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F :=
    fun g => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 with hπ
  have hπc : Continuous π := Units.continuous_val.matrix_elem 0 0
  have hA : IsCompact (π '' tsupport f) := hKc.image hπc
  have hB : IsCompact (π '' (tsupport f)⁻¹) := hKc.inv.image hπc
  have hpre : IsCompact (Units.embedProduct (AdeleRing (𝓞 F) F) ⁻¹'
      ((π '' tsupport f) ×ˢ (MulOpposite.op '' (π '' (tsupport f)⁻¹)))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hA.prod (hB.image MulOpposite.continuous_op))
  have hπcz : ∀ z : (AdeleRing (𝓞 F) F)ˣ, π (AutomorphicForm.centralScalar (𝓞 F) F z) = (z : AdeleRing (𝓞 F) F) := by
    intro z
    rw [hπ]
    dsimp only
    rw [coe_centralScalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have hC : IsCompact (AutomorphicForm.centralScalar (𝓞 F) F ⁻¹' tsupport f) := by
    refine hpre.of_isClosed_subset ((isClosed_tsupport f).preimage continuous_centralScalar) ?_
    intro z hz
    show ((z : AdeleRing (𝓞 F) F), MulOpposite.op ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ∈
      (π '' tsupport f) ×ˢ (MulOpposite.op '' (π '' (tsupport f)⁻¹))
    refine Set.mk_mem_prod ⟨_, hz, hπcz z⟩ ⟨_, ⟨(AutomorphicForm.centralScalar (𝓞 F) F z)⁻¹,
      Set.inv_mem_inv.mpr hz, ?_⟩, rfl⟩
    rw [← map_inv, hπcz]
  exact HasCompactSupport.of_support_subset_isCompact hC fun z hz => subset_tsupport f hz

private noncomputable def topChar (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  ξ.comp ⟨⟨fun z => ⟨z, Subgroup.mem_top z⟩, rfl⟩, fun _ _ => rfl⟩

private theorem topChar_apply (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 F) F)ˣ) :
    topChar ξ z = ξ ⟨z, Subgroup.mem_top z⟩ :=
  rfl

private theorem continuous_topChar (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (topChar ξ) := by
  rw [Units.continuous_iff]
  refine ⟨hξc, ?_⟩
  refine (hξc.comp continuous_inv).congr fun z => ?_
  show ((ξ ⟨z⁻¹, Subgroup.mem_top z⁻¹⟩ : ℂˣ) : ℂ) = (((topChar ξ z)⁻¹ : ℂˣ) : ℂ)
  rw [← map_inv]
  rfl

private theorem isIdeleClassChar_topChar (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1) :
    AutomorphicForm.IsIdeleClassChar (𝓞 F) F (topChar ξ) :=
  fun u => hξt _ ⟨u, rfl⟩

private theorem char_princ_mul (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (a : Fˣ) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ξ ⟨princ F a * z, Subgroup.mem_top _⟩ = ξ ⟨z, Subgroup.mem_top z⟩ := by
  have h : (⟨princ F a * z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) =
      ⟨princ F a, Subgroup.mem_top _⟩ * ⟨z, Subgroup.mem_top z⟩ := rfl
  rw [h, map_mul, hξt (princ F a) ⟨a, rfl⟩, one_mul]

private theorem ideleNorm_one' : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' (h.symm.trans (mul_one _).symm)

private theorem ideleNorm_inv' (u : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F u⁻¹ = (NumberField.TateGlobal.ideleNorm F u)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem ideleNorm_princ (a : Fˣ) : NumberField.TateGlobal.ideleNorm F (princ F a) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
  rw [globalPoints_scalar] at h
  have h' : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))) = 1 := h
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two,
    NumberField.TateGlobal.ideleNorm_mul] at h'
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F)
    (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a)
  unfold princ
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact h1
  · exact absurd h1 (by linarith)

private theorem det_kernel_arg (x g : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (x⁻¹ * g * (AutomorphicForm.centralScalar (𝓞 F) F z * x)) =
      Matrix.GeneralLinearGroup.det g * z ^ 2 := by
  have hdz : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 F) F z) = z ^ 2 := by
    have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
    rw [Fintype.card_fin] at h
    exact h
  rw [map_mul, map_mul, map_mul, map_inv, hdz,
    show (Matrix.GeneralLinearGroup.det x)⁻¹ * Matrix.GeneralLinearGroup.det g *
        (z ^ 2 * Matrix.GeneralLinearGroup.det x) =
      (Matrix.GeneralLinearGroup.det x)⁻¹ * (Matrix.GeneralLinearGroup.det g * z ^ 2) *
        Matrix.GeneralLinearGroup.det x by simp only [mul_assoc], inv_mul_cancel_comm]

private theorem ideleNorm_sq_mem_of_kernel_ne_zero (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) {m₀ M₀ : ℝ}
    (hlo : ∀ g ∈ tsupport f, m₀ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))
    (hhi : ∀ g ∈ tsupport f, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M₀)
    (γ : GL (Fin 2) F) (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ)
    (hne : f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ≠ 0) :
    NumberField.TateGlobal.ideleNorm F z ^ 2 ∈ Set.Icc m₀ M₀ := by
  have hmem : x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x) ∈
      tsupport f := subset_tsupport f hne
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
      (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))) =
      NumberField.TateGlobal.ideleNorm F z ^ 2 := by
    rw [det_kernel_arg, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul,
      pow_two, NumberField.TateGlobal.ideleNorm_mul, pow_two]
  rw [← hdet]
  exact ⟨hlo _ hmem, hhi _ hmem⟩

private theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

private theorem exists_forall_enorm_char_le (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z ∈ Set.Icc m₁ M₁ →
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ ≤ C := by
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F (topChar ξ)
    (isIdeleClassChar_topChar ξ hξt) (continuous_topChar ξ hξc)
  refine ⟨ENNReal.ofReal (max (m₁ ^ σ) (M₁ ^ σ)), ENNReal.ofReal_ne_top, fun z hz => ?_⟩
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [show ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = ((topChar ξ z : ℂˣ) : ℂ) from rfl, hσ z]
  rcases le_or_gt 0 σ with hσ0 | hσ0
  · exact le_max_of_le_right (Real.rpow_le_rpow (NumberField.TateGlobal.ideleNorm_pos (F := F) z).le hz.2 hσ0)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hm₁ hz.1 hσ0.le)

private theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Fˣ) (c : (AdeleRing (𝓞 F) F)ˣ), c ∈ C ∧ z = princ F a * c := by
  have hC :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul F
  obtain ⟨C₁, hC₁c, -, hC₁⟩ := hC
  have hs := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
  obtain ⟨s, hs_cont, hs_norm, -⟩ := hs
  set S₁ : Set ℝ≥0ˣ := {r | ((r : ℝ≥0) : ℝ) ∈ Set.Icc m₁ M₁} with hS₁
  have hS₁c : IsCompact S₁ := by
    set a₀ : ℝ≥0 := ⟨m₁, hm₁.le⟩ with ha₀
    set b₀ : ℝ≥0 := Real.toNNReal M₁ with hb₀
    have ha₀pos : 0 < a₀ := hm₁
    have hpre : IsCompact (Units.embedProduct ℝ≥0 ⁻¹'
        (Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹))) :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage
        (isCompact_Icc.prod (isCompact_Icc.image MulOpposite.continuous_op))
    refine hpre.of_isClosed_subset (isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)) ?_
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrpos : 0 < (r : ℝ≥0) := lt_of_lt_of_le ha₀pos hr1
    have h1 : a₀ ≤ (r : ℝ≥0) := hr1
    have h2 : (r : ℝ≥0) ≤ b₀ := (Real.le_toNNReal_iff_coe_le (le_trans (le_trans hm₁.le hr1) hr2)).mpr hr2
    show ((r : ℝ≥0), MulOpposite.op ((r⁻¹ : ℝ≥0ˣ) : ℝ≥0)) ∈
      Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹)
    refine Set.mk_mem_prod ⟨h1, h2⟩ ⟨(r : ℝ≥0)⁻¹, ⟨inv_anti₀ hrpos h2, inv_anti₀ ha₀pos h1⟩, ?_⟩
    rw [Units.val_inv_eq_inv_val]
  refine ⟨C₁ * s '' S₁, hC₁c.mul (hS₁c.image hs_cont), fun z hz => ?_⟩
  have hzpos : 0 < NumberField.TateGlobal.ideleNorm F z := NumberField.TateGlobal.ideleNorm_pos (F := F) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨NumberField.TateGlobal.ideleNorm F z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : NumberField.TateGlobal.ideleNorm F (s r) = NumberField.TateGlobal.ideleNorm F z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles F := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv', hsr,
      mul_inv_cancel₀ hzpos.ne']
  have hκ' := hC₁ _ hz₁
  obtain ⟨η, κ, hκ, hzκ⟩ := hκ'
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

private theorem exists_sup_function (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) {C : Set (AdeleRing (𝓞 F) F)ˣ} (hC : IsCompact C) :
    ∃ Fs : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℝ, Continuous Fs ∧ HasCompactSupport Fs ∧ (∀ g, 0 ≤ Fs g) ∧
      ∀ g, ∀ c ∈ C, ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖ ≤ Fs g := by
  classical
  have hKc : IsCompact (tsupport f) := hfc
  set Fs : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℝ :=
    fun g => sSup ((fun c => ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖) '' C) with hFs
  have hcont : Continuous Fs :=
    hC.continuous_sSup
      (continuous_norm.comp (hf.comp (continuous_fst.mul (continuous_centralScalar.comp continuous_snd))))
  have hbdd : ∀ g, BddAbove ((fun c => ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖) '' C) := fun g =>
    (hC.image (continuous_norm.comp (hf.comp (continuous_const.mul continuous_centralScalar)))).bddAbove
  have hle : ∀ g, ∀ c ∈ C, ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖ ≤ Fs g := fun g c hc =>
    le_csSup (hbdd g) ⟨c, hc, rfl⟩
  have hnn : ∀ g, 0 ≤ Fs g := by
    intro g
    by_cases hne : ((fun c => ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖) '' C).Nonempty
    · obtain ⟨_, ⟨c, hc, rfl⟩⟩ := hne
      exact le_trans (norm_nonneg _) (hle g c hc)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      show 0 ≤ sSup _
      rw [hne, Real.sSup_empty]
  have hsupp : HasCompactSupport Fs := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hKc.mul ((hC.image continuous_centralScalar).inv)) ?_
    intro g hg
    by_contra hgK
    apply hg
    have h0 : ∀ c ∈ C, ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖ = 0 := by
      intro c hc
      rw [norm_eq_zero]
      by_contra hne
      apply hgK
      exact Set.mem_mul.mpr ⟨g * AutomorphicForm.centralScalar (𝓞 F) F c, subset_tsupport f hne,
        (AutomorphicForm.centralScalar (𝓞 F) F c)⁻¹, Set.inv_mem_inv.mpr ⟨c, hc, rfl⟩, mul_inv_cancel_right _ _⟩
    refine le_antisymm ?_ (hnn g)
    by_cases hne : ((fun c => ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖) '' C).Nonempty
    · exact csSup_le hne (by rintro _ ⟨c, hc, rfl⟩; exact (h0 c hc).le)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      show sSup _ ≤ 0
      rw [hne, Real.sSup_empty]
  exact ⟨Fs, hcont, hsupp, hnn, hle⟩

private theorem finsum_enorm_princ_mul (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (a : Fˣ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ) :
    ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * c) * x))‖ₑ =
      ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ₑ := by
  rw [← finsum_mem_ellipticCell_scalar_mul (fun γ : GL (Fin 2) F => ‖f (x⁻¹ *
    AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ₑ) a]
  exact finsum_mem_congr rfl fun γ _ => by simp only [kernelSummand_scalar_mul f a γ x c]

private theorem finsum_enorm_le_enorm_ellipticPart (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
    (Fs : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℝ) (hFss : HasCompactSupport Fs) (hnn : ∀ g, 0 ≤ Fs g)
    {C : Set (AdeleRing (𝓞 F) F)ˣ}
    (hle : ∀ g, ∀ c ∈ C, ‖f (g * AutomorphicForm.centralScalar (𝓞 F) F c)‖ ≤ Fs g)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) {c : (AdeleRing (𝓞 F) F)ˣ} (hc : c ∈ C) :
    ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ₑ ≤
      ‖AutomorphicForm.adelicKernelEllipticPart F (fun g => (Fs g : ℂ)) x x‖ₑ := by
  classical
  set fF : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ := fun g => (Fs g : ℂ) with hfF
  have hfFc : HasCompactSupport fF := hFss.comp_left Complex.ofReal_zero
  have hfin := finite_support_kernel_summand F fF hfFc x x
  set T : Finset (GL (Fin 2) F) := hfin.toFinset.filter (· ∈ AutomorphicForm.ellipticCell F) with hT
  have hbound : ∀ γ : GL (Fin 2) F,
      ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ ≤
        Fs (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x) := by
    intro γ
    rw [inv_mul_mul_centralScalar_mul]
    exact hle _ c hc
  have hL : ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F,
      ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ₑ =
      ∑ γ ∈ T, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F c * x))‖ₑ := by
    rw [finsum_mem_eq_sum_of_subset _ (t := T) ?_ ?_]
    · rintro γ ⟨hγe, hγs⟩
      rw [Finset.mem_coe, hT, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨?_, hγe⟩
      show fF (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x) ≠ 0
      have h2 : f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
          (AutomorphicForm.centralScalar (𝓞 F) F c * x)) ≠ 0 := enorm_ne_zero.mp hγs
      have h3 := lt_of_lt_of_le (norm_pos_iff.mpr h2) (hbound γ)
      intro h0
      rw [hfF] at h0
      simp only [Complex.ofReal_eq_zero] at h0
      linarith
    · intro γ hγ
      rw [Finset.mem_coe, hT, Finset.mem_filter] at hγ
      exact hγ.2
  have hR : AutomorphicForm.adelicKernelEllipticPart F fF x x =
      ∑ γ ∈ T, fF (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x) := by
    show ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, fF (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x) = _
    rw [finsum_mem_eq_sum_of_subset _ (t := T) ?_ ?_]
    · rintro γ ⟨hγe, hγs⟩
      rw [Finset.mem_coe, hT, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hγs, hγe⟩
    · intro γ hγ
      rw [Finset.mem_coe, hT, Finset.mem_filter] at hγ
      exact hγ.2
  rw [hL, hR]
  have hsum : ‖∑ γ ∈ T, fF (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x)‖ₑ =
      ∑ γ ∈ T, ENNReal.ofReal (Fs (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x)) := by
    rw [hfF]
    dsimp only
    rw [← Complex.ofReal_sum, enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm,
      Real.enorm_of_nonneg (Finset.sum_nonneg fun γ _ => hnn _),
      ENNReal.ofReal_sum_of_nonneg fun γ _ => hnn _]
  rw [hsum]
  refine Finset.sum_le_sum fun γ _ => ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hbound γ)

private theorem lintegral_eq_setLIntegral_tsum_princ [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (G : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z ∂νZ = ∫⁻ z in Ω, ∑' a : Fˣ, G (princ F a * z) ∂νZ := by
  haveI := countable_range_principal (F := F)
  haveI := measurableConstSMul_principal F
  haveI := smulInvariantMeasure_principal F νZ
  have hmeas : ∀ g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range,
      AEMeasurable (fun x : (AdeleRing (𝓞 F) F)ˣ => G (g⁻¹ • x)) (νZ.restrict Ω) := fun g =>
    (hG.comp (measurable_const_smul g⁻¹)).aemeasurable
  rw [hΩ.lintegral_eq_tsum' G, ← lintegral_tsum hmeas]
  refine lintegral_congr fun z => ?_
  calc ∑' g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range, G (g⁻¹ • z)
      = ∑' g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range, G (g • z) :=
        (Equiv.inv _).tsum_eq fun g => G (g • z)
    _ = ∑' a : Fˣ, G (princ F a * z) :=
        ((MonoidHom.ofInjective (principal_injective (F := F))).toEquiv.tsum_eq fun g => G (g • z)).symm

private theorem enorm_finsum_mem_le {ι : Type*} (g : ι → ℂ) (s : Set ι) (hg : (s ∩ support g).Finite) :
    ‖∑ᶠ i ∈ s, g i‖ₑ ≤ ∑ᶠ i ∈ s, ‖g i‖ₑ := by
  classical
  rw [finsum_mem_eq_sum g hg, finsum_mem_eq_sum_of_subset _ (t := hg.toFinset) ?_ ?_]
  · exact enorm_sum_le _ _
  · intro i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨hi.1, enorm_ne_zero.mp hi.2⟩
  · intro i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
    exact hi.1

private theorem finsum_le_finsum_of_le {ι : Type*} (u v : ι → ℝ≥0∞) (hv : (support v).Finite) (h : ∀ i, u i ≤ v i) :
    ∑ᶠ i, u i ≤ ∑ᶠ i, v i := by
  classical
  have hu : support u ⊆ hv.toFinset := by
    intro i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact fun h0 => hi (le_antisymm (h0 ▸ h i) (zero_le : (0 : ℝ≥0∞) ≤ u i))
  have hv' : support v ⊆ hv.toFinset := by
    intro i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hi
  rw [finsum_eq_sum_of_support_subset u hu, finsum_eq_sum_of_support_subset v hv']
  exact Finset.sum_le_sum fun i _ => h i

private theorem finsum_mem_le_finsum_mem_of_subset {ι : Type*} (v : ι → ℝ≥0∞) {s t : Set ι} (hst : s ⊆ t)
    (ht : (t ∩ support v).Finite) :
    ∑ᶠ i ∈ s, v i ≤ ∑ᶠ i ∈ t, v i := by
  classical
  rw [finsum_mem_eq_sum v ht, finsum_mem_eq_sum_of_subset v (t := ht.toFinset.filter (· ∈ s)) ?_ ?_]
  · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hst hi.1, hi.2⟩, hi.1⟩
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    exact hi.2

private theorem enorm_char_mul_finsum_centralCell_eq (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ γ ∈ AutomorphicForm.centralCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ =
      ∑' a : Fˣ, ‖((ξ ⟨princ F a * z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ₑ *
        ‖f (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z))‖ₑ := by
  rw [finsum_mem_centralCell (fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
    (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ)]
  simp only [kernelSummand_scalar_eq]
  have hfin : (support fun a : Fˣ => ‖f (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z))‖ₑ).Finite := by
    refine ((finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)).preimage
      (glScalar_injective (K := F)).injOn).subset ?_
    intro a ha
    show f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
      (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ≠ 0
    rw [kernelSummand_scalar_eq]
    exact enorm_ne_zero.mp ha
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional _) hfin, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [char_princ_mul ξ hξt a z]

private theorem lintegral_enorm_char_mul_comp_centralScalar_lt_top [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫⁻ z, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖f (AutomorphicForm.centralScalar (𝓞 F) F z)‖ₑ ∂νZ < ⊤ := by
  have hint : Integrable (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 F) F z)) νZ :=
    (hξc.mul (hf.comp continuous_centralScalar)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_centralScalar f hfc).mul_left
  have h := hasFiniteIntegral_iff_enorm.mp hint.2
  simpa only [enorm_mul] using h

private theorem lintegral_lintegral_elliptic_lt_top (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F,
          ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  classical
  haveI := borelSpace_adelicGL2 F
  haveI := secondCountableTopology_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_ideles (F := F)
  haveI := isHaarMeasure_adelicGL2 F
  haveI := countable_range_principal (F := F)
  haveI := measurableConstSMul_principal F
  haveI := smulInvariantMeasure_principal F νZ
  set E : AutomorphicForm.AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun x z =>
    ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F,
      ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ with hE
  set ξe : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun z => ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ with hξe
  have hEcont : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ => E p.1 p.2 :=
    continuous_finsum_mem_orbit_comp (fun w : ℂ => ‖w‖ₑ) enorm_zero continuous_enorm f hf hfc _
  have hξecont : Continuous ξe := continuous_enorm.comp hξc

  have hKc : IsCompact (tsupport f) := hfc
  obtain ⟨m₀, hm₀, hlo⟩ : ∃ m₀ > 0, ∀ g ∈ tsupport f,
      m₀ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨g₀, -, hmin⟩ :=
        hKc.exists_isMinOn hne (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn
      exact ⟨_, NumberField.TateGlobal.ideleNorm_pos (F := F) _, fun g hg => hmin hg⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun g hg => by rw [hne] at hg; exact absurd hg (Set.notMem_empty g)⟩
  obtain ⟨M₀, hM₀pos, hhi⟩ : ∃ M₀, m₀ ≤ M₀ ∧ ∀ g ∈ tsupport f,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M₀ := by
    obtain ⟨M, hM⟩ := (hKc.image (NumberField.TateGlobal.continuous_ideleNorm_det F)).bddAbove
    exact ⟨max M m₀, le_max_right _ _, fun g hg => le_max_of_le_left (hM ⟨g, hg, rfl⟩)⟩
  set m₁ : ℝ := Real.sqrt m₀ with hm₁
  set M₁ : ℝ := Real.sqrt M₀ with hM₁
  have hm₁pos : 0 < m₁ := Real.sqrt_pos.mpr hm₀
  have hM₁pos : 0 < M₁ := Real.sqrt_pos.mpr (lt_of_lt_of_le hm₀ hM₀pos)
  set R : Set (AdeleRing (𝓞 F) F)ˣ := {z | NumberField.TateGlobal.ideleNorm F z ∈ Set.Icc m₁ M₁} with hR
  have hRmeas : MeasurableSet R :=
    (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm F)).measurableSet
  have hEoff : ∀ x z, z ∉ R → E x z = 0 := by
    intro x z hz
    refine finsum_mem_of_eqOn_zero fun γ _ => ?_
    show ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ = 0
    rw [enorm_eq_zero]
    by_contra hne
    exact hz (mem_Icc_sqrt_of_sq_mem_Icc (NumberField.TateGlobal.ideleNorm_pos (F := F) z).le
      (ideleNorm_sq_mem_of_kernel_ne_zero f hlo hhi γ x z hne))

  obtain ⟨Cξ, hCξ, hξle⟩ := exists_forall_enorm_char_le ξ hξc hξt hm₁pos (M₁ := M₁)

  obtain ⟨CR, hCRc, hlift⟩ := exists_isCompact_forall_mem_exists_princ_mul (F := F) hm₁pos (M₁ := M₁)

  obtain ⟨Fs, hFsc, hFss, hFsnn, hFsle⟩ := exists_sup_function f hf hfc hCRc
  set fF : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ := fun g => (Fs g : ℂ) with hfF
  have hfFcont : Continuous fF := Complex.continuous_ofReal.comp hFsc
  have hfFsupp : HasCompactSupport fF := hFss.comp_left Complex.ofReal_zero
  have hchild := AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab F α β
    hα hαβ Φ hΦ fF hfFcont hfFsupp
  have hJF : ∫⁻ x in Φ, ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      < ⊤ := by
    have h : ∫⁻ x, ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ
        ∂(((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)).restrict Φ) < ⊤ := hchild.2
    rwa [Measure.restrict_restrict₀ hΦ.nullMeasurableSet, Set.inter_eq_left.mpr hΦs] at h

  have hEle : ∀ z ∈ R, ∀ x, E x z ≤ ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ := by
    intro z hz x
    obtain ⟨a, c, hc, rfl⟩ := hlift z hz
    show ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
      (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * c) * x))‖ₑ ≤ _
    rw [finsum_enorm_princ_mul f a x c]
    exact finsum_enorm_le_enorm_ellipticPart f Fs hFss hFsnn hFsle x hc

  have hνR : νZ (R ∩ Ω) < ⊤ := by
    obtain ⟨D, -, hD, hDint⟩ :=
      NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
        F νZ
    obtain ⟨k, hk⟩ := hDint 0
    have hD' : IsFundamentalDomain
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range D νZ := hD
    have hRinv : ∀ g : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range,
        (fun z => g • z) ⁻¹' R = R := by
      rintro ⟨_, a, rfl⟩
      ext z
      show NumberField.TateGlobal.ideleNorm F (princ F a * z) ∈ Set.Icc m₁ M₁ ↔
        NumberField.TateGlobal.ideleNorm F z ∈ Set.Icc m₁ M₁
      rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_princ, one_mul]
    rw [hΩ.measure_set_eq hD' hRmeas hRinv]
    set ε : ℝ := min m₁ M₁⁻¹ ^ k with hε
    have hεpos : 0 < ε := pow_pos (lt_min hm₁pos (inv_pos.mpr hM₁pos)) k
    have hRsub : R ⊆ {z | ε ≤ min (NumberField.TateGlobal.ideleNorm F z)
        (NumberField.TateGlobal.ideleNorm F z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm F z ^ (0 : ℝ)} := by
      intro z hz
      obtain ⟨h1, h2⟩ := hz
      have hn : 0 < NumberField.TateGlobal.ideleNorm F z := NumberField.TateGlobal.ideleNorm_pos (F := F) z
      show ε ≤ _
      rw [Real.rpow_zero, mul_one]
      refine pow_le_pow_left₀ (le_min hm₁pos.le (inv_pos.mpr hM₁pos).le) ?_ k
      exact le_min (le_trans (min_le_left _ _) h1) (le_trans (min_le_right _ _) (inv_anti₀ hn h2))
    calc νZ (R ∩ D) = (νZ.restrict D) R := (Measure.restrict_apply hRmeas).symm
      _ ≤ (νZ.restrict D) {z | ε ≤ min (NumberField.TateGlobal.ideleNorm F z)
          (NumberField.TateGlobal.ideleNorm F z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm F z ^ (0 : ℝ)} :=
          measure_mono hRsub
      _ < ⊤ := Integrable.measure_ge_lt_top hk hεpos

  have hswap : ∫⁻ x in Φ, ∫⁻ z in Ω, ξe z * E x z ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ z in Ω, ∫⁻ x in Φ, ξe z * E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∂νZ :=
    lintegral_lintegral_swap ((hξecont.comp continuous_snd).measurable.mul hEcont.measurable).aemeasurable
  have hinner : ∀ z, ∫⁻ x in Φ, ξe z * E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ξe z * ∫⁻ x in Φ, E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := fun z =>
    lintegral_const_mul _ (hEcont.comp (continuous_id.prodMk continuous_const)).measurable
  have hbound : ∀ z, ξe z * ∫⁻ x in Φ, E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤
      R.indicator (fun _ => Cξ * ∫⁻ x in Φ, ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) z := by
    intro z
    by_cases hz : z ∈ R
    · rw [Set.indicator_of_mem hz]
      exact mul_le_mul' (hξle z hz) (lintegral_mono fun x => hEle z hz x)
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∫⁻ x in Φ, E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          ∫⁻ x in Φ, (0 : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        lintegral_congr fun x => hEoff x z hz
      rw [h0, lintegral_zero, mul_zero]
  calc ∫⁻ x in Φ, ∫⁻ z in Ω, ξe z * E x z ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫⁻ z in Ω, ξe z * ∫⁻ x in Φ, E x z ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∂νZ := by
        rw [hswap]
        exact lintegral_congr hinner
    _ ≤ ∫⁻ z in Ω, R.indicator (fun _ => Cξ * ∫⁻ x in Φ,
          ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) z ∂νZ :=
        lintegral_mono hbound
    _ = Cξ * (∫⁻ x in Φ, ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) *
          νZ (R ∩ Ω) := by
        rw [lintegral_indicator_const hRmeas, Measure.restrict_apply hRmeas]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCξ.lt_top hJF) hνR

private theorem lintegral_lintegral_abs_lt_top (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
          ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  classical
  haveI := borelSpace_adelicGL2 F
  haveI := secondCountableTopology_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_ideles (F := F)
  set G : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun z =>
    ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖f (AutomorphicForm.centralScalar (𝓞 F) F z)‖ₑ with hG
  have hGmeas : Measurable G :=
    (continuous_enorm.comp hξc).measurable.mul (continuous_enorm.comp (hf.comp continuous_centralScalar)).measurable
  have hC₀ : ∫⁻ z, G z ∂νZ < ⊤ := lintegral_enorm_char_mul_comp_centralScalar_lt_top νZ ξ hξc f hf hfc
  have hcen : ∀ x, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ γ ∈ AutomorphicForm.centralCell F,
      ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ =
      ∫⁻ z, G z ∂νZ := by
    intro x
    rw [lintegral_eq_setLIntegral_tsum_princ νZ Ω hΩ G hGmeas]
    exact lintegral_congr fun z => enorm_char_mul_finsum_centralCell_eq ξ hξt f hfc x z
  have hmeasA : ∀ x, Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ γ ∈ AutomorphicForm.centralCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ := by
    intro x
    exact (continuous_enorm.comp hξc).measurable.mul (continuous_finsum_mem_orbit_comp_snd
      (fun w : ℂ => ‖w‖ₑ) enorm_zero continuous_enorm f hf hfc (AutomorphicForm.centralCell F) x).measurable
  have hsplit : ∀ x z, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
      ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ =
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ γ ∈ AutomorphicForm.centralCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ +
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ := by
    intro x z
    rw [finsum_mem_union' disjoint_centralCell_ellipticCell
      ((finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)).subset
        fun γ hγ => enorm_ne_zero.mp hγ.2)
      ((finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)).subset
        fun γ hγ => enorm_ne_zero.mp hγ.2), mul_add]
  have hμΦ : adelicGLHaar (Fin 2) (𝓞 F) F Φ < ⊤ := by
    have h := (isFiniteMeasure_restrict_of_isFundamentalDomain_band α β hα hαβ Φ hΦs hΦ).measure_univ_lt_top
    rwa [Measure.restrict_apply_univ] at h
  calc ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
          ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫⁻ x in Φ, ((∫⁻ z, G z ∂νZ) + ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        refine lintegral_congr fun x => ?_
        rw [← hcen x, ← lintegral_add_left (hmeasA x)]
        exact lintegral_congr fun z => hsplit x z
    _ = (∫⁻ z, G z ∂νZ) * adelicGLHaar (Fin 2) (𝓞 F) F Φ +
        ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hC₀ hμΦ,
        lintegral_lintegral_elliptic_lt_top α β hα hαβ Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt f hf hfc⟩

private theorem integrable_prod_family (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (γ₀ : GL (Fin 2) F) (hγ₀ : γ₀ ∈ R) :
    Integrable (fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ p.1 p.2)
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ).prod νZ) := by
  classical
  haveI := borelSpace_adelicGL2 F
  haveI := secondCountableTopology_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_ideles (F := F)
  haveI := isHaarMeasure_adelicGL2 F
  have hcont : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ p.1 p.2 :=
    (hξc.comp continuous_snd).mul (continuous_orbitSum f hf hfc γ₀)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hmeasP : AEMeasurable (fun p : AutomorphicForm.AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ‖((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ p.1 p.2‖ₑ)
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ).prod νZ) :=
    (continuous_enorm.comp hcont).measurable.aemeasurable
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeasP]
  have hstabfin : (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀).Finite :=
    finite_scalarStab γ₀
  haveI : Finite (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀) :=
    hstabfin.to_subtype
  set N : ℝ≥0∞ :=
    (Nat.card (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀) : ℝ≥0∞) with hN
  have hcell : γ₀ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F := hRsub hγ₀

  have hpt : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ),
      ∑' a : Fˣ, ‖((ξ ⟨princ F a * z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x (princ F a * z)‖ₑ ≤
        N * (‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) := by
    intro x z
    have hT : (support fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ).Finite :=
      (finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)).subset
        fun γ hγ => enorm_ne_zero.mp hγ
    have hfin1 : (support fun a : Fˣ => ‖orbitSum F f γ₀ x (princ F a * z)‖ₑ).Finite :=
      (finite_support_orbitSum_princ f hfc γ₀ x z).subset fun a ha => enorm_ne_zero.mp ha
    have hv_fin : (support fun a : Fˣ => ∑ᶠ γ' ∈ conjOrbit γ₀,
        ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') *
          (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ).Finite := by
      have hW : (scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀ ∩
          support fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ).Finite := hT.inter_of_right _
      have hfinU : (⋃ w ∈ (scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀ ∩
          support fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ),
          Prod.fst '' scalarFibre (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀ w).Finite := by
        refine hW.biUnion fun w hw => ?_
        obtain ⟨h, a, rfl⟩ := hw.1
        haveI : Finite (scalarFibre (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀
            (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))) :=
          Finite.of_equiv _ (fibreEquiv scalar_mem_center a ⟨h, rfl⟩)
        exact (Set.toFinite _).image Prod.fst
      refine hfinU.subset ?_
      · intro a ha
        rw [Function.mem_support] at ha
        obtain ⟨γ', hγ'⟩ : ∃ γ' ∈ conjOrbit γ₀,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') *
              (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ≠ 0 := by
          by_contra hcon
          simp only [not_exists, not_and, not_not] at hcon
          exact ha (finsum_mem_of_eqOn_zero fun γ' hγ' => hcon γ' hγ')
        obtain ⟨⟨h, rfl⟩, hne⟩ := hγ'
        exact Set.mem_biUnion (x := Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
          ⟨⟨h, a, rfl⟩, hne⟩ ⟨(a, h⁻¹ * γ₀ * h), ⟨⟨h, rfl⟩, rfl⟩, rfl⟩
    have key := finsum_finsum_mem_orbit_eq_finsum_mem_family_nsmul (γ₀ := γ₀) scalar_mem_center
      (fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) (hT.inter_of_right _)
    calc ∑' a : Fˣ, ‖((ξ ⟨princ F a * z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x (princ F a * z)‖ₑ
        = ∑' a : Fˣ, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖orbitSum F f γ₀ x (princ F a * z)‖ₑ :=
          tsum_congr fun a => by rw [enorm_mul, char_princ_mul ξ hξt]
      _ = ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑' a : Fˣ, ‖orbitSum F f γ₀ x (princ F a * z)‖ₑ :=
          ENNReal.tsum_mul_left
      _ = ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ a : Fˣ, ‖orbitSum F f γ₀ x (princ F a * z)‖ₑ := by
          rw [tsum_eq_finsum (L := SummationFilter.unconditional _) hfin1]
      _ ≤ ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ∑ᶠ a : Fˣ, ∑ᶠ γ' ∈ conjOrbit γ₀,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') *
              (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ := by
          refine mul_le_mul_right (finsum_le_finsum_of_le _ _ hv_fin fun a => ?_) _
          have h1 : orbitSum F f γ₀ x (princ F a * z) = ∑ᶠ γ' ∈ conjOrbit γ₀,
              f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ') *
                (AutomorphicForm.centralScalar (𝓞 F) F z * x)) := by
            show ∑ᶠ γ' ∈ conjOrbit γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
              (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * z) * x)) = _
            exact finsum_mem_congr rfl fun γ' _ => (kernelSummand_scalar_mul f a γ' x z).symm
          rw [h1]
          exact enorm_finsum_mem_le _ _
            (((finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F z * x)).preimage
              (mul_right_injective (Matrix.GeneralLinearGroup.scalar (Fin 2) a)).injOn).inter_of_right _)
      _ = ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
            ∑ᶠ γ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀,
              Nat.card (scalarStab (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀) •
                ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
                  (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ := by
          rw [key]
      _ = ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * (N *
            ∑ᶠ γ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀,
              ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
                (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) := by
          rw [mul_finsum_mem (fun γ : GL (Fin 2) F => ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) N]
          simp only [nsmul_eq_mul, hN]
      _ ≤ ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * (N *
            ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
              ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
                (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) := by
          refine mul_le_mul_right (mul_le_mul_right
            (finsum_mem_le_finsum_mem_of_subset _ ?_ (hT.inter_of_right _)) _) _
          rintro γ ⟨h, a, rfl⟩
          rcases hcell with hc | he
          · exact Or.inl (scalar_mul_conj_mem_centralCell hc a h)
          · exact Or.inr (scalar_mul_conj_mem_ellipticCell he a h)
      _ = N * (‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
            ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
              ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
                (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ) := by
          rw [mul_left_comm]
  have hmeasG : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 F) F, Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x z‖ₑ := fun x =>
    ((continuous_enorm.comp hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hmeasA : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 F) F, Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
          ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ := by
    intro x
    exact (continuous_enorm.comp hξc).measurable.mul (continuous_finsum_mem_orbit_comp_snd
      (fun w : ℂ => ‖w‖ₑ) enorm_zero continuous_enorm f hf hfc
      (AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F) x).measurable
  have hinner : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      ∫⁻ z, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x z‖ₑ ∂νZ ≤
        N * ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ *
              (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ := by
    intro x
    rw [lintegral_eq_setLIntegral_tsum_princ νZ Ω hΩ _ (hmeasG x), ← lintegral_const_mul _ (hmeasA x)]
    exact lintegral_mono fun z => hpt x z
  calc ∫⁻ x in Φ, ∫⁻ z, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x z‖ₑ ∂νZ
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ ∫⁻ x in Φ, N * ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_mono hinner
    _ = N * ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
          ∑ᶠ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F,
            ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_const_mul' N _ (ENNReal.natCast_ne_top _)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top
        (lintegral_lintegral_abs_lt_top α β hα hαβ Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt f hf hfc)

private theorem integrableOn_centralizerDomain (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (_hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (γ₀ : GL (Fin 2) F) (hγ₀ : γ₀ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hΨs : Ψ ⊆ normBand F α β)
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (w : (AdeleRing (𝓞 F) F)ˣ) :
    IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ * (AutomorphicForm.centralScalar (𝓞 F) F w * x))) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
  classical
  haveI := borelSpace_adelicGL2 F
  haveI := secondCountableTopology_adelicGL2 (F := F)
  haveI := sigmaCompactSpace_adelicGL2 (F := F)
  haveI := countable_range_globalPoints (F := F)
  haveI := measurableConstSMul_globalPoints F
  haveI := smulInvariantMeasure_band_globalPoints F α β
  have hTcont : Continuous (kernelTerm f γ₀ w) := continuous_kernelTerm f hf γ₀ w
  show IntegrableOn (kernelTerm f γ₀ w) Ψ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))
  refine ⟨hTcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rcases hγ₀ with hc | he
  · obtain ⟨a, rfl⟩ := (mem_centralCell_iff_exists_scalar γ₀).mp hc
    have hΨ' : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Ψ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
      have h := hΨ
      rwa [Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (scalar_mem_center a)),
        ← MonoidHom.range_eq_map] at h
    have hμΨ : adelicGLHaar (Fin 2) (𝓞 F) F Ψ < ⊤ := by
      have h := (isFiniteMeasure_restrict_of_isFundamentalDomain_band α β hα hαβ Ψ hΨs hΨ').measure_univ_lt_top
      rwa [Measure.restrict_apply_univ] at h
    rw [Measure.restrict_restrict₀ hΨ.nullMeasurableSet, Set.inter_eq_left.mpr hΨs]
    calc ∫⁻ x in Ψ, ‖kernelTerm f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w x‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∫⁻ x in Ψ, ‖f (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * w))‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          refine lintegral_congr fun x => ?_
          show ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
            (AutomorphicForm.centralScalar (𝓞 F) F w * x))‖ₑ = _
          rw [kernelSummand_scalar_eq]
      _ = ‖f (AutomorphicForm.centralScalar (𝓞 F) F (princ F a * w))‖ₑ * adelicGLHaar (Fin 2) (𝓞 F) F Ψ :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hμΨ
  · have hCΓ : (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F) ≤
        (AutomorphicForm.globalPoints (𝓞 F) F).range :=
      Subgroup.map_le_range _ _
    have hΨ' := isFundamentalDomain_subgroupOf hCΓ hΨ
    have h4 := ae_forall_existsUnique_smul_mem _ hΨ'
    obtain ⟨Fs, hFsc, hFss, hFsnn, hFsle⟩ := exists_sup_function f hf hfc (isCompact_singleton (x := w))
    set fF : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ := fun g => (Fs g : ℂ) with hfF
    have hfFcont : Continuous fF := Complex.continuous_ofReal.comp hFsc
    have hfFsupp : HasCompactSupport fF := hFss.comp_left Complex.ofReal_zero
    have hchild := AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab F α β
      hα hαβ Φ hΦ fF hfFcont hfFsupp
    have hJF : ∫⁻ x in Φ, ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ
        ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) < ⊤ := hchild.2
    have hgΨ : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range, NullMeasurableSet (g • Ψ)
        (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)).restrict Φ) := fun g =>
      (hΨ.nullMeasurableSet.smul g).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    rw [← lintegral_indicator₀ hΨ.nullMeasurableSet,
      hΦ.lintegral_eq_tsum' (Ψ.indicator fun y => ‖kernelTerm f γ₀ w y‖ₑ)]
    have hterm : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        (fun x => Ψ.indicator (fun y => ‖kernelTerm f γ₀ w y‖ₑ) (g⁻¹ • x)) =
          fun x => (g • Ψ).indicator (fun y => ‖kernelTerm f γ₀ w (g⁻¹ • y)‖ₑ) x := by
      intro g
      funext x
      simp only [Set.indicator, Set.mem_smul_set_iff_inv_smul_mem]
    simp_rw [hterm]
    have hmeas : ∀ g : (AutomorphicForm.globalPoints (𝓞 F) F).range,
        AEMeasurable (fun x => (g • Ψ).indicator (fun y => ‖kernelTerm f γ₀ w (g⁻¹ • y)‖ₑ) x)
          (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)).restrict Φ) := fun g =>
      (((continuous_enorm.comp hTcont).measurable.comp (measurable_const_smul g⁻¹)).aemeasurable).indicator₀
        (hgΨ g)
    rw [← lintegral_tsum hmeas]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hJF
    refine (ae_restrict_of_ae h4).mono fun x hx => ?_
    rw [tsum_indicator_comp_kernelTerm_eq_finsum_orbit (fun c : ℂ => ‖c‖ₑ) enorm_zero f hfc γ₀ Ψ w x hx]
    calc ∑ᶠ γ' ∈ conjOrbit γ₀, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
          (AutomorphicForm.centralScalar (𝓞 F) F w * x))‖ₑ
        ≤ ∑ᶠ γ' ∈ AutomorphicForm.ellipticCell F, ‖f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ' *
            (AutomorphicForm.centralScalar (𝓞 F) F w * x))‖ₑ := by
          refine finsum_mem_le_finsum_mem_of_subset _ ?_
            ((finite_support_kernel_summand F f hfc x (AutomorphicForm.centralScalar (𝓞 F) F w * x)).subset
              (fun γ hγ => enorm_ne_zero.mp hγ) |>.inter_of_right _)
          rintro _ ⟨h, rfl⟩
          have := scalar_mul_conj_mem_ellipticCell he 1 h
          simpa only [map_one, one_mul] using this
      _ ≤ ‖AutomorphicForm.adelicKernelEllipticPart F fF x x‖ₑ :=
          finsum_enorm_le_enorm_ellipticPart f Fs hFss hFsnn hFsle x (Set.mem_singleton w)

end MeasureGlue

section UniformFiniteness

section Classification

variable {K : Type*} [Field K]

private theorem isRoot_charpoly_of_trace_eq_of_det_eq (M : Matrix (Fin 2) (Fin 2) K) (c : K) (htr : M.trace = 2 * c)
    (hdet : M.det = c ^ 2) : M.charpoly.IsRoot c := by
  rw [Matrix.charpoly_fin_two]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, htr, hdet]
  ring

private theorem trace_smul_one_fin_two (c : K) : (c • (1 : Matrix (Fin 2) (Fin 2) K)).trace = 2 * c := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

private theorem det_smul_one_fin_two (c : K) : (c • (1 : Matrix (Fin 2) (Fin 2) K)).det = c ^ 2 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

private theorem ne_smul_one_of_mem_ellipticCell {γ : GL (Fin 2) K} (hγ : γ ∈ AutomorphicForm.ellipticCell K) (c : K) :
    (γ : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro h
  have hγ' : AutomorphicForm.IsEllipticType (γ : Matrix (Fin 2) (Fin 2) K) := hγ
  refine hγ' c ?_
  rw [h]
  exact isRoot_charpoly_of_trace_eq_of_det_eq _ c (trace_smul_one_fin_two c) (det_smul_one_fin_two c)

private theorem mem_family_of_mem_centralCell_of_mem_centralCell {γ γ' : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.centralCell K) (hγ' : γ' ∈ AutomorphicForm.centralCell K) :
    γ' ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) γ := by
  obtain ⟨a, rfl⟩ := (mem_centralCell_iff_exists_scalar γ).mp hγ
  obtain ⟨a', rfl⟩ := (mem_centralCell_iff_exists_scalar γ').mp hγ'
  refine ⟨1, a' * a⁻¹, ?_⟩
  rw [inv_one, one_mul, mul_one, ← map_mul, inv_mul_cancel_right]

private theorem not_mem_ellipticCell_of_trace_eq_of_det_eq {γ γ' : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.centralCell K)
    (htr : (γ : Matrix (Fin 2) (Fin 2) K).trace = (γ' : Matrix (Fin 2) (Fin 2) K).trace)
    (hdet : (γ : Matrix (Fin 2) (Fin 2) K).det = (γ' : Matrix (Fin 2) (Fin 2) K).det) :
    γ' ∉ AutomorphicForm.ellipticCell K := by
  obtain ⟨c, hc⟩ := hγ
  intro hγ'
  have h' : AutomorphicForm.IsEllipticType (γ' : Matrix (Fin 2) (Fin 2) K) := hγ'
  refine h' c (isRoot_charpoly_of_trace_eq_of_det_eq _ c ?_ ?_)
  · rw [← htr, hc, trace_smul_one_fin_two]
  · rw [← hdet, hc, det_smul_one_fin_two]

private theorem mem_family_of_trace_eq_of_det_eq {γ γ' : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hγ' : γ' ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (htr : (γ : Matrix (Fin 2) (Fin 2) K).trace = (γ' : Matrix (Fin 2) (Fin 2) K).trace)
    (hdet : (γ : Matrix (Fin 2) (Fin 2) K).det = (γ' : Matrix (Fin 2) (Fin 2) K).det) :
    γ' ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) γ := by
  rcases hγ with hc | he
  · rcases hγ' with hc' | he'
    · exact mem_family_of_mem_centralCell_of_mem_centralCell hc hc'
    · exact absurd he' (not_mem_ellipticCell_of_trace_eq_of_det_eq hc htr hdet)
  · rcases hγ' with hc' | he'
    · exact absurd he (not_mem_ellipticCell_of_trace_eq_of_det_eq hc' htr.symm hdet.symm)
    · obtain ⟨Q, hQ⟩ := LT.TwistedNorm.GL2.exists_conj_of_trace_eq_det_eq γ γ'
        (ne_smul_one_of_mem_ellipticCell he) (ne_smul_one_of_mem_ellipticCell he') htr hdet
      refine ⟨Q, 1, ?_⟩
      rw [map_one, one_mul]
      exact hQ

end Classification

section FamilyGlue

variable {G A : Type*} [Group G] [CommGroup A] {sc : A →* G}

private theorem mem_family_trans (hsc : ∀ a : A, sc a ∈ Subgroup.center G) {γ₀ γ γ' : G} (h : γ ∈ scalarFamily sc γ₀)
    (h' : γ' ∈ scalarFamily sc γ) : γ' ∈ scalarFamily sc γ₀ := by
  obtain ⟨h, a, rfl⟩ := h
  obtain ⟨k, b, rfl⟩ := h'
  have hcomm : ∀ g : G, g * sc a = sc a * g := Subgroup.mem_center_iff.mp (hsc a)
  refine ⟨h * k, a * b, ?_⟩
  calc sc b * (k⁻¹ * (sc a * (h⁻¹ * γ₀ * h)) * k)
      = sc b * (sc a * (k⁻¹ * (h⁻¹ * γ₀ * h) * k)) := by
        rw [← mul_assoc k⁻¹, hcomm k⁻¹, mul_assoc (sc a), mul_assoc (sc a)]
    _ = sc (a * b) * ((h * k)⁻¹ * γ₀ * (h * k)) := by
        rw [map_mul, mul_inv_rev, ← hcomm (sc b)]
        group

private theorem sc_mul_mem_family {γ₀ γ : G} (h : γ ∈ scalarFamily sc γ₀) (a : A) : sc a * γ ∈ scalarFamily sc γ₀ := by
  obtain ⟨h, b, rfl⟩ := h
  exact ⟨h, a * b, by rw [map_mul, mul_assoc (sc a) (sc b)]⟩

end FamilyGlue

section Invariants

variable {F : Type} [Field F] [NumberField F]

private theorem val_globalPoints_eq_map (γ : GL (Fin 2) F) :
    ((AutomorphicForm.globalPoints (𝓞 F) F γ : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      (γ : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (AdeleRing (𝓞 F) F)) :=
  rfl

private theorem trace_val_globalPoints (γ : GL (Fin 2) F) :
    Matrix.trace ((AutomorphicForm.globalPoints (𝓞 F) F γ : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      algebraMap F (AdeleRing (𝓞 F) F) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F)) := by
  rw [val_globalPoints_eq_map]
  exact (AddMonoidHom.map_trace (algebraMap F (AdeleRing (𝓞 F) F)) _).symm

private theorem det_val_globalPoints (γ : GL (Fin 2) F) :
    Matrix.det ((AutomorphicForm.globalPoints (𝓞 F) F γ : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      algebraMap F (AdeleRing (𝓞 F) F) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) F)) := by
  rw [val_globalPoints_eq_map]
  exact ((algebraMap F (AdeleRing (𝓞 F) F)).map_det _).symm

private theorem trace_val_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    Matrix.trace ((x⁻¹ * g * x : AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]

private theorem det_val_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    Matrix.det ((x⁻¹ * g * x : AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))

private theorem inv_centralScalar_mul_kernel_arg (x g : AutomorphicForm.AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ) :
    (AutomorphicForm.centralScalar (𝓞 F) F c)⁻¹ * (x⁻¹ * g * (AutomorphicForm.centralScalar (𝓞 F) F c * x)) =
      x⁻¹ * g * x := by
  rw [inv_mul_mul_centralScalar_mul F x g c, ← centralScalar_mul_comm F c (x⁻¹ * g * x), inv_mul_cancel_left]

private theorem exists_finset_forall_eq_zero (α β : ℝ) (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f)
    (hfc : HasCompactSupport f) (R : Set (GL (Fin 2) F))
    (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    ∃ R₀ : Finset (GL (Fin 2) F), ↑R₀ ⊆ R ∧ ∀ γ₀ ∈ R, γ₀ ∉ R₀ → ∀ x ∈ normBand F α β,
      ∀ w : (AdeleRing (𝓞 F) F)ˣ,
        ∀ γ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀,
          f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * (AutomorphicForm.centralScalar (𝓞 F) F w * x)) = 0 := by
  classical
  have hKc : IsCompact (tsupport f) := hfc

  obtain ⟨m₀, hm₀, hlo⟩ : ∃ m₀ > 0, ∀ g ∈ tsupport f,
      m₀ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨g₀, -, hmin⟩ :=
        hKc.exists_isMinOn hne (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn
      exact ⟨_, NumberField.TateGlobal.ideleNorm_pos (F := F) _, fun g hg => hmin hg⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun g hg => by rw [hne] at hg; exact absurd hg (Set.notMem_empty g)⟩
  obtain ⟨M₀, -, hhi⟩ : ∃ M₀, m₀ ≤ M₀ ∧ ∀ g ∈ tsupport f,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M₀ := by
    obtain ⟨M, hM⟩ := (hKc.image (NumberField.TateGlobal.continuous_ideleNorm_det F)).bddAbove
    exact ⟨max M m₀, le_max_right _ _, fun g hg => le_max_of_le_left (hM ⟨g, hg, rfl⟩)⟩
  have hm₁pos : 0 < Real.sqrt m₀ := Real.sqrt_pos.mpr hm₀

  obtain ⟨C₁, hC₁c, hlift⟩ :=
    exists_isCompact_forall_mem_exists_princ_mul (F := F) (M₁ := Real.sqrt M₀) hm₁pos

  set Γ : Set (GL (Fin 2) F) := {γ₁ | ∃ x : AutomorphicForm.AdelicGL2 (𝓞 F) F, ∃ c ∈ C₁,
    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x)) ≠ 0}
    with hΓ

  have hcontM : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      (((AutomorphicForm.centralScalar (𝓞 F) F p.1)⁻¹ * p.2 : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Units.continuous_val.comp ((continuous_centralScalar.comp continuous_fst).inv.mul continuous_snd)
  set Tset : Set (AdeleRing (𝓞 F) F) := (fun p : (AdeleRing (𝓞 F) F)ˣ × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
    Matrix.trace (((AutomorphicForm.centralScalar (𝓞 F) F p.1)⁻¹ * p.2 : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) '' (C₁ ×ˢ tsupport f) with hTset
  set Dset : Set (AdeleRing (𝓞 F) F) := (fun p : (AdeleRing (𝓞 F) F)ˣ × AutomorphicForm.AdelicGL2 (𝓞 F) F =>
    Matrix.det (((AutomorphicForm.centralScalar (𝓞 F) F p.1)⁻¹ * p.2 : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) '' (C₁ ×ˢ tsupport f) with hDset
  have hTc : IsCompact Tset := (hC₁c.prod hKc).image hcontM.matrix_trace
  have hDc : IsCompact Dset := (hC₁c.prod hKc).image hcontM.matrix_det
  have hT₀ := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F hTc
  have hD₀ := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F hDc

  have hinv : ∀ γ₁ ∈ Γ, Matrix.trace (γ₁ : Matrix (Fin 2) (Fin 2) F) ∈
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ Tset} ∧
      Matrix.det (γ₁ : Matrix (Fin 2) (Fin 2) F) ∈ {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ Dset} := by
    rintro γ₁ ⟨x, c, hc, hne⟩
    have hmem : x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x) ∈
        tsupport f := subset_tsupport f hne
    constructor
    · show algebraMap F (AdeleRing (𝓞 F) F) (Matrix.trace (γ₁ : Matrix (Fin 2) (Fin 2) F)) ∈ Tset
      refine ⟨(c, x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x)),
        ⟨hc, hmem⟩, ?_⟩
      show Matrix.trace (((AutomorphicForm.centralScalar (𝓞 F) F c)⁻¹ *
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x)) :
          AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
      rw [inv_centralScalar_mul_kernel_arg, trace_val_conj, trace_val_globalPoints]
    · show algebraMap F (AdeleRing (𝓞 F) F) (Matrix.det (γ₁ : Matrix (Fin 2) (Fin 2) F)) ∈ Dset
      refine ⟨(c, x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x)),
        ⟨hc, hmem⟩, ?_⟩
      show Matrix.det (((AutomorphicForm.centralScalar (𝓞 F) F c)⁻¹ *
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₁ * (AutomorphicForm.centralScalar (𝓞 F) F c * x)) :
          AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
      rw [inv_centralScalar_mul_kernel_arg, det_val_conj, det_val_globalPoints]

  set Rc : Set (GL (Fin 2) F) := {γ₀ | γ₀ ∈ R ∧ ∃ γ₁ ∈ Γ,
    γ₁ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀} with hRc
  have hcells : ∀ γ₀ ∈ R, ∀ γ₁ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀,
      γ₁ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F := by
    rintro γ₀ hγ₀ γ₁ ⟨h, a, rfl⟩
    rcases hRsub hγ₀ with hc | he
    · exact Or.inl (scalar_mul_conj_mem_centralCell hc a h)
    · exact Or.inr (scalar_mul_conj_mem_ellipticCell he a h)
  have hRc_fin : Rc.Finite := by
    have hwit : ∀ γ₀ ∈ Rc, ∃ γ₁, γ₁ ∈ Γ ∧
        γ₁ ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀ := fun γ₀ h => h.2
    choose! wit hwitΓ hwitfam using hwit
    refine Set.Finite.of_finite_image (f := fun γ₀ => (Matrix.trace ((wit γ₀ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F), Matrix.det ((wit γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) ?_ ?_
    · refine (hT₀.prod hD₀).subset ?_
      rintro _ ⟨γ₀, hγ₀, rfl⟩
      exact ⟨(hinv _ (hwitΓ γ₀ hγ₀)).1, (hinv _ (hwitΓ γ₀ hγ₀)).2⟩
    · intro γ₀ hγ₀ γ₀' hγ₀' heq
      simp only [Prod.mk.injEq] at heq
      have h1 : wit γ₀' ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) (wit γ₀) :=
        mem_family_of_trace_eq_of_det_eq (hcells γ₀ hγ₀.1 _ (hwitfam γ₀ hγ₀))
          (hcells γ₀' hγ₀'.1 _ (hwitfam γ₀' hγ₀')) heq.1 heq.2
      have h2 : wit γ₀' ∈ scalarFamily (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) γ₀ :=
        mem_family_trans scalar_mem_center (hwitfam γ₀ hγ₀) h1
      obtain ⟨γs, -, huniq⟩ := hR (wit γ₀') (hcells γ₀' hγ₀'.1 _ (hwitfam γ₀' hγ₀'))
      exact (huniq γ₀ ⟨hγ₀.1, h2⟩).trans (huniq γ₀' ⟨hγ₀'.1, hwitfam γ₀' hγ₀'⟩).symm
  refine ⟨hRc_fin.toFinset, ?_, ?_⟩
  · intro γ₀ hγ₀
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hγ₀
    exact hγ₀.1
  · intro γ₀ hγ₀R hnot x _ w γ hγ
    by_contra hne
    have hw2 : NumberField.TateGlobal.ideleNorm F w ^ 2 ∈ Set.Icc m₀ M₀ :=
      ideleNorm_sq_mem_of_kernel_ne_zero f hlo hhi γ x w hne
    have hw : NumberField.TateGlobal.ideleNorm F w ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
      mem_Icc_sqrt_of_sq_mem_Icc (NumberField.TateGlobal.ideleNorm_pos (F := F) w).le hw2
    obtain ⟨a, c, hc, rfl⟩ := hlift w hw
    have hne' : f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ) *
        (AutomorphicForm.centralScalar (𝓞 F) F c * x)) ≠ 0 := by
      rw [kernelSummand_scalar_mul f a γ x c]
      exact hne
    refine hnot (hRc_fin.mem_toFinset.mpr ⟨hγ₀R, Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ, ⟨x, c, hc, hne'⟩,
      sc_mul_mem_family hγ a⟩)

end Invariants

end UniformFiniteness

end GeoEllUnfolding

open AutomorphicForm

noncomputable section

namespace CentralEllipticUnfolding

variable (F : Type) [Field F] [NumberField F]

private def orbitSet (γ₀ : GL (Fin 2) F) : Set (GL (Fin 2) F) :=
  {γ' | ∃ h : GL (Fin 2) F, γ' = h⁻¹ * γ₀ * h}

private def familySet (γ₀ : GL (Fin 2) F) : Set (GL (Fin 2) F) :=
  {γ | ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)}

private def stabCard (γ₀ : GL (Fin 2) F) : ℂ :=
  ((Nat.card {a : Fˣ // ∃ h : GL (Fin 2) F,
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)

private def orbitSum (f : AdelicGL2 (𝓞 F) F → ℂ) (γ₀ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F)
    (w : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ∑ᶠ γ' ∈ orbitSet F γ₀, f (x⁻¹ * globalPoints (𝓞 F) F γ' * (centralScalar (𝓞 F) F w * x))

private def princ (a : Fˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a

private def normBand (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

omit [NumberField F] in

private theorem orbitSet_subset_familySet (γ₀ : GL (Fin 2) F) : orbitSet F γ₀ ⊆ familySet F γ₀ := by
  rintro γ' ⟨h, rfl⟩
  exact ⟨h, 1, by rw [map_one, one_mul]⟩

omit [NumberField F] in

private theorem self_mem_familySet (γ₀ : GL (Fin 2) F) : γ₀ ∈ familySet F γ₀ :=
  ⟨1, 1, by rw [map_one, one_mul, inv_one, one_mul, mul_one]⟩

variable {F}

private theorem sigmaCompactSpace_adelicGL2 : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := by
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).symm.isClosedEmbedding
      |>.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem sigmaCompactSpace_ideles : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 F) F)).symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem _root_.CentralEllipticUnfolding.continuous_orbitSum (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F) :
    Continuous fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ => orbitSum F f γ₀ p.1 p.2 := by
  exact GeoEllUnfolding.continuous_orbitSum f hf hfc γ₀

p2m_export "CentralEllipticUnfolding" "continuous_orbitSum"

private theorem _root_.CentralEllipticUnfolding.kernelParts_eq_finsum_families (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ centralCell F ∪ ellipticCell F)
    (hR : ∀ γ ∈ centralCell F ∪ ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (x : AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    adelicKernelCentralPart F f x (centralScalar (𝓞 F) F z * x) +
        adelicKernelEllipticPart F f x (centralScalar (𝓞 F) F z * x) =
      ∑ᶠ γ₀ ∈ R, (stabCard F γ₀)⁻¹ * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) := by
  exact GeoEllUnfolding.kernelParts_eq_finsum_families f hfc R hRsub hR x z

p2m_export "CentralEllipticUnfolding" "kernelParts_eq_finsum_families"

private theorem _root_.CentralEllipticUnfolding.exists_finset_forall_eq_zero (α β : ℝ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ centralCell F ∪ ellipticCell F)
    (hR : ∀ γ ∈ centralCell F ∪ ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    ∃ R₀ : Finset (GL (Fin 2) F), ↑R₀ ⊆ R ∧ ∀ γ₀ ∈ R, γ₀ ∉ R₀ → ∀ x ∈ normBand F α β,
      ∀ w : (AdeleRing (𝓞 F) F)ˣ, ∀ γ ∈ familySet F γ₀,
        f (x⁻¹ * globalPoints (𝓞 F) F γ * (centralScalar (𝓞 F) F w * x)) = 0 := by
  exact GeoEllUnfolding.exists_finset_forall_eq_zero α β f hf hfc R hRsub hR

p2m_export "CentralEllipticUnfolding" "exists_finset_forall_eq_zero"

private theorem _root_.CentralEllipticUnfolding.lintegral_lintegral_abs_lt_top (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫⁻ x in Φ, ∫⁻ z in Ω, ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑ᶠ γ ∈ centralCell F ∪ ellipticCell F,
          ‖f (x⁻¹ * globalPoints (𝓞 F) F γ * (centralScalar (𝓞 F) F z * x))‖ₑ ∂νZ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  exact GeoEllUnfolding.lintegral_lintegral_abs_lt_top α β hα hαβ Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt f hf hfc

p2m_export "CentralEllipticUnfolding" "lintegral_lintegral_abs_lt_top"

private theorem _root_.CentralEllipticUnfolding.setIntegral_finsum_princ_eq_integral
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F)
    (x : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun w : (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) νZ) :
    IntegrableOn (fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z)) Ω νZ ∧
      ∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) ∂νZ =
        ∫ w, ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w ∂νZ := by
  exact GeoEllUnfolding.setIntegral_finsum_princ_eq_integral νZ Ω hΩ ξ hξc hξt f hf hfc γ₀ x hint

p2m_export "CentralEllipticUnfolding" "setIntegral_finsum_princ_eq_integral"

private theorem _root_.CentralEllipticUnfolding.setIntegral_orbitSum_eq_setIntegral_centralizerDomain (α β : ℝ)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F)
    (Ψ : Set (AdelicGL2 (𝓞 F) F)) (hΨs : Ψ ⊆ normBand F α β)
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (w : (AdeleRing (𝓞 F) F)ˣ)
    (hint : IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
      f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F w * x))) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    ∫ x in Φ, orbitSum F f γ₀ x w ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in Ψ, f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F w * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  exact GeoEllUnfolding.setIntegral_orbitSum_eq_setIntegral_centralizerDomain α β Φ hΦs hΦ f hf hfc γ₀ Ψ hΨs hΨ w hint

p2m_export "CentralEllipticUnfolding" "setIntegral_orbitSum_eq_setIntegral_centralizerDomain"

private theorem _root_.CentralEllipticUnfolding.integrable_prod_family (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ centralCell F ∪ ellipticCell F) (γ₀ : GL (Fin 2) F) (hγ₀ : γ₀ ∈ R) :
    Integrable (fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ p.1 p.2)
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ).prod νZ) := by
  exact GeoEllUnfolding.integrable_prod_family α β hα hαβ Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt f hf hfc R hRsub γ₀ hγ₀

p2m_export "CentralEllipticUnfolding" "integrable_prod_family"

private theorem _root_.CentralEllipticUnfolding.integrableOn_centralizerDomain (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (γ₀ : GL (Fin 2) F)
    (hγ₀ : γ₀ ∈ centralCell F ∪ ellipticCell F)
    (Ψ : Set (AdelicGL2 (𝓞 F) F)) (hΨs : Ψ ⊆ normBand F α β)
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)))
    (w : (AdeleRing (𝓞 F) F)ˣ) :
    IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
      f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F w * x))) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := by
  exact GeoEllUnfolding.integrableOn_centralizerDomain α β hα hαβ Φ hΦs hΦ f hf hfc γ₀ hγ₀ Ψ hΨs hΨ w

p2m_export "CentralEllipticUnfolding" "integrableOn_centralizerDomain"

private theorem _root_.CentralEllipticUnfolding.nullMeasurableSet_of_isFundamentalDomain_band (α β : ℝ)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  exact GeoEllUnfolding.nullMeasurableSet_of_isFundamentalDomain_band α β Φ hΦs hΦ

p2m_export "CentralEllipticUnfolding" "nullMeasurableSet_of_isFundamentalDomain_band"

private theorem isFiniteMeasure_restrict_of_isFundamentalDomain_band (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ normBand F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β))) :
    IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have h : adelicGLHaar (Fin 2) (𝓞 F) F (Φ ∩ normBand F α β) < ⊤ :=
    AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      F α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_left.mpr hΦs] at h

end CentralEllipticUnfolding

end

open CentralEllipticUnfolding in
theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (Ψ : GL (Fin 2) F → Set (AdelicGL2 (𝓞 F) F))
    (hΨs : ∀ γ₀ ∈ R, Ψ γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : ∀ γ₀ ∈ R, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) (Ψ γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelCentralPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x) +
          AutomorphicForm.adelicKernelEllipticPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂νZ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∑ᶠ γ₀ ∈ R,
      ((Nat.card {a : Fˣ // ∃ h : GL (Fin 2) F,
          Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
        ∫ z : (AdeleRing (𝓞 F) F)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ∂νZ := by
  classical

  have hΦs' : Φ ⊆ normBand F α β := hΦs
  have hΦ' : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := hΦ
  have hΨs' : ∀ γ₀ ∈ R, Ψ γ₀ ⊆ normBand F α β := hΨs
  have hΨ' : ∀ γ₀ ∈ R, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (globalPoints (𝓞 F) F)) (Ψ γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) := hΨ
  haveI := sigmaCompactSpace_ideles (F := F)
  haveI := isFiniteMeasure_restrict_of_isFundamentalDomain_band α β hα hαβ Φ hΦs' hΦ'
  have hΦm := nullMeasurableSet_of_isFundamentalDomain_band α β Φ hΦs' hΦ'

  obtain ⟨R₀, hR₀sub, hR₀⟩ := exists_finset_forall_eq_zero α β f hf hfc R hRsub hR
  have hvan : ∀ γ₀ ∈ R, γ₀ ∉ R₀ → ∀ x ∈ normBand F α β, ∀ w, orbitSum F f γ₀ x w = 0 := by
    intro γ₀ hγ₀ hnot x hx w
    unfold orbitSum
    exact finsum_mem_of_eqOn_zero fun γ' hγ' => hR₀ γ₀ hγ₀ hnot x hx w γ' (orbitSet_subset_familySet F γ₀ hγ')
  have hvan' : ∀ γ₀ ∈ R, γ₀ ∉ R₀ → ∀ x ∈ normBand F α β, ∀ w,
      f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F w * x)) = 0 :=
    fun γ₀ hγ₀ hnot x hx w => hR₀ γ₀ hγ₀ hnot x hx w γ₀ (self_mem_familySet F γ₀)

  have hjoint : ∀ γ₀ ∈ R, Integrable (fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ p.1 p.2)
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ).prod νZ) :=
    fun γ₀ hγ₀ => integrable_prod_family α β hα hαβ Φ hΦs' hΦ' νZ Ω hΩ ξ hξc hξt f hf hfc R hRsub γ₀ hγ₀
  have hΨint : ∀ γ₀ ∈ R, ∀ w, IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
      f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F w * x))) (Ψ γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (normBand F α β)) :=
    fun γ₀ hγ₀ w => integrableOn_centralizerDomain α β hα hαβ Φ hΦs' hΦ' f hf hfc γ₀ (hRsub hγ₀) (Ψ γ₀)
      (hΨs' γ₀ hγ₀) (hΨ' γ₀ hγ₀) w

  have hpt : ∀ x ∈ normBand F α β, ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (adelicKernelCentralPart F f x (centralScalar (𝓞 F) F z * x) +
          adelicKernelEllipticPart F f x (centralScalar (𝓞 F) F z * x)) =
      ∑ γ₀ ∈ R₀, (stabCard F γ₀)⁻¹ *
        (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z)) := by
    intro x hx z
    rw [kernelParts_eq_finsum_families f hfc R hRsub hR x z,
      finsum_mem_eq_sum_of_subset _ (t := R₀) ?_ hR₀sub, Finset.mul_sum]
    · exact Finset.sum_congr rfl fun γ₀ _ => by ring
    · rintro γ₀ ⟨hγ₀R, hsupp⟩
      by_contra hnot
      refine Function.mem_support.mp hsupp ?_
      show (stabCard F γ₀)⁻¹ * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z) = 0
      rw [finsum_congr fun a => hvan γ₀ hγ₀R hnot x hx (princ F a * z), finsum_zero, mul_zero]

  have hae : ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F), x ∈ Φ → ∀ γ₀ ∈ R₀,
      Integrable (fun w : (AdeleRing (𝓞 F) F)ˣ =>
        ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) νZ := by
    rw [← ae_restrict_iff'₀ hΦm, Filter.eventually_all_finset]
    exact fun γ₀ hγ₀ => (hjoint γ₀ (hR₀sub hγ₀)).prod_right_ae
  have hinner : ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F), x ∈ Φ →
      (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (adelicKernelCentralPart F f x (centralScalar (𝓞 F) F z * x) +
          adelicKernelEllipticPart F f x (centralScalar (𝓞 F) F z * x)) ∂νZ) =
      ∑ γ₀ ∈ R₀, (stabCard F γ₀)⁻¹ *
        ∫ w, ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w ∂νZ := by
    filter_upwards [hae] with x hx hxΦ
    have hx' := hΦs' hxΦ
    have hxint := hx hxΦ
    have hfun : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (adelicKernelCentralPart F f x (centralScalar (𝓞 F) F z * x) +
          adelicKernelEllipticPart F f x (centralScalar (𝓞 F) F z * x))) =
        fun z => ∑ γ₀ ∈ R₀, (stabCard F γ₀)⁻¹ *
          (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ a : Fˣ, orbitSum F f γ₀ x (princ F a * z)) :=
      funext fun z => hpt x hx' z
    rw [hfun, integral_finsetSum]
    · refine Finset.sum_congr rfl fun γ₀ hγ₀ => ?_
      rw [integral_const_mul,
        (setIntegral_finsum_princ_eq_integral νZ Ω hΩ ξ hξc hξt f hf hfc γ₀ x (hxint γ₀ hγ₀)).2]
    · intro γ₀ hγ₀
      exact ((setIntegral_finsum_princ_eq_integral νZ Ω hΩ ξ hξc hξt f hf hfc γ₀ x (hxint γ₀ hγ₀)).1).const_mul _

  rw [setIntegral_congr_ae₀ hΦm hinner, integral_finsetSum]
  ·
    rw [finsum_mem_eq_sum_of_subset _ (t := R₀) ?_ hR₀sub]
    · refine Finset.sum_congr rfl fun γ₀ hγ₀ => ?_
      have hγ₀R := hR₀sub hγ₀
      rw [integral_const_mul]
      unfold stabCard
      congr 1

      have hswap := integral_integral_swap (μ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) (ν := νZ)
        (f := fun x w => ((ξ ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * orbitSum F f γ₀ x w) (hjoint γ₀ hγ₀R)
      rw [hswap]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      beta_reduce
      rw [integral_const_mul]
      congr 1

      exact setIntegral_orbitSum_eq_setIntegral_centralizerDomain α β Φ hΦs' hΦ' f hf hfc γ₀ (Ψ γ₀)
        (hΨs' γ₀ hγ₀R) (hΨ' γ₀ hγ₀R) w (hΨint γ₀ hγ₀R w)
    · rintro γ₀ ⟨hγ₀R, hsupp⟩
      by_contra hnot
      refine Function.mem_support.mp hsupp ?_
      show ((Nat.card {a : Fˣ // ∃ h : GL (Fin 2) F,
          Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
        ∫ z : (AdeleRing (𝓞 F) F)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ γ₀, f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ∂νZ = 0
      have hzero : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
          (∫ x in Ψ γ₀, f (x⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = 0 := fun z => by
        rw [← Measure.restrict_restrict_of_subset (hΨs' γ₀ hγ₀R)]
        refine (setIntegral_congr_ae₀ (hΨ' γ₀ hγ₀R).nullMeasurableSet
          (Filter.Eventually.of_forall fun x hx => hvan' γ₀ hγ₀R hnot x (hΨs' γ₀ hγ₀R hx) z)).trans ?_
        simp
      simp [hzero]
  · intro γ₀ hγ₀
    exact ((hjoint γ₀ (hR₀sub hγ₀)).integral_prod_left).const_mul _

end S_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain (solution)
