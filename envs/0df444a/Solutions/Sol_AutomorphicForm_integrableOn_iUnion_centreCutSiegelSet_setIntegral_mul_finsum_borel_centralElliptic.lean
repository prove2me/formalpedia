-- Prove2me | solution 1 for AutomorphicForm.integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1bce7e94-4a3b-513d-bb0b-89c7b81576cd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_MeasureTheory_ContractionDecay
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_SiegelVolume
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

section KernelSplitting

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.adeleBorel

namespace KernelSplitting

section Kernel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K))) {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ}
  {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}

private theorem isFactorizableTestFn_of_isSemiLocalFactorization
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    AutomorphicForm.IsFactorizableTestFn L φ :=
  ⟨φa, φf, h.1, h.2.1, h.2.2.2.2.2⟩

private theorem continuous_and_hasCompactSupport_of_isSemiLocalFactorization
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    Continuous φ ∧ HasCompactSupport φ :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    (isFactorizableTestFn_of_isSemiLocalFactorization K L S h)

end Kernel

end KernelSplitting

end KernelSplitting

section CellScalar

set_option autoImplicit false

namespace CellScalarStability

section Charpoly

open Polynomial

variable {R : Type*} [Field R]

private theorem charpoly_smul_fin_two {a : R} (ha : a ≠ 0) (M : Matrix (Fin 2) (Fin 2) R) :
    (a • M).charpoly = C (a ^ 2) * M.charpoly.comp (C a⁻¹ * X) := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul]
  simp only [add_comp, sub_comp, pow_comp, mul_comp, X_comp, C_comp]
  have hinv : C a * C a⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ ha, C_1]
  rw [C_mul, C_mul, C_pow]
  linear_combination (-(C a * C a⁻¹ + 1) * X ^ 2 + C a * C M.trace * X) * hinv

private theorem sq_X_sub_C_mul_eq {a : R} (ha : a ≠ 0) (c : R) :
    (X - C (a * c)) ^ 2 = C (a ^ 2) * (C a⁻¹ * X - C c) ^ 2 := by
  have h : X - C (a * c) = C a * (C a⁻¹ * X - C c) := by
    rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, ← C_mul]
  rw [h, mul_pow, C_pow]

private theorem X_sub_C_mul_mul_eq {a : R} (ha : a ≠ 0) (b c : R) :
    (X - C (a * b)) * (X - C (a * c)) = C (a ^ 2) * ((C a⁻¹ * X - C b) * (C a⁻¹ * X - C c)) := by
  have h : ∀ d : R, X - C (a * d) = C a * (C a⁻¹ * X - C d) := fun d => by
    rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, ← C_mul]
  rw [h b, h c, C_pow]
  ring

private theorem not_isCentralType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : ¬AutomorphicForm.IsCentralType M) : ¬AutomorphicForm.IsCentralType (a • M) := by
  rintro ⟨d, hd⟩
  exact hM ⟨a⁻¹ * d, by rw [← smul_smul, ← hd, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

private theorem isUnipotentType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsUnipotentType M) : AutomorphicForm.IsUnipotentType (a • M) := by
  obtain ⟨hnc, c, hc⟩ := hM
  refine ⟨not_isCentralType_smul ha hnc, a * c, ?_⟩
  rw [charpoly_smul_fin_two ha, hc, sq_X_sub_C_mul_eq ha]
  simp only [pow_comp, sub_comp, X_comp, C_comp]

private theorem isHyperbolicType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsHyperbolicType M) : AutomorphicForm.IsHyperbolicType (a • M) := by
  obtain ⟨b, c, hbc, hM⟩ := hM
  refine ⟨a * b, a * c, fun h => hbc (mul_left_cancel₀ ha h), ?_⟩
  rw [charpoly_smul_fin_two ha, hM, X_sub_C_mul_mul_eq ha]
  simp only [mul_comp, sub_comp, X_comp, C_comp]

end Charpoly

section Cells

variable {R : Type*} [Field R]

private theorem coe_scalar (s : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = Matrix.scalar (Fin 2) (s : R) := rfl

private theorem coe_mul_scalar (γ : GL (Fin 2) R) (s : Rˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = (s : R) • (γ : Matrix (Fin 2) (Fin 2) R) := by
  rw [Units.val_mul, coe_scalar, Matrix.scalar_apply]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem isCentralType_smul (a : R) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsCentralType M) : AutomorphicForm.IsCentralType (a • M) := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨a * c, by rw [hc, smul_smul]⟩

private theorem isEllipticType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsEllipticType M) : AutomorphicForm.IsEllipticType (a • M) := by
  intro b hb
  apply hM (b / a)
  rw [Matrix.charpoly_fin_two] at hb ⊢
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul] at hb ⊢
  have key : (b / a) ^ 2 - M.trace * (b / a) + M.det
      = (b ^ 2 - a * M.trace * b + a ^ 2 * M.det) / a ^ 2 := by
    field_simp
  rw [key, hb, zero_div]

private theorem mul_scalar_mem_centralCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.centralCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.centralCell R := by
  show AutomorphicForm.IsCentralType _
  rw [coe_mul_scalar]
  exact isCentralType_smul _ hγ

private theorem mul_scalar_mem_ellipticCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.ellipticCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.ellipticCell R := by
  show AutomorphicForm.IsEllipticType _
  rw [coe_mul_scalar]
  exact isEllipticType_smul s.ne_zero hγ

private theorem mul_scalar_mem_unipotentCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.unipotentCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.unipotentCell R := by
  show AutomorphicForm.IsUnipotentType _
  rw [coe_mul_scalar]
  exact isUnipotentType_smul s.ne_zero hγ

private theorem mul_scalar_mem_hyperbolicCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.hyperbolicCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.hyperbolicCell R := by
  show AutomorphicForm.IsHyperbolicType _
  rw [coe_mul_scalar]
  exact isHyperbolicType_smul s.ne_zero hγ

end Cells

section Scalars

private theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) s) := by
  apply Units.ext
  ext i j
  show f ((Matrix.scalar (Fin 2) (s : R)) i j) = (Matrix.scalar (Fin 2) (f (s : R))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem _root_.CellScalarStability.scalar_commute {R : Type*} [CommRing R] (s : Rˣ) (g : GL (Fin 2) R) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) s) g := by
  show Matrix.GeneralLinearGroup.scalar (Fin 2) s * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) s
  exact Units.ext
    (Matrix.scalar_commute (s : R) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) R)).eq

p2m_export "CellScalarStability" "scalar_commute"
private theorem sigmaPartialNorm_mul_of_commute {G : Type*} [Group G] (σ : G →* G) {s : G}
    (hs : ∀ g : G, Commute s g) (x : G) (r : ℕ) :
    LT.TwistedNorm.sigmaPartialNorm σ (x * s) r
      = LT.TwistedNorm.sigmaPartialNorm σ x r * LT.TwistedNorm.sigmaPartialNorm σ s r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', LT.TwistedNorm.sigmaPartialNorm_succ',
        LT.TwistedNorm.sigmaPartialNorm_succ', ih, map_mul]
      have hc := (hs (σ (LT.TwistedNorm.sigmaPartialNorm σ x r))).eq
      simp only [mul_assoc]
      rw [← mul_assoc s, hc, mul_assoc]

private theorem sigmaNormPow_mul_of_commute {G : Type*} [Group G] (σ : G →* G) {s : G}
    (hs : ∀ g : G, Commute s g) (ℓ : ℕ) (x : G) :
    LT.TwistedNorm.sigmaNormPow σ ℓ (x * s)
      = LT.TwistedNorm.sigmaNormPow σ ℓ x * LT.TwistedNorm.sigmaNormPow σ ℓ s :=
  sigmaPartialNorm_mul_of_commute σ hs x ℓ

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

private theorem sigmaNormPow_scalar (σ : L ≃ₐ[F] L) (ℓ : ℕ) (a : Lˣ) :
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) ℓ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (LT.TwistedNorm.sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) ℓ a) :=
  (LT.TwistedNorm.hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L))
    (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Matrix.GeneralLinearGroup.scalar (Fin 2))
    (fun b => (map_scalar (σ : L →+* L) b).symm) ℓ a).symm

variable [FiniteDimensional F L] [IsGalois F L]

private theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (a : Lˣ) :
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a)
      = LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
          (Module.finrank F L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap F L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a)) := by
  rw [sigmaNormPow_mul_of_commute _ (scalar_commute a), sigmaNormPow_scalar, map_scalar]
  congr 2
  apply Units.ext
  rw [LT.TwistedNorm.coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  simp only [Units.coe_map, MonoidHom.coe_coe]

private theorem isNormRep_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : LT.TwistedNorm.IsNormRep σ γ δ) (a : Lˣ) :
    LT.TwistedNorm.IsNormRep σ
      (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP, map_scalar]
  have hc := (scalar_commute (Units.map ((algebraMap F L : F →+* L) : F →* L)
    (Units.map (Algebra.norm F : L →* F) a)) P).eq
  simp only [mul_assoc]
  rw [hc]

private theorem normClassMap_mk_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ)
    (a : Lˣ) :
    LT.TwistedNorm.normClassMap hgen
        (LT.TwistedNorm.SigmaConjClasses.mk σ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a))
      = ConjClasses.mk
          (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a)) := by
  rw [LT.TwistedNorm.normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P, hP⟩ := LT.TwistedNorm.isNormRep_normRep hgen δ
  have hγ : LT.TwistedNorm.IsNormRep σ γ δ :=
    ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, by
      rw [← hQ, map_mul, map_mul, map_inv, ← hP]
      group⟩
  exact LT.TwistedNorm.normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hγ a)

private theorem mul_scalar_mem_centralElliptic {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  refine ⟨γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a), ?_,
    normClassMap_mk_mul_scalar hgen hclass a⟩
  rcases hγ with hγ | hγ
  · exact Or.inl (mul_scalar_mem_ellipticCell hγ _)
  · exact Or.inr (mul_scalar_mem_centralCell hγ _)

end Scalars

section IndexSets

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem mul_scalar_mem_setOf_unipotent {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      γ ∈ AutomorphicForm.unipotentCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  exact ⟨_, mul_scalar_mem_unipotentCell hγ _, normClassMap_mk_mul_scalar hgen hclass a⟩

private theorem mul_scalar_mem_setOf_hyperbolic {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.hyperbolicCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      γ ∈ AutomorphicForm.hyperbolicCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  exact ⟨_, mul_scalar_mem_hyperbolicCell hγ _, normClassMap_mk_mul_scalar hgen hclass a⟩

end IndexSets

end CellScalarStability

end CellScalar

section CentralEllipticShell

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct Pointwise

namespace CentralEllipticShell

section Scalars

private theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) s) := by
  apply Units.ext
  ext i j
  show f ((Matrix.scalar (Fin 2) (s : R)) i j) = (Matrix.scalar (Fin 2) (f (s : R))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end Scalars

section Reindex

variable {L : Type*} [Field L]

private theorem finsum_mem_mul_scalar_eq {M : Type*} [AddCommMonoid M] (T : Set (GL (Fin 2) L))
    (hT : ∀ δ ∈ T, ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ T)
    (G : GL (Fin 2) L → M) (a : Lˣ) :
    ∑ᶠ δ ∈ T, G (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) = ∑ᶠ δ ∈ T, G δ := by
  refine finsum_mem_eq_of_bijOn (fun δ => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a)
    ⟨fun δ hδ => hT δ hδ a, ?_, ?_⟩ fun δ _ => rfl
  · intro δ₁ _ δ₂ _ h
    exact mul_right_cancel h
  · intro δ hδ
    refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹, hT δ hδ a⁻¹, ?_⟩
    show δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a = δ
    rw [map_inv, inv_mul_cancel_right]

end Reindex

section Kernel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

private theorem centralScalar_map_algebraMap (ζ : Lˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) ζ)
      = AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) := by
  show Matrix.GeneralLinearGroup.scalar (Fin 2) _
    = Matrix.GeneralLinearGroup.map (algebraMap L (AdeleRing (𝓞 L) L))
        (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)
  rw [map_scalar]

private theorem ideleNorm_one' : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  have h : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) *
      NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ)
        = NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, mul_one]
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne'
    (h.trans (mul_one _).symm)

private theorem ideleNorm_inv' (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one']

private theorem ideleNorm_sq_mem_of_ne_zero (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) (δ : GL (Fin 2) L)
    (hne : φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0) :
    NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈
      (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' Function.support φ := by
  refine ⟨_, hne, ?_⟩
  have hx : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z * z := by
    apply Units.ext
    show Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = (z : AdeleRing (𝓞 L) L) * z
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  dsimp only
  rw [map_mul, map_mul, map_inv, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv', AutomorphicForm.ideleNorm_det_globalPoints,
    AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ, map_mul,
    NumberField.TateGlobal.ideleNorm_mul, hdet, NumberField.TateGlobal.ideleNorm_mul]
  field_simp

private theorem finsum_mem_centralScalar_map_mul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (T : Set (GL (Fin 2) L))
    (hT : ∀ δ ∈ T, ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ T)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) := by
  have hσ : AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ))
      = AutomorphicForm.globalPoints (𝓞 L) L
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) :=
    AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ _
  refine Eq.trans ?_ (finsum_mem_mul_scalar_eq T hT
    (fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    (Units.map ((σ : L →+* L) : L →* L) ζ))
  refine finsum_mem_congr rfl fun δ _ => ?_
  beta_reduce
  simp only [map_mul, centralScalar_map_algebraMap, hσ, map_scalar, mul_assoc]

end Kernel

end CentralEllipticShell

end CentralEllipticShell

section FoldBounds

set_option autoImplicit false

open MeasureTheory NumberField Topology
open IsDedekindDomain
open scoped TensorProduct Pointwise NNReal

namespace KernelFoldBounds

section Generic

variable (L : Type) [Field L] [NumberField L]

private theorem exists_finite_forall_ne_zero_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * 1 ∈
    X * tsupport φ * Y⁻¹}, hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : AutomorphicForm.globalPoints (𝓞 L) L δ
      = x * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * 1 ∈
    X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

private theorem finsum_mem_eq_sum_of_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ t : Finset (GL (Fin 2) L), (t : Set (GL (Fin 2) L)) ⊆ T ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y)
        = ∑ δ ∈ t, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  refine ⟨hΓT.toFinset, fun δ hδ => (hΓT.mem_toFinset.mp hδ).2, fun x hx y hy => ?_⟩
  apply finsum_mem_eq_sum_of_subset
  · rintro δ ⟨hδT, hδs⟩
    exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
  · intro δ hδ
    exact (hΓT.mem_toFinset.mp hδ).2

private theorem continuous_finsum_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨t, -, ht⟩ := finsum_mem_eq_sum_of_mem L hfin φ hφs T hX hY
  have hsum : Continuous fun q : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ t, φ (q.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * q.2) := by
    refine continuous_finsetSum t fun δ _ => hφc.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul continuous_snd
  refine ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt ?_
  exact prod_mem_nhds hXn hYn

private theorem exists_forall_norm_finsum_mem_le (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X)
    (hY : IsCompact Y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ‖∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hX.prod hY).exists_bound_of_continuousOn
    (continuous_finsum_mem L hfin φ hφc hφs T).continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx y hy => (hM (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)⟩

end Generic

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem continuous_glMap'' {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

private theorem continuous_sigmaAdelicAct'' : Continuous (AutomorphicForm.sigmaAdelicAct K L D σ) :=
  continuous_glMap'' (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom (D.continuous_act σ)

private theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_val
    · exact continuous_const
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem continuous_sigmaAdelicAct_centralScalar_mul :
    Continuous fun q : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1 * q.2) :=
  (continuous_sigmaAdelicAct'' K L D σ).comp
    (((continuous_centralScalar L).comp continuous_fst).mul continuous_snd)

private theorem continuous_finsum_mem_centralScalar (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) := by
  have hzx : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (z, x) := continuous_id.prodMk continuous_const
  have hact := (continuous_sigmaAdelicAct_centralScalar_mul K L D σ).comp hzx
  have hpair := (continuous_const (y := x)).prodMk hact
  have h := (continuous_finsum_mem L hfin φ hφc hφs T).comp hpair
  exact h

private theorem exists_forall_norm_mul_finsum_mem_le (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Z : Set (AdeleRing (𝓞 L) L)ˣ) {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    (hrep : ∀ z ∈ Z, ∃ η : Lˣ, ∃ w ∈ W,
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w)
    (hZ : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), ∀ z ∉ Z,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (hper : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    {X : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ X, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ ≤ M := by
  have hY : IsCompact ((fun q : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1 * q.2)) ''
        (W ×ˢ X)) :=
    (hW.prod hX).image (continuous_sigmaAdelicAct_centralScalar_mul K L D σ)
  obtain ⟨MK, hMK0, hMK⟩ := exists_forall_norm_finsum_mem_le L hfin φ hφc hφs T hX hY
  obtain ⟨Mξ, hMξ⟩ := hW.exists_bound_of_continuousOn hξc.continuousOn
  refine ⟨max Mξ 0 * MK, mul_nonneg (le_max_right _ _) hMK0, fun x hx z => ?_⟩
  by_cases hz : z ∈ Z
  · obtain ⟨η, w, hw, rfl⟩ := hrep z hz
    have hξ : ξL ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w,
          Subgroup.mem_top _⟩ = ξL ⟨w, Subgroup.mem_top w⟩ := by
      rw [show (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w, Subgroup.mem_top _⟩ :
            (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ))
          = ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η, Subgroup.mem_top _⟩ *
            ⟨w, Subgroup.mem_top w⟩ from rfl,
        map_mul, hξt _ (MonoidHom.mem_range.mpr ⟨η, rfl⟩), one_mul]
    rw [hper x η w, hξ, norm_mul]
    exact mul_le_mul ((hMξ w hw).trans (le_max_left _ _)) (hMK x hx _ ⟨(w, x), ⟨hw, hx⟩, rfl⟩)
      (norm_nonneg _) (le_max_right _ _)
  · rw [hZ x z hz, mul_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) hMK0

private theorem integrableOn_mul_finsum_mem [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Z : Set (AdeleRing (𝓞 L) L)ˣ) (hZm : MeasurableSet Z) (hvol : νZL (Z ∩ ΩL) < ⊤)
    {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    (hrep : ∀ z ∈ Z, ∃ η : Lˣ, ∃ w ∈ W,
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w)
    (hZ : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), ∀ z ∉ Z,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (hper : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL := by
  obtain ⟨M, -, hM⟩ := exists_forall_norm_mul_finsum_mem_le K L D σ hfin φ hφc hφs T ξL hξc hξt Z hW
    hrep hZ hper isCompact_singleton (X := {x})
  have hg : Integrable (Z.indicator fun _ => M) (νZL.restrict ΩL) := by
    rw [integrable_indicator_iff hZm]
    exact integrableOn_const (by rw [Measure.restrict_apply hZm]; exact hvol.ne)
  have hmeas : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) :=
    hξc.mul (continuous_finsum_mem_centralScalar K L D σ hfin φ hφc hφs T x)
  show Integrable _ (νZL.restrict ΩL)
  refine Integrable.mono' hg hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Z
  · rw [Set.indicator_of_mem hz]
    exact hM x (Set.mem_singleton x) z
  · have h0 := hZ x z hz
    simp only [Set.indicator_of_notMem hz, h0, mul_zero, norm_zero, le_refl]

end Fold

section Representatives

variable (L : Type) [Field L] [NumberField L]

private theorem ideleNorm_one'' : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  have h : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) *
      NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ)
        = NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, mul_one]
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne'
    (h.trans (mul_one _).symm)

private theorem ideleNorm_inv'' (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one'']

private theorem exists_isCompact_forall_mem_shell_exists_eq_mul
    (hK : ∃ Kc : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Kc ∧
      Kc ⊆ (NumberField.TateGlobal.normOneIdeles L : Set (AdeleRing (𝓞 L) L)ˣ) ∧
      ∀ x ∈ NumberField.TateGlobal.normOneIdeles L, ∃ (η : Lˣ) (κ : (AdeleRing (𝓞 L) L)ˣ), κ ∈ Kc ∧
        x = Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η * κ)
    (hs : ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 L) L)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, NumberField.TateGlobal.ideleNorm L (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1)
    {a b : ℝ≥0} (ha : 0 < a) :
    ∃ W : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact W ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (a : ℝ) b →
        ∃ η : Lˣ, ∃ w ∈ W, z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w := by
  obtain ⟨Kc, hKc, -, hKrep⟩ := hK
  obtain ⟨s, hsc, hsn, -⟩ := hs
  haveI : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Set.Icc a b → (AdeleRing (𝓞 L) L)ˣ := fun t =>
    s (Units.mk0 (t : ℝ≥0) (ha.trans_le t.2.1).ne')
  have hF : Continuous F := by
    refine hsc.comp (Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩)
    exact continuous_subtype_val.inv₀ fun t => (ha.trans_le t.2.1).ne'
  refine ⟨Set.range F * Kc, (isCompact_range hF).mul hKc, fun z hz => ?_⟩

  have hr0 : 0 ≤ NumberField.TateGlobal.ideleNorm L z := (NumberField.TateGlobal.ideleNorm_pos z).le
  have hz' : (⟨NumberField.TateGlobal.ideleNorm L z, hr0⟩ : ℝ≥0) ∈ Set.Icc a b :=
    ⟨NNReal.coe_le_coe.mp hz.1, NNReal.coe_le_coe.mp hz.2⟩
  set t : Set.Icc a b := ⟨_, hz'⟩ with ht
  have hFt : NumberField.TateGlobal.ideleNorm L (F t) = NumberField.TateGlobal.ideleNorm L z :=
    hsn (Units.mk0 ⟨NumberField.TateGlobal.ideleNorm L z, hr0⟩ (ha.trans_le hz'.1).ne')

  have hnorm : z * (F t)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv'',
      hFt]
    exact mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne'
  obtain ⟨η, κ, hκ, hzκ⟩ := hKrep _ hnorm
  refine ⟨η, F t * κ, Set.mul_mem_mul ⟨t, rfl⟩ hκ, ?_⟩
  have hz'' : z = z * (F t)⁻¹ * F t := by rw [inv_mul_cancel_right]
  rw [hz'', hzκ]
  simp only [RingHom.toMonoidHom_eq_coe, mul_assoc, mul_comm κ (F t)]

end Representatives

end KernelFoldBounds

end FoldBounds

section ShellVolume

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

namespace ShellVolume

section Shell

variable (L : Type) [Field L] [NumberField L]

private theorem continuous_det_gl :
    Continuous fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

private theorem exists_forall_ideleNorm_det_mem_Icc (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφs : HasCompactSupport φ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
  set N : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ :=
    fun g => NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) with hN
  have hNc : Continuous N := (NumberField.TateGlobal.continuous_ideleNorm L).comp (continuous_det_gl L)
  have hS : IsCompact (N '' tsupport φ) := hφs.image hNc
  by_cases hne : (N '' tsupport φ).Nonempty
  · obtain ⟨a, haS, ha⟩ := hS.exists_isLeast hne
    obtain ⟨b, hbS, hb⟩ := hS.exists_isGreatest hne
    obtain ⟨ga, -, hga⟩ := haS
    have ha_pos : 0 < a := by
      rw [← hga]
      exact NumberField.TateGlobal.ideleNorm_pos _
    refine ⟨a, b, ha_pos, ha hbS, fun g hg => ?_⟩
    have hgN : N g ∈ N '' tsupport φ := ⟨g, subset_tsupport φ hg, rfl⟩
    exact ⟨ha hgN, hb hgN⟩
  · refine ⟨1, 1, one_pos, le_rfl, fun g hg => ?_⟩
    exact (hne ⟨N g, g, subset_tsupport φ hg, rfl⟩).elim

private theorem measurableSet_shell [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (a b : ℝ) :
    MeasurableSet {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b} :=
  (NumberField.TateGlobal.continuous_ideleNorm L).measurable measurableSet_Icc

private theorem mem_shell_of_mul_self_mem {a b : ℝ} (z : (AdeleRing (𝓞 L) L)ˣ)
    (h : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b) :
    NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b) := by
  have h0 : 0 ≤ NumberField.TateGlobal.ideleNorm L z := (NumberField.TateGlobal.ideleNorm_pos z).le
  constructor
  · calc Real.sqrt a ≤ Real.sqrt (NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z) :=
          Real.sqrt_le_sqrt h.1
      _ = NumberField.TateGlobal.ideleNorm L z := Real.sqrt_mul_self h0
  · calc NumberField.TateGlobal.ideleNorm L z
          = Real.sqrt (NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z) :=
          (Real.sqrt_mul_self h0).symm
      _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h.2

private theorem preimage_smul_shell_eq
    (hn : ∀ η : Lˣ, NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1)
    (a b : ℝ) (c : (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range) :
    (fun z : (AdeleRing (𝓞 L) L)ˣ => c • z) ⁻¹'
        {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b}
      = {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b} := by
  obtain ⟨η, hη⟩ := MonoidHom.mem_range.mp c.2
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul,
    NumberField.TateGlobal.ideleNorm_mul, ← hη, hn, one_mul]

end Shell

section Volume

variable (L : Type) [Field L] [NumberField L]
private theorem countable_range_map_algebraMap :
    Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
  haveI : Countable L := Countable.of_equiv _ (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.symm
  haveI : Countable Lˣ := Units.val_injective.countable
  exact (Set.countable_range _).to_subtype

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

private theorem smulInvariantMeasure_range (μ : Measure (AdeleRing (𝓞 L) L)ˣ) [μ.IsMulLeftInvariant] :
    SMulInvariantMeasure (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range
      (AdeleRing (𝓞 L) L)ˣ μ := by
  refine ⟨fun c s _ => ?_⟩
  exact measure_preimage_mul μ (c : (AdeleRing (𝓞 L) L)ˣ) s

private theorem measure_shell_inter_lt_top (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (hn : ∀ η : Lˣ, NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (Dm : Set (AdeleRing (𝓞 L) L)ˣ)
    (hDm : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Dm νZL)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ)
    (hint : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => min (NumberField.TateGlobal.ideleNorm L z)
      (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)) Dm νZL) :
    νZL ({z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} ∩ ΩL) < ⊤ := by
  haveI := countable_range_map_algebraMap L
  haveI : MeasurableConstSMul
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range (AdeleRing (𝓞 L) L)ˣ :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable⟩
  haveI := smulInvariantMeasure_range L νZL
  set Z : Set (AdeleRing (𝓞 L) L)ˣ :=
    {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} with hZ
  have hZm : MeasurableSet Z := measurableSet_shell L _ _
  rw [hΩL.measure_set_eq hDm hZm (preimage_smul_shell_eq L hn _ _)]

  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr (ha.trans_le hab)
  set ε : ℝ := min (Real.sqrt a) (Real.sqrt b)⁻¹ ^ k with hε
  have hε0 : 0 < ε := pow_pos (lt_min hsa (inv_pos.mpr hsb)) k
  have hsub : Z ⊆ {z : (AdeleRing (𝓞 L) L)ˣ | ε ≤ ‖min (NumberField.TateGlobal.ideleNorm L z)
      (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)‖} := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hz
    have hz0 : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos z
    have hmin : min (Real.sqrt a) (Real.sqrt b)⁻¹
        ≤ min (NumberField.TateGlobal.ideleNorm L z) (NumberField.TateGlobal.ideleNorm L z)⁻¹ :=
      le_min ((min_le_left _ _).trans h₁) ((min_le_right _ _).trans (inv_anti₀ hz0 h₂))
    have hpow : ε ≤ min (NumberField.TateGlobal.ideleNorm L z) (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k :=
      pow_le_pow_left₀ (le_min hsa.le (inv_pos.mpr hsb).le) hmin k
    show ε ≤ ‖_‖
    rw [Real.rpow_zero, mul_one]
    exact hpow.trans (le_abs_self _)
  calc νZL (Z ∩ Dm) = νZL.restrict Dm Z := (Measure.restrict_apply hZm).symm
    _ ≤ νZL.restrict Dm {z | ε ≤ ‖min (NumberField.TateGlobal.ideleNorm L z)
          (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)‖} :=
        measure_mono hsub
    _ < ⊤ := Integrable.measure_norm_ge_lt_top hint hε0

end Volume

end ShellVolume

end ShellVolume

section OffBorel

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace OffBorelFold

section Split

variable {L : Type} [Field L]

private theorem setOf_eq_borel_union_offBorel (Q : GL (Fin 2) L → Prop) :
    {δ : GL (Fin 2) L | Q δ}
      = {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Q δ} ∪
        {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∧ Q δ} := by
  ext δ
  by_cases h : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 <;> simp [h]

private theorem disjoint_borel_offBorel (Q : GL (Fin 2) L → Prop) :
    Disjoint {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Q δ}
      {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∧ Q δ} :=
  Set.disjoint_left.mpr fun _ h₁ h₂ => h₂.1 h₁.1

private theorem finsum_mem_setOf_eq_add (Q : GL (Fin 2) L → Prop) (f : GL (Fin 2) L → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ δ ∈ {δ : GL (Fin 2) L | Q δ}, f δ
      = (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Q δ}, f δ) +
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∧ Q δ}, f δ := by
  rw [setOf_eq_borel_union_offBorel Q]
  exact finsum_mem_union' (disjoint_borel_offBorel Q) (hf.subset Set.inter_subset_right)
    (hf.subset Set.inter_subset_right)

private theorem apply_one_zero_mul_scalar (δ : GL (Fin 2) L) (a : Lˣ) :
    ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0
      = (δ : Matrix (Fin 2) (Fin 2) L) 1 0 * a := by
  rw [Units.val_mul]
  change ((δ : Matrix (Fin 2) (Fin 2) L) * Matrix.scalar (Fin 2) (a : L)) 1 0 = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]

private theorem mem_borel_mul_scalar {Q : GL (Fin 2) L → Prop} (hQ : ∀ δ, Q δ → ∀ a : Lˣ,
      Q (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a))
    {δ : GL (Fin 2) L} (hδ : δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Q δ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a
      ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Q δ} :=
  ⟨by rw [apply_one_zero_mul_scalar, hδ.1, zero_mul], hQ δ hδ.2 a⟩

private theorem mem_offBorel_mul_scalar {Q : GL (Fin 2) L → Prop} (hQ : ∀ δ, Q δ → ∀ a : Lˣ,
      Q (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a))
    {δ : GL (Fin 2) L} (hδ : δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∧ Q δ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a
      ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∧ Q δ} :=
  ⟨by rw [apply_one_zero_mul_scalar]; exact mul_ne_zero hδ.1 a.ne_zero, hQ δ hδ.2 a⟩

end Split

section Support

variable (L : Type) [Field L] [NumberField L]

private theorem finite_support_summand (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (x y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (Function.support fun δ : GL (Fin 2) L => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y)).Finite :=
  (hfin (tsupport φ) hφs x y).subset fun _ hδ => subset_tsupport φ hδ

end Support

section Bounds

variable {α : Type*} [MeasurableSpace α]

private theorem norm_setIntegral_le_integral_indicator (μ : Measure α) (Ω Z : Set α) (hZm : MeasurableSet Z)
    (hvol : μ (Z ∩ Ω) < ⊤) (M : ℝ) (f : α → ℂ)
    (hfM : ∀ z, ‖f z‖ ≤ M) (hfZ : ∀ z ∉ Z, f z = 0) :
    ‖∫ z in Ω, f z ∂μ‖ ≤ ∫ z in Ω, Z.indicator (fun _ => M) z ∂μ := by
  have hg : Integrable (Z.indicator fun _ => M) (μ.restrict Ω) := by
    rw [integrable_indicator_iff hZm]
    exact integrableOn_const (by rw [Measure.restrict_apply hZm]; exact hvol.ne)
  refine norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Z
  · rw [Set.indicator_of_mem hz]
    exact hfM z
  · simp only [Set.indicator_of_notMem hz, hfZ z hz, norm_zero, le_refl]

private theorem integrableOn_of_eq_zero_of_lt (μ : Measure α) (S : Set α) (hSm : MeasurableSet S) (hμ : μ S < ⊤)
    (G : α → ℂ) (hG : AEStronglyMeasurable G μ) (Ht : α → ℝ) (h : ℝ) (hzero : ∀ x, h < Ht x → G x = 0)
    (Kc : Set α) (hKc : {x | x ∈ S ∧ Ht x ≤ h} ⊆ Kc) (C : ℝ) (hC : ∀ x ∈ Kc, ‖G x‖ ≤ C) :
    IntegrableOn G S μ := by
  refine Measure.integrableOn_of_bounded hμ.ne hG (M := max C 0) (ae_restrict_of_forall_mem hSm fun x hx => ?_)
  by_cases hh : h < Ht x
  · rw [hzero x hh, norm_zero]
    exact le_max_right _ _
  · exact (hC x (hKc ⟨hx, not_lt.mp hh⟩)).trans (le_max_left _ _)

end Bounds

section Measurability

variable (L : Type) [Field L] [NumberField L]

private theorem stronglyMeasurable_setIntegral_of_continuous [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] [SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [SFinite νZL] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ) (hf : Continuous f) :
    StronglyMeasurable fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => ∫ z in ΩL, f (x, z) ∂νZL := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  exact hf.stronglyMeasurable.integral_prod_right'

private theorem stronglyMeasurable_setIntegral_curried [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] [SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [SFinite νZL] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hg : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => g p.1 p.2) :
    StronglyMeasurable fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => ∫ z in ΩL, g x z ∂νZL :=
  stronglyMeasurable_setIntegral_of_continuous L νZL ΩL (fun p => g p.1 p.2) hg

end Measurability

section Continuity

private theorem continuous_mul_comp₂ {X Y W : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    {c : Y → ℂ} (hc : Continuous c) (G : X → W → ℂ) (hG : Continuous fun q : X × W => G q.1 q.2)
    (a : Y → X → W) (ha : Continuous fun q : Y × X => a q.1 q.2) :
    Continuous fun p : X × Y => c p.2 * G p.1 (a p.2 p.1) :=
  (hc.comp continuous_snd).mul (hG.comp (continuous_fst.prodMk (ha.comp (continuous_snd.prodMk continuous_fst))))

end Continuity

end OffBorelFold

end OffBorel

section IdeleTopology

set_option autoImplicit false

namespace IdeleTopology

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_units_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end IdeleTopology

end IdeleTopology

section BorelNormClasses

set_option autoImplicit false

open Polynomial

namespace BorelNormClasses

section Triangular

variable {L : Type*} [Field L]

private theorem sigmaPartialNorm_entries_of_upper (σ : L →+* L) (δ : GL (Fin 2) L)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (p : Lˣ) (hp : (p : L) = δ 0 0) (r : ℕ) :
    (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ r) 1 0 = 0 ∧
      (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ r) 0 0
        = ((LT.TwistedNorm.sigmaPartialNorm (Units.map (σ : L →* L)) p r : Lˣ) : L) := by
  induction r with
  | zero => simp
  | succ r ih =>
      obtain ⟨ih10, ih00⟩ := ih
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', LT.TwistedNorm.sigmaPartialNorm_succ']
      constructor
      · change ((δ : Matrix (Fin 2) (Fin 2) L) *
          ((Matrix.GeneralLinearGroup.map σ (LT.TwistedNorm.sigmaPartialNorm
            (Matrix.GeneralLinearGroup.map σ) δ r) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
          Matrix.GeneralLinearGroup.map_apply, hδ, ih10, map_zero, mul_zero, zero_mul, add_zero]
      · change ((δ : Matrix (Fin 2) (Fin 2) L) *
          ((Matrix.GeneralLinearGroup.map σ (LT.TwistedNorm.sigmaPartialNorm
            (Matrix.GeneralLinearGroup.map σ) δ r) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) 0 0
          = ((p * Units.map (σ : L →* L) (LT.TwistedNorm.sigmaPartialNorm (Units.map (σ : L →* L)) p r) :
              Lˣ) : L)
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
          Matrix.GeneralLinearGroup.map_apply, ih10, map_zero, mul_zero, add_zero, ih00, Units.val_mul,
          Units.coe_map, MonoidHom.coe_coe, hp]

private theorem apply_zero_zero_ne_zero_of_upper (δ : GL (Fin 2) L)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero
  rw [Matrix.det_fin_two, hδ, mul_zero, sub_zero] at hdet
  exact left_ne_zero_of_mul hdet

end Triangular

section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem sigmaNormPow_entries_of_upper {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ) 1 0
        = 0 ∧
      (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ) 0 0
        = algebraMap F L (Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0)) := by
  have hp0 := apply_zero_zero_ne_zero_of_upper δ hδ
  obtain ⟨h10, h00⟩ := sigmaPartialNorm_entries_of_upper (σ : L →+* L) δ hδ (Units.mk0 _ hp0)
    (Units.val_mk0 hp0) (Module.finrank F L)
  refine ⟨h10, ?_⟩
  rw [LT.TwistedNorm.sigmaNormPow_def, h00, ← LT.TwistedNorm.sigmaNormPow_def,
    LT.TwistedNorm.coe_sigmaNormPow_units_eq_algebraMap_norm hgen, Units.val_mk0]

private theorem isRoot_charpoly_normRep_of_upper {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((LT.TwistedNorm.normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly.IsRoot
      (Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0)) := by
  obtain ⟨P, hP⟩ := LT.TwistedNorm.isNormRep_normRep hgen δ
  have hch := LT.TwistedNorm.charpoly_map_eq_charpoly_of_conj_eq_map hP
  obtain ⟨hN10, hN00⟩ := sigmaNormPow_entries_of_upper hgen δ hδ
  rw [Polynomial.IsRoot.def]
  apply (algebraMap F L).injective
  rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hch, ← hN00, Matrix.eval_charpoly,
    Matrix.det_fin_two]
  simp [Matrix.scalar_apply, hN10]

private theorem not_mem_ellipticCell_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L}
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) {γ : GL (Fin 2) F}
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    γ ∉ AutomorphicForm.ellipticCell F := by
  rw [LT.TwistedNorm.normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  have hchar : (γ : Matrix (Fin 2) (Fin 2) F).charpoly
      = ((LT.TwistedNorm.normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly := by
    rw [← hc, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  intro hγ
  have hroot := isRoot_charpoly_normRep_of_upper hgen δ hδ
  rw [← hchar] at hroot
  exact (AutomorphicForm.mem_ellipticCell_iff.mp hγ) _ hroot

private theorem setOf_upper_ellipticOrCentral_eq_setOf_upper_central {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) :
    {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) F,
        (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
      = {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) F,
        γ ∈ AutomorphicForm.centralCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  ext δ
  constructor
  · rintro ⟨h10, γ, hγ | hγ, hcls⟩
    · exact absurd hγ (not_mem_ellipticCell_of_normClassMap_mk_eq hgen h10 hcls)
    · exact ⟨h10, γ, hγ, hcls⟩
  · rintro ⟨h10, γ, hγ, hcls⟩
    exact ⟨h10, γ, Or.inr hγ, hcls⟩

end Galois

end BorelNormClasses

end BorelNormClasses

section BorelNormSubspace

set_option autoImplicit false

open Finset

namespace BorelNormSubspace

section Triangular

variable {L : Type*} [Field L]

private theorem apply_one_one_ne_zero_of_upper (δ : GL (Fin 2) L)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero
  rw [Matrix.det_fin_two, hδ, mul_zero, sub_zero] at hdet
  exact right_ne_zero_of_mul hdet

private theorem sigmaPartialNorm_apply_one_one_of_upper (σ : L →+* L) (δ : GL (Fin 2) L)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (d : Lˣ) (hd : (d : L) = δ 1 1) (r : ℕ) :
    (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ r) 1 1
      = ((LT.TwistedNorm.sigmaPartialNorm (Units.map (σ : L →* L)) d r : Lˣ) : L) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', LT.TwistedNorm.sigmaPartialNorm_succ']
      change ((δ : Matrix (Fin 2) (Fin 2) L) *
          ((Matrix.GeneralLinearGroup.map σ (LT.TwistedNorm.sigmaPartialNorm
            (Matrix.GeneralLinearGroup.map σ) δ r) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) 1 1
          = ((d * Units.map (σ : L →* L) (LT.TwistedNorm.sigmaPartialNorm (Units.map (σ : L →* L)) d r) :
              Lˣ) : L)
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
        Matrix.GeneralLinearGroup.map_apply, hδ, zero_mul, zero_add, ih, Units.val_mul, Units.coe_map,
        MonoidHom.coe_coe, hd]

private theorem exists_forall_sigmaPartialNorm_apply_zero_one_eq (σ : L →+* L) (p : L) (d : Lˣ) (r : ℕ) :
    ∃ C : ℕ → L, (0 < r → C 0 ≠ 0) ∧ ∀ δ : GL (Fin 2) L, (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 →
      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = p → (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = d →
      (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ r) 0 1
        = ∑ i ∈ range r, C i * (⇑σ)^[i] ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) := by
  induction r with
  | zero => exact ⟨fun _ => 0, fun h => absurd h (lt_irrefl 0), fun δ _ _ _ => by simp⟩
  | succ r ih =>
      obtain ⟨C, -, hC⟩ := ih
      refine ⟨fun i => if i = 0 then σ ((LT.TwistedNorm.sigmaPartialNorm (Units.map (σ : L →* L)) d r : Lˣ) : L)
          else p * σ (C (i - 1)), fun _ => ?_, fun δ hδ hp hd => ?_⟩
      · simp only [if_true]
        exact (map_ne_zero σ).mpr (Units.ne_zero _)
      · have h11 := sigmaPartialNorm_apply_one_one_of_upper σ δ hδ d hd.symm r
        have h01 := hC δ hδ hp hd
        rw [LT.TwistedNorm.sigmaPartialNorm_succ']
        change ((δ : Matrix (Fin 2) (Fin 2) L) *
            ((Matrix.GeneralLinearGroup.map σ (LT.TwistedNorm.sigmaPartialNorm
              (Matrix.GeneralLinearGroup.map σ) δ r) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) 0 1 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
          Matrix.GeneralLinearGroup.map_apply, h01, h11, hp, sum_range_succ']
        simp only [if_true, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
          Function.iterate_zero_apply, Function.iterate_succ_apply', map_sum, map_mul, mul_sum, mul_assoc]
        ring

end Triangular

section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem exists_sum_mul_pow_apply_ne_zero {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (C : ℕ → L) (hC0 : C 0 ≠ 0) :
    ∃ q : L, ∑ i ∈ range (Module.finrank F L), C i * (σ ^ i) q ≠ 0 := by
  classical
  have horder : orderOf σ = Module.finrank F L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank F L]
  have hpos : 0 < Module.finrank F L := Module.finrank_pos
  let g : Fin (Module.finrank F L) → (L →* L) := fun i => MonoidHomClass.toMonoidHom (σ ^ (i : ℕ))
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    refine pow_injOn_Iio_orderOf (x := σ) (by rw [horder]; exact i.2) (by rw [horder]; exact j.2) ?_
    show σ ^ (i : ℕ) = σ ^ (j : ℕ)
    exact AlgEquiv.ext fun x => DFunLike.congr_fun hij x
  have hli : LinearIndependent L (fun i => ⇑(g i)) := (linearIndependent_monoidHom L L).comp g hg
  by_contra h
  have h' : ∀ q : L, ∑ i ∈ range (Module.finrank F L), C i * (σ ^ i) q = 0 := fun q =>
    not_not.mp fun hq => h ⟨q, hq⟩
  have hzero : ∑ i : Fin (Module.finrank F L), C i • ⇑(g i) = (0 : L → L) := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hq := h' q
    rw [sum_range] at hq
    exact hq
  exact hC0 (by simpa using Fintype.linearIndependent_iff.mp hli (fun i => C i) hzero ⟨0, hpos⟩)

private theorem sigmaNormPow_apply_zero_one_eq_zero_of_central {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) L)
    (h : ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.centralCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ) 0 1
      = 0 := by
  obtain ⟨γ, hγ, hcls⟩ := h
  obtain ⟨c, hc⟩ := AutomorphicForm.mem_centralCell_iff.mp hγ
  rw [LT.TwistedNorm.normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hcls
  obtain ⟨Q, hQ⟩ := hcls
  obtain ⟨P, hP⟩ := LT.TwistedNorm.isNormRep_normRep hgen δ

  have hrep : ((LT.TwistedNorm.normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : LT.TwistedNorm.normRep hgen δ = Q⁻¹ * γ * Q := by
      rw [← hQ]
      group
    rw [h1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  have hmap : ((Matrix.GeneralLinearGroup.map (algebraMap F L) (LT.TwistedNorm.normRep hgen δ) :
      GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hrep]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp

  have hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ
      = P * Matrix.GeneralLinearGroup.map (algebraMap F L) (LT.TwistedNorm.normRep hgen δ) * P⁻¹ := by
    rw [← hP]
    group
  rw [hN, Units.val_mul, Units.val_mul, hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv,
    Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_zero]

private theorem exists_submodule_ne_top_forall_apply_zero_one_mem {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (p : L) (d : Lˣ) :
    ∃ W : Submodule F L, W ≠ ⊤ ∧ ∀ δ : GL (Fin 2) L, (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 →
      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = p → (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = d →
      (∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.centralCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) →
      (δ : Matrix (Fin 2) (Fin 2) L) 0 1 ∈ W := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_forall_sigmaPartialNorm_apply_zero_one_eq (σ : L →+* L) p d (Module.finrank F L)

  set ℓ : L →ₗ[F] L := ∑ i ∈ range (Module.finrank F L), C i • (σ ^ i).toLinearMap with hℓ
  have hℓ_apply : ∀ q : L, ℓ q = ∑ i ∈ range (Module.finrank F L), C i * (σ ^ i) q := by
    intro q
    rw [hℓ, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul]
  refine ⟨LinearMap.ker ℓ, ?_, fun δ hδ hp hd hcentral => ?_⟩
  · intro htop
    obtain ⟨q, hq⟩ := exists_sum_mul_pow_apply_ne_zero hgen C (hC0 Module.finrank_pos)
    apply hq
    rw [← hℓ_apply]
    exact LinearMap.mem_ker.mp (by rw [htop]; exact Submodule.mem_top)
  · rw [LinearMap.mem_ker, hℓ_apply]
    have h1 := sigmaNormPow_apply_zero_one_eq_zero_of_central hgen δ hcentral
    rw [LT.TwistedNorm.sigmaNormPow_def, hC δ hδ hp hd] at h1
    simp only [RingHom.coe_coe] at h1
    simp only [AlgEquiv.coe_pow]
    exact h1

end Galois

end BorelNormSubspace

end BorelNormSubspace

section SubspaceBallCount

set_option autoImplicit false

open Module NumberField NumberField.mixedEmbedding

namespace SubspaceBallCount

section Generic

variable {α : Type*}

private theorem ncard_le_of_injOn {n : ℕ} {N : ℤ} (_ : 0 ≤ N) (s : Set α) (ψ : α → Fin n → ℤ) (hψ : Set.InjOn ψ s)
    (hbound : ∀ a ∈ s, ∀ k, |ψ a k| ≤ N) : s.Finite ∧ s.ncard ≤ (2 * N + 1).toNat ^ n := by
  classical
  have hsub : ψ '' s ⊆ (Fintype.piFinset fun _ : Fin n => Finset.Icc (-N) N : Finset (Fin n → ℤ)) := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, Finset.coe_Icc, Set.mem_Icc, forall_const]
    intro k
    exact abs_le.mp (hbound a ha k)
  refine ⟨Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hψ, ?_⟩
  calc s.ncard = (ψ '' s).ncard := hψ.ncard_image.symm
    _ ≤ ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-N) N : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (2 * N + 1).toNat ^ n := by
        rw [Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        rw [Int.card_Icc]
        congr 1
        ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem exists_forall_abs_apply_le (g : (ι → ℚ) →ₗ[ℚ] (κ → ℚ)) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (v : ι → ℚ) (B : ℝ), 0 ≤ B → (∀ j, |(v j : ℝ)| ≤ B) → ∀ i, |(g v i : ℝ)| ≤ G * B := by
  classical
  refine ⟨∑ i, ∑ j, |(g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)|, by positivity, fun v B hB hv i => ?_⟩
  have hv' : g v i = ∑ j, v j * g (fun l => if j = l then (1 : ℚ) else 0) i := by
    conv_lhs => rw [pi_eq_sum_univ v, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hv']
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |(v j : ℝ) * (g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)|
      ≤ ∑ j, B * |(g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hv j) (abs_nonneg _)
    _ = (∑ j, |(g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)|) * B := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ (∑ i, ∑ j, |(g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)|) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact Finset.single_le_sum (f := fun i => ∑ j, |(g (fun l => if j = l then (1 : ℚ) else 0) i : ℝ)|)
          (fun _ _ => by positivity) (Finset.mem_univ i)

end Generic

section NumberField

variable (F : Type*) [Field F] [NumberField F]

private theorem exists_forall_abs_integralBasis_repr_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : F) (R : ℝ), (∀ w : InfinitePlace F, w x ≤ R) →
      ∀ i, |((integralBasis F).repr x i : ℝ)| ≤ C * R := by
  classical
  set e : mixedSpace F →L[ℝ] (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) :=
    ((latticeBasis F).equivFunL : mixedSpace F ≃L[ℝ] (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ)).toContinuousLinearMap
  refine ⟨‖e‖, norm_nonneg _, fun x R hR i => ?_⟩
  have h1 : ‖mixedEmbedding F x‖ ≤ R := by
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.sup'_le _ _ fun w _ => by rw [normAtPlace_apply]; exact hR w
  have h2 : ((integralBasis F).repr x i : ℝ) = e (mixedEmbedding F x) i := by
    rw [← latticeBasis_repr_apply]
    rfl
  rw [h2, ← Real.norm_eq_abs]
  calc ‖e (mixedEmbedding F x) i‖ ≤ ‖e (mixedEmbedding F x)‖ := norm_le_pi_norm _ i
    _ ≤ ‖e‖ * ‖mixedEmbedding F x‖ := e.le_opNorm _
    _ ≤ ‖e‖ * R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

private theorem _root_.SubspaceBallCount.exists_forall_ncard_le (V : Submodule ℚ F) :
    ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      {y : 𝓞 F | (y : F) ∈ V ∧ ∀ w : InfinitePlace F, w (y : F) ≤ R}.Finite ∧
        (({y : 𝓞 F | (y : F) ∈ V ∧ ∀ w : InfinitePlace F, w (y : F) ≤ R}.ncard : ℝ)) ≤
          C * (1 + R) ^ finrank ℚ V := by
  classical

  set φ : 𝓞 F →ₗ[ℤ] F := (Algebra.linearMap (𝓞 F) F).restrictScalars ℤ with hφ
  have hφinj : Function.Injective φ := fun a b h => RingOfIntegers.coe_injective h
  set M : Submodule ℤ (𝓞 F) := (V.restrictScalars ℤ).comap φ with hM
  have hmemM : ∀ y : 𝓞 F, y ∈ M ↔ (y : F) ∈ V := fun y => Iff.rfl
  obtain ⟨n, e⟩ := M.basisOfPid (RingOfIntegers.basis F)

  set v : Fin n → F := fun k => ((e k : 𝓞 F) : F) with hv
  have hvV : ∀ k, v k ∈ V := fun k => (hmemM _).mp (e k).2
  have hvind : LinearIndependent ℚ v := by
    have h1 : LinearIndependent ℤ ((φ ∘ₗ M.subtype) ∘ e) :=
      e.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (hφinj.comp Subtype.val_injective))
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have hn : n ≤ finrank ℚ V := by
    set vV : Fin n → V := fun k => ⟨v k, hvV k⟩ with hvV'
    have hind : LinearIndependent ℚ vV := by
      refine LinearIndependent.of_comp V.subtype ?_
      convert hvind using 1 <;> first | rfl | (funext k; rfl)
    simpa using hind.fintype_card_le_finrank

  set u : (Fin n → ℚ) →ₗ[ℚ] (Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ) :=
    ((integralBasis F).equivFun : F →ₗ[ℚ] (Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ)) ∘ₗ Fintype.linearCombination ℚ v
    with hu
  have huker : LinearMap.ker u = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h1 : ∑ k, c k • v k = 0 := by
      have h2 : (integralBasis F).equivFun (∑ k, c k • v k) = 0 := by
        simpa [hu, Fintype.linearCombination_apply] using hc
      exact (integralBasis F).equivFun.map_eq_zero_iff.mp h2
    exact funext (Fintype.linearIndependent_iff.mp hvind c h1)
  obtain ⟨g, hg⟩ := u.exists_leftInverse_of_injective huker
  obtain ⟨G, hG0, hG⟩ := exists_forall_abs_apply_le g
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_forall_abs_integralBasis_repr_le F

  set ψ : 𝓞 F → Fin n → ℤ := fun y => if h : y ∈ M then e.equivFun ⟨y, h⟩ else 0 with hψ
  refine ⟨(2 * (G * C₁) + 1) ^ n, fun R hR => ?_⟩
  set S : Set (𝓞 F) := {y : 𝓞 F | (y : F) ∈ V ∧ ∀ w : InfinitePlace F, w (y : F) ≤ R} with hS
  have hinj : Set.InjOn ψ S := by
    intro y₁ hy₁ y₂ hy₂ h
    have h₁ : y₁ ∈ M := (hmemM y₁).mpr hy₁.1
    have h₂ : y₂ ∈ M := (hmemM y₂).mpr hy₂.1
    simp only [hψ, dif_pos h₁, dif_pos h₂] at h
    exact congrArg Subtype.val (e.equivFun.injective h)
  set N : ℤ := ⌊G * (C₁ * R)⌋ with hN
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (by positivity)
  have hbound : ∀ y ∈ S, ∀ k, |ψ y k| ≤ N := by
    intro y hy k
    have hyM : y ∈ M := (hmemM y).mpr hy.1
    simp only [hψ, dif_pos hyM]

    set c : Fin n → ℤ := e.equivFun ⟨y, hyM⟩ with hc
    have hy' : (y : F) = ∑ k, (c k : ℚ) • v k := by
      have h1 : (⟨y, hyM⟩ : M) = ∑ k, c k • e k := (e.sum_equivFun ⟨y, hyM⟩).symm
      have h2 : (y : F) = φ ((⟨y, hyM⟩ : M) : 𝓞 F) := rfl
      rw [h2, h1, Submodule.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, map_smul, Int.cast_smul_eq_zsmul]
      rfl

    have hcg : (fun k => (c k : ℚ)) = g ((integralBasis F).equivFun (y : F)) := by
      have h1 : u (fun k => (c k : ℚ)) = (integralBasis F).equivFun (y : F) := by
        simp only [hu, LinearMap.comp_apply, Fintype.linearCombination_apply, LinearEquiv.coe_coe, hy']
      rw [← h1]
      exact (LinearMap.congr_fun hg _).symm
    have hrepr : ∀ j, |(((integralBasis F).equivFun (y : F)) j : ℝ)| ≤ C₁ * R := fun j => by
      rw [Basis.equivFun_apply]
      exact hC₁ _ R hy.2 j
    have h3 := hG ((integralBasis F).equivFun (y : F)) (C₁ * R) (by positivity) hrepr k
    rw [← hcg] at h3
    beta_reduce at h3
    have h4 : |(c k : ℝ)| ≤ G * (C₁ * R) := by exact_mod_cast h3
    rw [hN, Int.le_floor]
    exact_mod_cast h4
  obtain ⟨hSfin, hcount⟩ := ncard_le_of_injOn hN0 S ψ hinj hbound
  refine ⟨hSfin, ?_⟩

  have hNle : (N : ℝ) ≤ G * (C₁ * R) := Int.floor_le _
  have h2N : (((2 * N + 1).toNat : ℤ) : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
    norm_num
  calc (S.ncard : ℝ) ≤ (((2 * N + 1).toNat ^ n : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (2 * (N : ℝ) + 1) ^ n := by
        rw [Nat.cast_pow]
        congr 1
    _ ≤ ((2 * (G * C₁) + 1) * (1 + R)) ^ n := by
        refine pow_le_pow_left₀ (by positivity) ?_ n
        nlinarith [mul_nonneg hG0 hC₁0]
    _ = (2 * (G * C₁) + 1) ^ n * (1 + R) ^ n := mul_pow _ _ _
    _ ≤ (2 * (G * C₁) + 1) ^ n * (1 + R) ^ finrank ℚ V := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hn) (by positivity)

p2m_export "SubspaceBallCount" "exists_forall_ncard_le"
end NumberField

end SubspaceBallCount

end SubspaceBallCount

section BalancedExtraction

set_option autoImplicit false

open Finset

namespace BalancedExtraction

section Matrices

variable {K : Type*} [NormedField K]

private theorem norm_mul_apply_le (P Q : Matrix (Fin 2) (Fin 2) K) {i j : Fin 2} {α β : ℝ}
    (hP : ∀ a, ‖P i a‖ ≤ α) (hQ : ∀ a, ‖Q a j‖ ≤ β) (hα : 0 ≤ α) : ‖(P * Q) i j‖ ≤ 2 * (α * β) := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hQ 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  calc ‖P i 0 * Q 0 j + P i 1 * Q 1 j‖ ≤ ‖P i 0 * Q 0 j‖ + ‖P i 1 * Q 1 j‖ := norm_add_le _ _
    _ = ‖P i 0‖ * ‖Q 0 j‖ + ‖P i 1‖ * ‖Q 1 j‖ := by rw [norm_mul, norm_mul]
    _ ≤ α * β + α * β :=
        add_le_add (mul_le_mul (hP 0) (hQ 0) (norm_nonneg _) hα) (mul_le_mul (hP 1) (hQ 1) (norm_nonneg _) hα)
    _ = 2 * (α * β) := by ring

private theorem norm_coe_inv_apply_le (y : GL (Fin 2) K) {A D m : ℝ} (hm : 0 < m)
    (hdet : m ≤ ‖(y : Matrix (Fin 2) (Fin 2) K).det‖)
    (htop : ∀ j, ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖ ≤ A) (hbot : ∀ j, ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖ ≤ D) :
    (∀ a, ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a 0‖ ≤ D / m) ∧
      ∀ a, ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a 1‖ ≤ A / m := by
  have hinv : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((y : Matrix (Fin 2) (Fin 2) K).det)⁻¹ • (y : Matrix (Fin 2) (Fin 2) K).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  have hscale : ∀ (e : K) (B : ℝ), ‖e‖ ≤ B → ‖((y : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * e‖ ≤ B / m := by
    intro e B he
    rw [norm_mul, norm_inv, div_eq_inv_mul]
    exact mul_le_mul (inv_anti₀ hm hdet) he (norm_nonneg _) (inv_nonneg.mpr hm.le)
  rw [hinv]
  simp only [Matrix.smul_apply, Matrix.adjugate_fin_two, smul_eq_mul]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · fin_cases a
    · simpa using hscale ((y : Matrix (Fin 2) (Fin 2) K) 1 1) D (hbot 1)
    · simpa using hscale (-(y : Matrix (Fin 2) (Fin 2) K) 1 0) D (by rw [norm_neg]; exact hbot 0)
  · fin_cases a
    · simpa using hscale (-(y : Matrix (Fin 2) (Fin 2) K) 0 1) A (by rw [norm_neg]; exact htop 1)
    · simpa using hscale ((y : Matrix (Fin 2) (Fin 2) K) 0 0) A (htop 0)

private theorem norm_mul_mul_inv_apply_le (y k y' : GL (Fin 2) K) {A D m M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hytop : ∀ j, ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖ ≤ A) (hybot : ∀ j, ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖ ≤ D)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ M)
    (hdet : m ≤ ‖(y' : Matrix (Fin 2) (Fin 2) K).det‖)
    (hy'top : ∀ j, ‖(y' : Matrix (Fin 2) (Fin 2) K) 0 j‖ ≤ A)
    (hy'bot : ∀ j, ‖(y' : Matrix (Fin 2) (Fin 2) K) 1 j‖ ≤ D) :
    ‖((y * k * y'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≤ 4 * M * (A * D) / m ∧
      ‖((y * k * y'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1‖ ≤ 4 * M * (A * A) / m ∧
      ‖((y * k * y'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ 4 * M * (A * D) / m := by
  obtain ⟨hcol0, hcol1⟩ := norm_coe_inv_apply_le y' hm hdet hy'top hy'bot
  have hyk0 : ∀ a, ‖((y : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) 0 a‖ ≤ 2 * (A * M) :=
    fun a => norm_mul_apply_le _ _ hytop (fun b => hk b a) hA
  have hyk1 : ∀ a, ‖((y : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) 1 a‖ ≤ 2 * (D * M) :=
    fun a => norm_mul_apply_le _ _ hybot (fun b => hk b a) hD
  have hcoe : ((y * k * y'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (y : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) *
          ((y'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul, Units.val_mul]
  rw [hcoe]
  have h2AM : 0 ≤ 2 * (A * M) := by positivity
  have h2DM : 0 ≤ 2 * (D * M) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (norm_mul_apply_le _ _ hyk0 hcol0 h2AM).trans (le_of_eq ?_)
    ring
  · refine (norm_mul_apply_le _ _ hyk0 hcol1 h2AM).trans (le_of_eq ?_)
    ring
  · refine (norm_mul_apply_le _ _ hyk1 hcol1 h2DM).trans (le_of_eq ?_)
    ring

end Matrices

section Weights

variable {ι : Type*} [Fintype ι]

private theorem weight_mul_weight_le {c u h : ℝ} (hc : 0 < c) (hh : c ≤ h) :
    Real.sqrt (u ^ 2 / c + h) * (Real.sqrt h)⁻¹ ≤ Real.sqrt (1 + u ^ 2 / c ^ 2) := by
  have hh0 : 0 < h := hc.trans_le hh
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  rw [← div_eq_mul_inv, div_le_iff₀ hsh, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + u ^ 2 / c ^ 2)]
  refine Real.sqrt_le_sqrt ?_
  have h1 : u ^ 2 / c ≤ u ^ 2 / c ^ 2 * h := by
    rw [div_le_iff₀ hc, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc u ^ 2 * c ^ 2 = u ^ 2 * c * c := by ring
      _ ≤ u ^ 2 * h * c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (sq_nonneg u)) hc.le
  rw [add_mul, one_mul, add_comm]
  exact add_le_add_right h1 h

private theorem prod_height_le_prod_weight_div_weight {c u : ℝ} (hc : 0 < c) (h : ι → ℝ) (hh : ∀ w, c ≤ h w)
    (mult : ι → ℕ) :
    ∏ w, h w ^ mult w ≤ ∏ w, (Real.sqrt (u ^ 2 / c + h w) / (Real.sqrt (h w))⁻¹) ^ mult w ∧
      ∏ w, (Real.sqrt (u ^ 2 / c + h w) / (Real.sqrt (h w))⁻¹) ^ mult w
        ≤ Real.sqrt (1 + u ^ 2 / c ^ 2) ^ (∑ w, mult w) * ∏ w, h w ^ mult w := by
  have hratio : ∀ w, Real.sqrt (u ^ 2 / c + h w) / (Real.sqrt (h w))⁻¹
      = Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w) := fun w => by rw [div_inv_eq_mul]
  have hh0 : ∀ w, 0 < h w := fun w => hc.trans_le (hh w)

  have hlow : ∀ w, h w ≤ Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w) := by
    intro w
    calc h w = Real.sqrt (h w) * Real.sqrt (h w) := (Real.mul_self_sqrt (hh0 w).le).symm
      _ ≤ Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (le_add_of_nonneg_left (by positivity)))
            (Real.sqrt_nonneg _)
  have hup : ∀ w, Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w) ≤ Real.sqrt (1 + u ^ 2 / c ^ 2) * h w := by
    intro w
    have hsh : 0 < Real.sqrt (h w) := Real.sqrt_pos.mpr (hh0 w)
    have h1 := weight_mul_weight_le (u := u) hc (hh w)
    rw [← div_eq_mul_inv, div_le_iff₀ hsh] at h1
    calc Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w)
        ≤ Real.sqrt (1 + u ^ 2 / c ^ 2) * Real.sqrt (h w) * Real.sqrt (h w) := mul_le_mul_of_nonneg_right h1 hsh.le
      _ = Real.sqrt (1 + u ^ 2 / c ^ 2) * h w := by rw [mul_assoc, Real.mul_self_sqrt (hh0 w).le]
  simp only [hratio]
  constructor
  · refine prod_le_prod (fun w _ => pow_nonneg (hh0 w).le _) fun w _ => ?_
    exact pow_le_pow_left₀ (hh0 w).le (hlow w) _
  · calc ∏ w, (Real.sqrt (u ^ 2 / c + h w) * Real.sqrt (h w)) ^ mult w
        ≤ ∏ w, (Real.sqrt (1 + u ^ 2 / c ^ 2) * h w) ^ mult w := by
          refine prod_le_prod (fun w _ => by positivity) fun w _ => ?_
          exact pow_le_pow_left₀ (by positivity) (hup w) _
      _ = Real.sqrt (1 + u ^ 2 / c ^ 2) ^ (∑ w, mult w) * ∏ w, h w ^ mult w := by
          simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]

private theorem prod_height_le_div_pow {c u A D : ℝ} (hc : 0 < c) (h : ι → ℝ) (hh : ∀ w, c ≤ h w) (mult : ι → ℕ)
    (hA : A ^ (∑ w, mult w) = ∏ w, Real.sqrt (u ^ 2 / c + h w) ^ mult w)
    (hD : D ^ (∑ w, mult w) = ∏ w, (Real.sqrt (h w))⁻¹ ^ mult w) :
    ∏ w, h w ^ mult w ≤ (A / D) ^ (∑ w, mult w) ∧
      (A / D) ^ (∑ w, mult w) ≤ Real.sqrt (1 + u ^ 2 / c ^ 2) ^ (∑ w, mult w) * ∏ w, h w ^ mult w := by
  have hkey : (A / D) ^ (∑ w, mult w) = ∏ w, (Real.sqrt (u ^ 2 / c + h w) / (Real.sqrt (h w))⁻¹) ^ mult w := by
    rw [div_pow, hA, hD, ← prod_div_distrib]
    simp only [div_pow]
  rw [hkey]
  exact prod_height_le_prod_weight_div_weight hc h hh mult

end Weights

end BalancedExtraction

end BalancedExtraction

section ContributorCount

set_option autoImplicit false

open Module NumberField

namespace ContributorCount

section Generic

variable {α ι : Type*}

private theorem ncard_biUnion_le (I : Finset ι) (t : ι → Set α) (ht : ∀ i, (t i).Finite) :
    (⋃ i ∈ I, t i).ncard ≤ ∑ i ∈ I, (t i).ncard := by
  classical
  have hsub : (⋃ i ∈ I, t i) ⊆ ((I.biUnion fun i => (ht i).toFinset : Finset α) : Set α) := by
    intro a ha
    simp only [Set.mem_iUnion, exists_prop] at ha
    obtain ⟨i, hi, hai⟩ := ha
    simp only [Finset.coe_biUnion, Finset.mem_coe, Set.Finite.coe_toFinset, Set.mem_iUnion, exists_prop]
    exact ⟨i, hi, hai⟩
  calc (⋃ i ∈ I, t i).ncard ≤ (((I.biUnion fun i => (ht i).toFinset : Finset α) : Set α)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (I.biUnion fun i => (ht i).toFinset).card := Set.ncard_coe_finset _
    _ ≤ ∑ i ∈ I, ((ht i).toFinset).card := Finset.card_biUnion_le
    _ = ∑ i ∈ I, (t i).ncard := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Set.ncard_eq_toFinset_card _ (ht i)]

end Generic

section Count

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

omit [NumberField L] in

private theorem ext_of_upper {δ δ' : GL (Fin 2) L} (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h10' : (δ' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h00 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (δ' : Matrix (Fin 2) (Fin 2) L) 0 0)
    (h11 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ' : Matrix (Fin 2) (Fin 2) L) 1 1)
    (h01 : (δ : Matrix (Fin 2) (Fin 2) L) 0 1 = (δ' : Matrix (Fin 2) (Fin 2) L) 0 1) : δ = δ' := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10.trans h10'.symm
  · exact h11

private theorem finite_setOf_bounded_integral (s₀ : 𝓞 L) (hs₀ : s₀ ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    {x : L | (∃ y : 𝓞 L, (y : L) = (s₀ : L) * x) ∧ ∀ w : InfinitePlace L, w x ≤ R₀}.Finite := by
  set Ms : ℝ := ∑ w : InfinitePlace L, w (s₀ : L)
  have hMs_le : ∀ w : InfinitePlace L, w (s₀ : L) ≤ Ms := fun w =>
    Finset.single_le_sum (fun w' _ => apply_nonneg w' (s₀ : L)) (Finset.mem_univ w)
  have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun w _ => apply_nonneg w _
  obtain ⟨C, hC⟩ := SubspaceBallCount.exists_forall_ncard_le L (⊤ : Submodule ℚ L)
  have hfin := (hC (Ms * R₀) (mul_nonneg hMs0 hR₀)).1
  have hs₀' : (s₀ : L) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs₀
  refine (hfin.image fun y : 𝓞 L => (y : L) / (s₀ : L)).subset ?_
  rintro x ⟨⟨y, hy⟩, hx⟩
  refine ⟨y, ⟨Submodule.mem_top, fun w => ?_⟩, ?_⟩
  · rw [hy, map_mul]
    exact mul_le_mul (hMs_le w) (hx w) (apply_nonneg w _) hMs0
  · show (y : L) / (s₀ : L) = x
    rw [hy, mul_div_cancel_left₀ _ hs₀']

private theorem exists_forall_ncard_le_of_diag {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (s₀ : 𝓞 L) (hs₀ : s₀ ≠ 0) (p r : L) (hr : r ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ S : Set (GL (Fin 2) L),
      (∀ δ ∈ S, (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = p ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = r ∧
        (∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ∧
        (∀ w : InfinitePlace L, w ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) ≤ ρ) ∧
        ∃ y : 𝓞 L, (y : L) = (s₀ : L) * (δ : Matrix (Fin 2) (Fin 2) L) 0 1) →
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (1 + ρ) ^ (finrank ℚ L - 1) := by
  obtain ⟨W, hWtop, hW⟩ := BorelNormSubspace.exists_submodule_ne_top_forall_apply_zero_one_mem hgen p (Units.mk0 r hr)
  have hs₀' : (s₀ : L) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs₀

  set V : Submodule ℚ L := (W.map (LinearMap.mulLeft K (s₀ : L))).restrictScalars ℚ with hV
  have hVtop : V ≠ ⊤ := by
    intro hV'
    apply hWtop
    rw [Submodule.restrictScalars_eq_top_iff] at hV'
    rw [Submodule.eq_top_iff']
    intro x
    have hx : (s₀ : L) * x ∈ W.map (LinearMap.mulLeft K (s₀ : L)) := by rw [hV']; exact Submodule.mem_top
    obtain ⟨x', hx', hxx'⟩ := Submodule.mem_map.mp hx
    have : x' = x := mul_left_cancel₀ hs₀' hxx'
    exact this ▸ hx'
  have hVrank : finrank ℚ V ≤ finrank ℚ L - 1 := Nat.le_sub_one_of_lt (Submodule.finrank_lt hVtop)
  set Ms : ℝ := ∑ w : InfinitePlace L, w (s₀ : L)
  have hMs_le : ∀ w : InfinitePlace L, w (s₀ : L) ≤ Ms := fun w =>
    Finset.single_le_sum (fun w' _ => apply_nonneg w' _) (Finset.mem_univ w)
  have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun w _ => apply_nonneg w _
  obtain ⟨C, hC⟩ := SubspaceBallCount.exists_forall_ncard_le L V
  refine ⟨max C 0 * (1 + Ms) ^ (finrank ℚ L - 1), by positivity, fun ρ hρ S hS => ?_⟩
  obtain ⟨hYfin, hYcard⟩ := hC (Ms * ρ) (mul_nonneg hMs0 hρ)

  set ψ : GL (Fin 2) L → L := fun δ => (s₀ : L) * (δ : Matrix (Fin 2) (Fin 2) L) 0 1 with hψ
  have hinj : Set.InjOn ψ S := by
    intro δ hδ δ' hδ' h
    simp only [hψ] at h
    obtain ⟨h10, h00, h11, -, -, -⟩ := hS δ hδ
    obtain ⟨h10', h00', h11', -, -, -⟩ := hS δ' hδ'
    exact ext_of_upper h10 h10' (h00.trans h00'.symm) (h11.trans h11'.symm) (mul_left_cancel₀ hs₀' h)
  have himg : ψ '' S ⊆ (fun y : 𝓞 L => (y : L)) ''
      {y : 𝓞 L | (y : L) ∈ V ∧ ∀ w : InfinitePlace L, w (y : L) ≤ Ms * ρ} := by
    rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨h10, h00, h11, hcentral, hbound, y, hy⟩ := hS δ hδ
    refine ⟨y, ⟨?_, fun w => ?_⟩, hy⟩
    · rw [hy, hV, Submodule.restrictScalars_mem]
      exact Submodule.mem_map.mpr ⟨_, hW δ h10 h00 h11 hcentral, rfl⟩
    · rw [hy, map_mul]
      exact mul_le_mul (hMs_le w) (hbound w) (apply_nonneg w _) hMs0
  have hSfin : S.Finite := Set.Finite.of_finite_image ((hYfin.image _).subset himg) hinj
  refine ⟨hSfin, ?_⟩
  have hcount : S.ncard ≤ {y : 𝓞 L | (y : L) ∈ V ∧ ∀ w : InfinitePlace L, w (y : L) ≤ Ms * ρ}.ncard := by
    calc S.ncard = (ψ '' S).ncard := (hinj.ncard_image).symm
      _ ≤ ((fun y : 𝓞 L => (y : L)) ''
            {y : 𝓞 L | (y : L) ∈ V ∧ ∀ w : InfinitePlace L, w (y : L) ≤ Ms * ρ}).ncard :=
          Set.ncard_le_ncard himg (hYfin.image _)
      _ ≤ _ := Set.ncard_image_le hYfin
  have h1ρ : (1 : ℝ) ≤ 1 + ρ := by linarith
  have h1Ms : (1 : ℝ) ≤ 1 + Ms := by linarith
  calc (S.ncard : ℝ) ≤ ({y : 𝓞 L | (y : L) ∈ V ∧ ∀ w : InfinitePlace L, w (y : L) ≤ Ms * ρ}.ncard : ℝ) := by
        exact_mod_cast hcount
    _ ≤ C * (1 + Ms * ρ) ^ finrank ℚ V := hYcard
    _ ≤ max C 0 * ((1 + Ms) * (1 + ρ)) ^ (finrank ℚ L - 1) := by
        have hle : 1 + Ms * ρ ≤ (1 + Ms) * (1 + ρ) := by nlinarith
        have h1 : (1 + Ms * ρ) ^ finrank ℚ V ≤ ((1 + Ms) * (1 + ρ)) ^ finrank ℚ V :=
          pow_le_pow_left₀ (by positivity) hle _
        have h2 : ((1 + Ms) * (1 + ρ)) ^ finrank ℚ V ≤ ((1 + Ms) * (1 + ρ)) ^ (finrank ℚ L - 1) :=
          pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le h1Ms h1ρ) hVrank
        calc C * (1 + Ms * ρ) ^ finrank ℚ V ≤ max C 0 * (1 + Ms * ρ) ^ finrank ℚ V :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max C 0 * ((1 + Ms) * (1 + ρ)) ^ (finrank ℚ L - 1) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (le_max_right _ _)
    _ = max C 0 * (1 + Ms) ^ (finrank ℚ L - 1) * (1 + ρ) ^ (finrank ℚ L - 1) := by rw [mul_pow, mul_assoc]

private theorem _root_.ContributorCount.exists_forall_ncard_le {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (s₀ : 𝓞 L) (hs₀ : s₀ ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ∀ S : Set (GL (Fin 2) L),
      (∀ δ ∈ S, (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ∧
        (∀ w : InfinitePlace L, w ((δ : Matrix (Fin 2) (Fin 2) L) 0 0) ≤ R₀ ∧
          w ((δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≤ R₀ ∧ w ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) ≤ ρ) ∧
        ∀ i j : Fin 2, ∃ y : 𝓞 L, (y : L) = (s₀ : L) * (δ : Matrix (Fin 2) (Fin 2) L) i j) →
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (1 + ρ) ^ (finrank ℚ L - 1) := by
  classical
  set A₀ : Set L := {x : L | (∃ y : 𝓞 L, (y : L) = (s₀ : L) * x) ∧ ∀ w : InfinitePlace L, w x ≤ R₀}
  have hA₀fin : A₀.Finite := finite_setOf_bounded_integral s₀ hs₀ hR₀

  have hdiag : ∀ pr : L × L, ∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ∀ S : Set (GL (Fin 2) L),
      (∀ δ ∈ S, (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = pr.1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = pr.2 ∧
        (∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ∧
        (∀ w : InfinitePlace L, w ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) ≤ ρ) ∧
        ∃ y : 𝓞 L, (y : L) = (s₀ : L) * (δ : Matrix (Fin 2) (Fin 2) L) 0 1) →
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (1 + ρ) ^ (finrank ℚ L - 1) := by
    intro pr
    by_cases hr : pr.2 = 0
    · refine ⟨0, fun ρ _ S hS => ?_⟩
      have hempty : S = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro δ hδ
        obtain ⟨h10, -, h11, -⟩ := hS δ hδ
        exact BorelNormSubspace.apply_one_one_ne_zero_of_upper δ h10 (h11.trans hr)
      subst hempty
      simp
    · obtain ⟨C, -, hC⟩ := exists_forall_ncard_le_of_diag hgen s₀ hs₀ pr.1 pr.2 hr
      exact ⟨C, hC⟩
  choose Cf hCf using hdiag
  set pairs : Finset (L × L) := hA₀fin.toFinset ×ˢ hA₀fin.toFinset with hpairs
  refine ⟨∑ pr ∈ pairs, Cf pr, fun ρ hρ S hS => ?_⟩

  set slice : L × L → Set (GL (Fin 2) L) := fun pr =>
    {δ ∈ S | (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = pr.1 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = pr.2}
  have hslice_hyp : ∀ pr : L × L, (slice pr).Finite ∧
      ((slice pr).ncard : ℝ) ≤ Cf pr * (1 + ρ) ^ (finrank ℚ L - 1) := by
    intro pr
    refine hCf pr ρ hρ (slice pr) fun δ hδ => ?_
    obtain ⟨hδS, h00, h11⟩ : δ ∈ S ∧ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = pr.1 ∧
      (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = pr.2 := hδ
    obtain ⟨h10, hcentral, hbound, hint⟩ := hS δ hδS
    exact ⟨h10, h00, h11, hcentral, fun w => (hbound w).2.2, hint 0 1⟩
  have hcover : S ⊆ ⋃ pr ∈ pairs, slice pr := by
    intro δ hδ
    obtain ⟨h10, hcentral, hbound, hint⟩ := hS δ hδ
    have hmem : ((δ : Matrix (Fin 2) (Fin 2) L) 0 0, (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ∈ pairs := by
      rw [hpairs, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact ⟨⟨hint 0 0, fun w => (hbound w).1⟩, ⟨hint 1 1, fun w => (hbound w).2.1⟩⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨_, hmem, hδ, rfl, rfl⟩
  have hunion_fin : (⋃ pr ∈ pairs, slice pr).Finite :=
    Set.Finite.biUnion pairs.finite_toSet fun pr _ => (hslice_hyp pr).1
  refine ⟨hunion_fin.subset hcover, ?_⟩
  calc (S.ncard : ℝ) ≤ ((⋃ pr ∈ pairs, slice pr).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hcover hunion_fin
    _ ≤ ∑ pr ∈ pairs, ((slice pr).ncard : ℝ) := by
        exact_mod_cast ncard_biUnion_le pairs slice fun pr => (hslice_hyp pr).1
    _ ≤ ∑ pr ∈ pairs, Cf pr * (1 + ρ) ^ (finrank ℚ L - 1) :=
        Finset.sum_le_sum fun pr _ => (hslice_hyp pr).2
    _ = (∑ pr ∈ pairs, Cf pr) * (1 + ρ) ^ (finrank ℚ L - 1) := (Finset.sum_mul _ _ _).symm

p2m_export "ContributorCount" "exists_forall_ncard_le"
end Count

end ContributorCount

end ContributorCount

section KernelCountReduction

set_option autoImplicit false

open MeasureTheory NumberField Topology
open IsDedekindDomain
open scoped TensorProduct Pointwise NNReal

namespace KernelCountReduction

section Generic

private theorem norm_finsum_mem_le_ncard_mul {ι : Type*} (f : ι → ℂ) (T : Set ι)
    (hS : (T ∩ Function.support f).Finite) {B : ℝ} (hB : ∀ i, ‖f i‖ ≤ B) :
    ‖∑ᶠ i ∈ T, f i‖ ≤ ((T ∩ Function.support f).ncard : ℝ) * B := by
  rw [finsum_mem_eq_sum_of_subset f (t := hS.toFinset) (fun i hi => hS.mem_toFinset.mpr hi)
    (fun i hi => (hS.mem_toFinset.mp hi).1), Set.ncard_eq_toFinset_card _ hS]
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_le_card_nsmul hS.toFinset (fun i => ‖f i‖) B (fun i _ => hB i)
  rwa [nsmul_eq_mul] at h

end Generic

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem exists_forall_norm_setIntegral_le_mul_of_ncard_le (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    {Z : Set (AdeleRing (𝓞 L) L)ˣ} (hZm : MeasurableSet Z) (hvol : νZL (Z ∩ ΩL) < ⊤)
    {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    (hrep : ∀ z ∈ Z, ∃ η : Lˣ, ∃ w ∈ W,
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w)
    (hZ : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), ∀ z ∉ Z,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (hper : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (N : ℕ),
      (∀ w ∈ W, (T ∩ Function.support fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L w * x))).ncard ≤ N) →
      ‖∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL‖
        ≤ C * N := by
  obtain ⟨Mξ, hMξ⟩ := hW.exists_bound_of_continuousOn hξc.continuousOn
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB' : ∀ g, ‖φ g‖ ≤ max B 0 := fun g => (hB g).trans (le_max_left _ _)
  refine ⟨max Mξ 0 * max B 0 * νZL.real (ΩL ∩ Z),
    mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) measureReal_nonneg, ?_⟩
  intro x N hN
  set k : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) with hk
  have hkZ : k = Z.indicator k := by
    funext z
    by_cases hz : z ∈ Z
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hk]
      simp only [hZ x z hz, mul_zero]
  have hbound : ∀ z ∈ ΩL ∩ Z, ‖k z‖ ≤ max Mξ 0 * (N * max B 0) := by
    rintro z ⟨-, hz⟩
    obtain ⟨η, w, hw, rfl⟩ := hrep z hz
    have hξ : ξL ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w,
          Subgroup.mem_top _⟩ = ξL ⟨w, Subgroup.mem_top w⟩ := by
      rw [show (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w, Subgroup.mem_top _⟩ :
            (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ))
          = ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η, Subgroup.mem_top _⟩ *
            ⟨w, Subgroup.mem_top w⟩ from rfl,
        map_mul, hξt _ (MonoidHom.mem_range.mpr ⟨η, rfl⟩), one_mul]
    have hS : (T ∩ Function.support fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L w * x))).Finite := by
      refine (hfin (tsupport φ) hφs x (AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L w * x))).subset ?_
      rintro δ ⟨-, hδ⟩
      exact subset_tsupport φ hδ
    have hsum := norm_finsum_mem_le_ncard_mul _ T hS (fun _ => hB' _)
    rw [hk]
    dsimp only
    rw [hper x η w, norm_mul, hξ]
    refine mul_le_mul ((hMξ w hw).trans (le_max_left _ _)) (hsum.trans ?_) (norm_nonneg _) (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN w hw) (le_max_right _ _)
  have hint : ‖∫ z in ΩL, k z ∂νZL‖ ≤ max Mξ 0 * (N * max B 0) * νZL.real (ΩL ∩ Z) := by
    rw [hkZ, setIntegral_indicator hZm]
    exact norm_setIntegral_le_of_norm_le_const (by rwa [Set.inter_comm]) hbound
  calc ‖∫ z in ΩL, k z ∂νZL‖ ≤ max Mξ 0 * (N * max B 0) * νZL.real (ΩL ∩ Z) := hint
    _ = max Mξ 0 * max B 0 * νZL.real (ΩL ∩ Z) * N := by ring

end Fold

end KernelCountReduction

end KernelCountReduction

section SiegelRowBounds

set_option autoImplicit false

open AutomorphicForm.WindowedSiegel

namespace SiegelRowBounds

variable {K : Type*} [NormedField K]

private theorem localHeight_mul_rowNormSq (g : GL (Fin 2) K) :
    localHeight g * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
  have hρ : rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≠ 0 := (rowNormSq_pos g).ne'
  unfold localHeight
  field_simp

private theorem rowNormSq_le_div (g : GL (Fin 2) K) {c d₂ : ℝ} (hc : 0 < c) (hlh : c ≤ localHeight g)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ d₂) :
    rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / localHeight g := by
  rw [le_div_iff₀ (hc.trans_le hlh), mul_comm, localHeight_mul_rowNormSq]
  exact hdet

private theorem rowNormSq_le_div_floor (g : GL (Fin 2) K) {c d₂ : ℝ} (hc : 0 < c) (hlh : c ≤ localHeight g)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ d₂) :
    rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / c := by
  rw [le_div_iff₀ hc]
  calc rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * c
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * localHeight g :=
        mul_le_mul_of_nonneg_left hlh (rowNormSq_pos g).le
    _ = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by rw [mul_comm, localHeight_mul_rowNormSq]
    _ ≤ d₂ := hdet

private theorem norm_apply_one_le (g : GL (Fin 2) K) {c d₂ : ℝ} (hc : 0 < c) (hlh : c ≤ localHeight g)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ d₂) (j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) K) 1 j‖ ≤ Real.sqrt d₂ * (Real.sqrt (localHeight g))⁻¹ := by
  have hd₂ : 0 ≤ d₂ := (norm_nonneg _).trans hdet
  have hh : 0 < localHeight g := hc.trans_le hlh
  have hsq : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 j‖ ^ 2 ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    fin_cases j
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)
  rw [← div_eq_mul_inv, ← Real.sqrt_div hd₂]
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (hsq.trans (rowNormSq_le_div g hc hlh hdet))

private theorem norm_apply_zero_le (g : GL (Fin 2) K) {c u d₂ : ℝ} (hc : 0 < c) (hlh : c ≤ localHeight g)
    (hxw : xWindowSq g ≤ u ^ 2) (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ d₂) (j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) K) 0 j‖ ≤ Real.sqrt d₂ * Real.sqrt (u ^ 2 / c + localHeight g) := by
  have hd₂ : 0 ≤ d₂ := (norm_nonneg _).trans hdet
  have hh : 0 < localHeight g := hc.trans_le hlh
  have hρ : 0 < rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := rowNormSq_pos g
  have hsq : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 j‖ ^ 2 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    fin_cases j
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)

  have htop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      = (xWindowSq g + localHeight g ^ 2) * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    have hρ' : rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≠ 0 := hρ.ne'
    unfold xWindowSq
    rw [sub_add_cancel]
    field_simp
  have hbound : topNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ * (u ^ 2 / c + localHeight g) := by
    rw [htop, add_mul]
    have h1 : xWindowSq g * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ u ^ 2 * (d₂ / c) :=
      mul_le_mul hxw (rowNormSq_le_div_floor g hc hlh hdet) hρ.le (sq_nonneg u)
    have h2 : localHeight g ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ localHeight g * d₂ := by
      rw [pow_two, mul_assoc, localHeight_mul_rowNormSq]
      exact mul_le_mul_of_nonneg_left hdet hh.le
    calc xWindowSq g * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
          + localHeight g ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
        ≤ u ^ 2 * (d₂ / c) + localHeight g * d₂ := add_le_add h1 h2
      _ = d₂ * (u ^ 2 / c + localHeight g) := by ring
  rw [← Real.sqrt_mul hd₂]
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (hsq.trans hbound)

end SiegelRowBounds

end SiegelRowBounds

section HeightGaloisInvariance

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open scoped NumberField.PlaceTransport

namespace HeightGaloisInvariance

open AutomorphicForm.WindowedSiegel NumberField.AdelicHeight

section Local

variable {K₁ K₂ : Type*} [NormedField K₁] [NormedField K₂]

private theorem det_map_eq (f : K₁ →+* K₂) (M : Matrix (Fin 2) (Fin 2) K₁) : (M.map f).det = f M.det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

private theorem localHeight_eq_of_entries_eq (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (M : GL (Fin 2) K₁)
    (N : GL (Fin 2) K₂)
    (hN : ∀ i j, (N : Matrix (Fin 2) (Fin 2) K₂) i j = f ((M : Matrix (Fin 2) (Fin 2) K₁) i j)) :
    localHeight N = localHeight M := by
  have hmat : (N : Matrix (Fin 2) (Fin 2) K₂) = (M : Matrix (Fin 2) (Fin 2) K₁).map f := Matrix.ext hN
  unfold localHeight rowNormSq
  rw [hmat, det_map_eq, hf, Matrix.map_apply, Matrix.map_apply, hf, hf]

private theorem finLocalHeight_eq_of_entries_eq (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (M : GL (Fin 2) K₁)
    (N : GL (Fin 2) K₂)
    (hN : ∀ i j, (N : Matrix (Fin 2) (Fin 2) K₂) i j = f ((M : Matrix (Fin 2) (Fin 2) K₁) i j)) :
    finLocalHeight N = finLocalHeight M := by
  have hmat : (N : Matrix (Fin 2) (Fin 2) K₂) = (M : Matrix (Fin 2) (Fin 2) K₁).map f := Matrix.ext hN
  unfold finLocalHeight rowMaxNorm
  rw [hmat, det_map_eq, hf, Matrix.map_apply, Matrix.map_apply, hf, hf]

end Local

section Transport

variable {K L : Type} [Field K] [Field L] [Algebra K L]

private theorem norm_infinitePlaceTransport (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w')
    (x : w.Completion) : ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  refine NumberField.InfinitePlace.Completion.induction_on _ x ?_ ?_
  · exact isClosed_eq (NumberField.InfinitePlaceTransport.continuous_transport σ h).norm continuous_norm
  · intro a
    rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe]
    exact NumberField.InfinitePlaceTransport.apply_apply_of_smul_eq h _

variable [NumberField L]

private theorem absNorm_smul_asIdeal (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • v).asIdeal = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv v.asIdeal (σ • v).asIdeal
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)
    (NumberField.PlaceTransport.smul_asIdeal_eq_map σ v)).toEquiv).symm

private theorem norm_placeTransport (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) :
    ‖NumberField.PlaceTransport.transport σ (rfl : σ • v = σ • v) x‖ = ‖x‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def,
    NumberField.PlaceTransport.valued_transport]
  simp only [absNorm_smul_asIdeal σ v]

end Transport

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
private theorem sigmaAdelicAct_entry (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((AutomorphicForm.sigmaAdelicAct K L D σ g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      = D.act σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  rfl

private theorem adelicHeight_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ g) = adelicHeight L g := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  set gσ := AutomorphicForm.sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ g
    with hgσ
  have harchc : ∀ (w : InfinitePlace L) (i j : Fin 2),
      ((archComponent L (σ • w) (glArch (𝓞 L) L gσ) : GL (Fin 2) (σ • w).Completion) :
          Matrix (Fin 2) (Fin 2) (σ • w).Completion) i j
        = (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • w = σ • w)).toRingHom
            (((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
    intro w i j
    rw [archComponent_apply, glArch_apply, archComponent_apply, glArch_apply, hgσ, sigmaAdelicAct_entry,
      M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ (w := w) rfl]
    rfl
  have hfinc : ∀ (v : HeightOneSpectrum (𝓞 L)) (i j : Fin 2),
      ((finComponent (𝓞 L) L (σ • v) (glFin (𝓞 L) L gσ) : GL (Fin 2) ((σ • v).adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) ((σ • v).adicCompletion L)) i j
        = (NumberField.PlaceTransport.transport σ (rfl : σ • v = σ • v)).toRingHom
            (((finComponent (𝓞 L) L v (glFin (𝓞 L) L g) : GL (Fin 2) (v.adicCompletion L)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j) := by
    intro v i j
    rw [finComponent_apply, glFin_apply, finComponent_apply, glFin_apply, hgσ, sigmaAdelicAct_entry,
      M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (w := v) rfl]
    rfl
  have hmult : ∀ w : InfinitePlace L, (σ • w).mult = w.mult := by
    intro w
    by_cases h : w.IsReal
    · simp only [InfinitePlace.mult]
      rw [if_pos (InfinitePlace.isReal_smul_iff.mpr h), if_pos h]
    · simp only [InfinitePlace.mult]
      rw [if_neg (mt InfinitePlace.isReal_smul_iff.mp h), if_neg h]
  let eArch : InfinitePlace L ≃ InfinitePlace L :=
    ⟨fun w => σ • w, fun w => σ⁻¹ • w, inv_smul_smul σ, smul_inv_smul σ⟩
  let eFin : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) :=
    ⟨fun v => σ • v, fun v => σ⁻¹ • v, inv_smul_smul σ, smul_inv_smul σ⟩
  have harch : archHeight L (glArch (𝓞 L) L gσ) = archHeight L (glArch (𝓞 L) L g) := by
    unfold archHeight
    refine (Fintype.prod_equiv eArch _ _ fun w => ?_).symm
    dsimp only [eArch, Equiv.coe_fn_mk]
    rw [hmult w, localHeight_eq_of_entries_eq _ (norm_infinitePlaceTransport σ rfl) _ _ (harchc w)]
  have hfin : finHeight L (glFin (𝓞 L) L gσ) = finHeight L (glFin (𝓞 L) L g) := by
    unfold finHeight
    refine (finprod_eq_of_bijective eFin eFin.bijective fun v => ?_).symm
    dsimp only [eFin, Equiv.coe_fn_mk]
    rw [finLocalHeight_eq_of_entries_eq _ (norm_placeTransport σ v) _ _ (hfinc v)]
  unfold adelicHeight
  rw [harch, hfin]

end Adelic

end HeightGaloisInvariance

end HeightGaloisInvariance

section AdelicExtraction

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
open scoped Pointwise NumberField.PlaceTransport

namespace AdelicExtraction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem archComponent_glArch_sigmaAdelicAct (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : InfinitePlace L) :
    ((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
        GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion)
      = ((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).map
            (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • w = σ • w)).toRingHom := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  ext i j
  rw [Matrix.map_apply, archComponent_apply, glArch_apply, archComponent_apply, glArch_apply,
    HeightGaloisInvariance.sigmaAdelicAct_entry,
    M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ (w := w) rfl]
  rfl

private theorem finComponent_glFin_sigmaAdelicAct (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 L)) (i j : Fin 2) :
    ((finComponent (𝓞 L) L (σ • v) (glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
        GL (Fin 2) ((σ • v).adicCompletion L)) : Matrix (Fin 2) (Fin 2) ((σ • v).adicCompletion L)) i j
      = NumberField.PlaceTransport.transport σ (rfl : σ • v = σ • v)
          (((finComponent (𝓞 L) L v (glFin (𝓞 L) L g) : GL (Fin 2) (v.adicCompletion L)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j) := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [finComponent_apply, glFin_apply, finComponent_apply, glFin_apply,
    HeightGaloisInvariance.sigmaAdelicAct_entry,
    M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (w := v) rfl]

private theorem norm_archComponent_sigmaAdelicAct_apply (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : InfinitePlace L)
    (i j : Fin 2) :
    ‖((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
        GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion) i j‖
      = ‖((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ := by
  rw [archComponent_glArch_sigmaAdelicAct, Matrix.map_apply]
  exact HeightGaloisInvariance.norm_infinitePlaceTransport σ rfl _

private theorem norm_det_archComponent_sigmaAdelicAct (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : InfinitePlace L) :
    ‖(((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
        GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion)).det‖
      = ‖(((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)).det‖ := by
  rw [archComponent_glArch_sigmaAdelicAct, HeightGaloisInvariance.det_map_eq]
  exact HeightGaloisInvariance.norm_infinitePlaceTransport σ rfl _

private theorem glFin_sigmaAdelicAct_apply_mem_integralFiniteAdeles (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hg : ∀ i j, ((glFin (𝓞 L) L g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) (i j : Fin 2) :
    ((glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  intro v'
  obtain ⟨v, rfl⟩ : ∃ v, σ • v = v' := ⟨σ⁻¹ • v', smul_inv_smul σ v'⟩
  have h := finComponent_glFin_sigmaAdelicAct K L D σ g v i j
  rw [finComponent_apply, finComponent_apply] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h, NumberField.PlaceTransport.valued_transport]
  exact valued_apply_le_one (hg i j) v

private theorem glFin_sigmaAdelicAct_mem_finiteIntegralGL2 (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hg : glFin (𝓞 L) L g ∈ finiteIntegralGL2 (𝓞 L) L) :
    glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) ∈ finiteIntegralGL2 (𝓞 L) L := by
  rw [mem_finiteIntegralGL2_iff] at hg ⊢
  refine ⟨glFin_sigmaAdelicAct_apply_mem_integralFiniteAdeles K L D σ g hg.1, fun i j => ?_⟩
  have h2 : ∀ i j, ((glFin (𝓞 L) L g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
    intro i j
    rw [map_inv]
    exact hg.2 i j
  have h3 := glFin_sigmaAdelicAct_apply_mem_integralFiniteAdeles K L D σ g⁻¹ h2 i j
  rwa [map_inv, map_inv] at h3

private theorem norm_archComponent_globalPoints_apply (δ : GL (Fin 2) L) (w : InfinitePlace L) (i j : Fin 2) :
    ‖((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L δ)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j‖ = w ((δ : Matrix (Fin 2) (Fin 2) L) i j) := by
  rw [archComponent_apply, glArch_apply]
  change ‖((algebraMap L (AdeleRing (𝓞 L) L) ((δ : Matrix (Fin 2) (Fin 2) L) i j)).1 w)‖ = _
  rw [AdeleRing.algebraMap_fst_apply]
  exact NumberField.InfinitePlace.Completion.norm_coe w _

private theorem glFin_globalPoints_apply (δ : GL (Fin 2) L) (i j : Fin 2) :
    ((glFin (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L δ) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j
      = algebraMap L (FiniteAdeleRing (𝓞 L) L) ((δ : Matrix (Fin 2) (Fin 2) L) i j) := by
  rw [glFin_apply]
  rfl

private theorem exists_eq_mul_of_mem_integralFiniteAdeles (s : 𝓞 L) (x : L)
    (h : algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * algebraMap L (FiniteAdeleRing (𝓞 L) L) x
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ∃ y : 𝓞 L, (y : L) = (s : L) * x := by
  have hval : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((s : L) * x) ≤ 1 := by
    intro v

    have hv : Valued.v ((algebraMap L (FiniteAdeleRing (𝓞 L) L) (s : L) *
        algebraMap L (FiniteAdeleRing (𝓞 L) L) x) v) ≤ 1 := valued_apply_le_one h v
    rwa [← map_mul, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      at hv
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp
    (HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) (K := L) ((s : L) * x) hval)
  exact ⟨y, hy⟩

private theorem exists_forall_norm_archComponent_le {Ξ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hΞ : IsCompact Ξ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ Ξ, ∀ (w : InfinitePlace L) (i j : Fin 2),
      ‖((archComponent L w (glArch (𝓞 L) L ξ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ M := by
  classical

  let e : InfinitePlace L × Fin 2 × Fin 2 → AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ := fun p ξ =>
    ‖((archComponent L p.1 (glArch (𝓞 L) L ξ) : GL (Fin 2) p.1.Completion) :
        Matrix (Fin 2) (Fin 2) p.1.Completion) p.2.1 p.2.2‖
  have he : ∀ p, Continuous (e p) := by
    intro p
    refine Continuous.norm ?_
    exact (Units.continuous_val.comp ((continuous_archComponent L p.1).comp (continuous_glArch (𝓞 L) L))).matrix_elem
      p.2.1 p.2.2
  have he0 : ∀ p ξ, 0 ≤ e p ξ := fun p ξ => norm_nonneg _
  have hsum : Continuous fun ξ => ∑ p, e p ξ := continuous_finsetSum _ fun p _ => he p
  obtain ⟨M, hM⟩ := hΞ.exists_bound_of_continuousOn hsum.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun ξ hξ w i j => ?_⟩
  calc e (w, i, j) ξ ≤ ∑ p, e p ξ :=
        Finset.single_le_sum (f := fun p => e p ξ) (fun p _ => he0 p ξ) (Finset.mem_univ (w, i, j))
    _ ≤ ‖∑ p, e p ξ‖ := le_abs_self _
    _ ≤ M := hM ξ hξ
    _ ≤ max M 0 := le_max_left _ _

private theorem exists_ne_zero_forall_algebraMap_mul_glFin_apply_mem {Ξ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)}
    (hΞ : IsCompact Ξ) :
    ∃ s : 𝓞 L, s ≠ 0 ∧ ∀ ξ ∈ Ξ, ∀ i j : Fin 2,
      algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s *
          ((glFin (𝓞 L) L ξ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j
        ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  have hcont : ∀ i j : Fin 2, Continuous fun ξ : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ((glFin (𝓞 L) L ξ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j :=
    fun i j => (Units.continuous_val.comp (continuous_glFin (𝓞 L) L)).matrix_elem i j
  have hC : IsCompact (⋃ (i : Fin 2) (j : Fin 2), (fun ξ : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ((glFin (𝓞 L) L ξ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) '' Ξ) :=
    isCompact_iUnion fun i => isCompact_iUnion fun j => hΞ.image (hcont i j)
  obtain ⟨s, hs, hmem⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
      (𝓞 L) L hC
  refine ⟨s, hs, fun ξ hξ i j => ?_⟩
  intro v
  exact hmem _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨ξ, hξ, rfl⟩⟩⟩) v

private theorem place_apply_le_of_eq_mul_mul_inv {A Dd m M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ Dd) (hm : 0 < m) (hM : 0 ≤ M)
    (t ξ : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (htop : ∀ (w : InfinitePlace L) (j : Fin 2), ‖((archComponent L w (glArch (𝓞 L) L t) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖ ≤ A)
    (hbot : ∀ (w : InfinitePlace L) (j : Fin 2), ‖((archComponent L w (glArch (𝓞 L) L t) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ ≤ Dd)
    (hdet : ∀ w : InfinitePlace L, m ≤ ‖(((archComponent L w (glArch (𝓞 L) L t) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion)).det‖)
    (hξ : ∀ (w : InfinitePlace L) (i j : Fin 2), ‖((archComponent L w (glArch (𝓞 L) L ξ) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ M)
    (δ : GL (Fin 2) L)
    (hδ : AutomorphicForm.globalPoints (𝓞 L) L δ = t * ξ * (AutomorphicForm.sigmaAdelicAct K L D σ t)⁻¹)
    (w' : InfinitePlace L) :
    w' ((δ : Matrix (Fin 2) (Fin 2) L) 0 0) ≤ 4 * M * (A * Dd) / m ∧
      w' ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) ≤ 4 * M * (A * A) / m ∧
      w' ((δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≤ 4 * M * (A * Dd) / m := by
  obtain ⟨w, rfl⟩ : ∃ w, σ • w = w' := ⟨σ⁻¹ • w', smul_inv_smul σ w'⟩

  have hcomp : archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L δ))
      = archComponent L (σ • w) (glArch (𝓞 L) L t) * archComponent L (σ • w) (glArch (𝓞 L) L ξ) *
          (archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t)))⁻¹ := by
    simp only [hδ, map_mul, map_inv]
  have hy'top : ∀ j : Fin 2, ‖((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t)) :
      GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion) 0 j‖ ≤ A := fun j => by
    rw [norm_archComponent_sigmaAdelicAct_apply]; exact htop w j
  have hy'bot : ∀ j : Fin 2, ‖((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t)) :
      GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion) 1 j‖ ≤ Dd := fun j => by
    rw [norm_archComponent_sigmaAdelicAct_apply]; exact hbot w j
  have hy'det : m ≤ ‖(((archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t)) :
      GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion)).det‖ := by
    rw [norm_det_archComponent_sigmaAdelicAct]; exact hdet w
  obtain ⟨h00, h01, h11⟩ := BalancedExtraction.norm_mul_mul_inv_apply_le
    (archComponent L (σ • w) (glArch (𝓞 L) L t)) (archComponent L (σ • w) (glArch (𝓞 L) L ξ))
    (archComponent L (σ • w) (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t)))
    hA hD hm hM (htop (σ • w)) (hbot (σ • w)) (hξ (σ • w)) hy'det hy'top hy'bot
  rw [← hcomp] at h00 h01 h11
  rw [norm_archComponent_globalPoints_apply] at h00 h01 h11
  exact ⟨h00, h01, h11⟩

private theorem exists_eq_mul_apply_of_eq_mul_mul_inv (s : 𝓞 L) (t ξ : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (ht : glFin (𝓞 L) L t ∈ finiteIntegralGL2 (𝓞 L) L)
    (hξ : ∀ i j : Fin 2, algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s *
      ((glFin (𝓞 L) L ξ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L)
    (δ : GL (Fin 2) L)
    (hδ : AutomorphicForm.globalPoints (𝓞 L) L δ = t * ξ * (AutomorphicForm.sigmaAdelicAct K L D σ t)⁻¹)
    (i j : Fin 2) : ∃ y : 𝓞 L, (y : L) = (s : L) * (δ : Matrix (Fin 2) (Fin 2) L) i j := by
  set a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
    ((glFin (𝓞 L) L t : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    with ha
  set b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
    ((glFin (𝓞 L) L ξ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    with hb
  set c : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
    (((glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ t))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) with hc
  have hamem : ∀ i j, a i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := (mem_finiteIntegralGL2_iff.mp ht).1
  have hcmem : ∀ i j, c i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L :=
    (mem_finiteIntegralGL2_iff.mp (glFin_sigmaAdelicAct_mem_finiteIntegralGL2 K L D σ t ht)).2
  have hbmem : ∀ i j,
      algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * b i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L := hξ

  have hentry : algebraMap L (FiniteAdeleRing (𝓞 L) L) ((δ : Matrix (Fin 2) (Fin 2) L) i j) = (a * b * c) i j := by
    rw [ha, hb, hc, ← glFin_globalPoints_apply, hδ, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  refine exists_eq_mul_of_mem_integralFiniteAdeles L s _ ?_
  rw [hentry, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]

  have key : ∀ (x y z : FiniteAdeleRing (𝓞 L) L), x ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L →
      algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L →
      z ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L →
      algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (x * y * z) ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
    intro x y z hx hy hz
    have : algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (x * y * z)
        = x * (algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * y) * z := by ring
    rw [this]
    exact mul_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles hx hy) hz
  have hsplit : algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s *
      ((a i 0 * b 0 0 + a i 1 * b 1 0) * c 0 j + (a i 0 * b 0 1 + a i 1 * b 1 1) * c 1 j)
      = algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (a i 0 * b 0 0 * c 0 j)
        + algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (a i 1 * b 1 0 * c 0 j)
        + (algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (a i 0 * b 0 1 * c 1 j)
        + algebraMap (𝓞 L) (FiniteAdeleRing (𝓞 L) L) s * (a i 1 * b 1 1 * c 1 j)) := by ring
  rw [hsplit]
  exact add_mem_integralFiniteAdeles
    (add_mem_integralFiniteAdeles (key _ _ _ (hamem i 0) (hbmem 0 0) (hcmem 0 j))
      (key _ _ _ (hamem i 1) (hbmem 1 0) (hcmem 0 j)))
    (add_mem_integralFiniteAdeles (key _ _ _ (hamem i 0) (hbmem 0 1) (hcmem 1 j))
      (key _ _ _ (hamem i 1) (hbmem 1 1) (hcmem 1 j)))

end AdelicExtraction

end AdelicExtraction

section UnitBalancing

set_option autoImplicit false

open Module NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace UnitBalancing

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

private theorem exists_forall_exists_norm_logEmbedding_sub_le :
    ∃ C : ℝ, ∀ v : logSpace F, ∃ ε : (𝓞 F)ˣ, ‖logEmbedding F (Additive.ofMul ε) - v‖ ≤ C := by
  let b := Module.Free.chooseBasis ℤ (unitLattice F)
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ))
  refine ⟨C, fun v => ?_⟩
  obtain ⟨g, hg, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) v
  have hgmem : (g : logSpace F) ∈ unitLattice F := (b.ofZLatticeBasis_span ℝ).le g.2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hgmem
  have hx' : logEmbedding F x = (g : logSpace F) := hx
  refine ⟨(Additive.toMul x)⁻¹, ?_⟩
  have h1 : logEmbedding F (Additive.ofMul (Additive.toMul x)⁻¹) = -(g : logSpace F) := by
    rw [ofMul_inv, map_neg, ofMul_toMul, hx']
  have h2 : (g : logSpace F) + v ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) := hg
  calc ‖logEmbedding F (Additive.ofMul (Additive.toMul x)⁻¹) - v‖
      = ‖(g : logSpace F) + v‖ := by rw [h1, ← norm_neg]; congr 1; abel
    _ ≤ C := hC _ h2

private noncomputable def meanLog (a : InfinitePlace F → ℝ) : ℝ :=
  (∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (a w)) / (finrank ℚ F : ℝ)

private theorem finrank_mul_meanLog (a : InfinitePlace F → ℝ) :
    (finrank ℚ F : ℝ) * meanLog F a = ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (a w) := by
  have hn : (finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := F)).ne'
  rw [meanLog]
  field_simp

private theorem exp_meanLog_pow (a : InfinitePlace F → ℝ) (ha : ∀ w, 0 < a w) :
    Real.exp (meanLog F a) ^ finrank ℚ F = ∏ w : InfinitePlace F, a w ^ mult w := by
  rw [← Real.exp_nat_mul, finrank_mul_meanLog, Real.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Real.exp_nat_mul, Real.exp_log (ha w)]

private theorem exists_forall_exists_unit_abs_log_mul_sub_meanLog_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : InfinitePlace F → ℝ, (∀ w, 0 < a w) → ∃ ε : (𝓞 F)ˣ,
      ∀ w : InfinitePlace F, |Real.log (w (ε : F) * a w) - meanLog F a| ≤ C := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_forall_exists_norm_logEmbedding_sub_le F
  set C₁ : ℝ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  refine ⟨(Fintype.card (InfinitePlace F) : ℝ) * C₁, by positivity, fun a ha => ?_⟩
  set m : ℝ := meanLog F a with hm
  obtain ⟨ε, hε⟩ := hC₀ (fun w : {w : InfinitePlace F // w ≠ w₀} => (mult w.1 : ℝ) * (m - Real.log (a w.1)))
  refine ⟨ε, ?_⟩

  set d : InfinitePlace F → ℝ := fun w => Real.log (w (ε : F)) + Real.log (a w) - m with hd

  have hdev : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |(mult w.1 : ℝ) * d w.1| ≤ C₁ := by
    intro w
    have h1 := norm_le_pi_norm
      (logEmbedding F (Additive.ofMul ε) -
        fun w : {w : InfinitePlace F // w ≠ w₀} => (mult w.1 : ℝ) * (m - Real.log (a w.1))) w
    rw [Pi.sub_apply, logEmbedding_component, Real.norm_eq_abs] at h1
    refine le_trans (le_of_eq ?_) (h1.trans (hε.trans (le_max_left _ _)))
    congr 1
    simp only [hd]
    ring

  have hsum : ∑ w : InfinitePlace F, (mult w : ℝ) * d w = 0 := by
    have hmean : ∑ w : InfinitePlace F, (mult w : ℝ) * m = ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (a w) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, sum_mult_eq, hm, finrank_mul_meanLog]
    have hunit := sum_mult_mul_log ε
    simp only [hd, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hunit, hmean]
    ring

  have hall : ∀ w : InfinitePlace F, |(mult w : ℝ) * d w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * C₁ := by
    intro w
    by_cases hw : w = w₀
    · have hsplit : ∑ u : InfinitePlace F, (mult u : ℝ) * d u =
          (mult (w₀ : InfinitePlace F) : ℝ) * d w₀ +
            ∑ u : {u : InfinitePlace F // u ≠ w₀}, (mult u.1 : ℝ) * d u.1 :=
        Fintype.sum_eq_add_sum_subtype_ne _ _
      rw [hsum] at hsplit
      have h0 : (mult (w₀ : InfinitePlace F) : ℝ) * d w₀ =
          -∑ u : {u : InfinitePlace F // u ≠ w₀}, (mult u.1 : ℝ) * d u.1 := by
        linarith
      rw [hw, h0, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ C₁ fun u _ => hdev u).trans ?_
      rw [Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) hC₁0
    · refine (hdev ⟨w, hw⟩).trans ?_
      have h1 : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
      exact le_mul_of_one_le_left hC₁0 h1
  intro w
  have hpos : 0 < w (ε : F) := pos_at_place ε w
  have hw1 : Real.log (w (ε : F) * a w) - m = d w := by
    rw [Real.log_mul hpos.ne' (ha w).ne']
  rw [hw1]
  have hmult : (1 : ℝ) ≤ mult w := one_le_mult
  have h2 := hall w
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < mult w)] at h2
  have h3 : |d w| ≤ (mult w : ℝ) * |d w| := le_mul_of_one_le_left (abs_nonneg _) hmult
  exact h3.trans h2

private theorem exists_forall_exists_unit_mul_le_and_le_mul :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : InfinitePlace F → ℝ, (∀ w, 0 < a w) → ∃ ε : (𝓞 F)ˣ,
      ∀ w : InfinitePlace F,
        w (ε : F) * a w ≤ C * Real.exp (meanLog F a) ∧ Real.exp (meanLog F a) ≤ C * (w (ε : F) * a w) := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_exists_unit_abs_log_mul_sub_meanLog_le F
  refine ⟨Real.exp C, by simpa using Real.exp_le_exp.mpr hC0, fun a ha => ?_⟩
  obtain ⟨ε, hε⟩ := hC a ha
  refine ⟨ε, fun w => ?_⟩
  have hy : 0 < w (ε : F) * a w := mul_pos (pos_at_place ε w) (ha w)
  obtain ⟨h1, h2⟩ := abs_le.mp (hε w)
  constructor
  · calc w (ε : F) * a w = Real.exp (Real.log (w (ε : F) * a w)) := (Real.exp_log hy).symm
      _ ≤ Real.exp (C + meanLog F a) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp C * Real.exp (meanLog F a) := Real.exp_add _ _
  · calc Real.exp (meanLog F a) ≤ Real.exp (C + Real.log (w (ε : F) * a w)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp C * (w (ε : F) * a w) := by rw [Real.exp_add, Real.exp_log hy]

end UnitBalancing

end UnitBalancing

section UnitBalancing

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain

namespace UnitBalancing

section Diagonal

variable {L : Type*} [Field L]

private def unitDiag (a b : Lˣ) : GL (Fin 2) L where
  val := Matrix.diagonal ![(a : L), (b : L)]
  inv := Matrix.diagonal ![((a⁻¹ : Lˣ) : L), ((b⁻¹ : Lˣ) : L)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

private theorem coe_unitDiag (a b : Lˣ) :
    ((unitDiag a b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = Matrix.diagonal ![(a : L), (b : L)] := rfl

private theorem coe_unitDiag_inv (a b : Lˣ) :
    (((unitDiag a b)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = Matrix.diagonal ![((a⁻¹ : Lˣ) : L), ((b⁻¹ : Lˣ) : L)] := rfl

private theorem coe_inv_mul_mul_map_apply_one_zero (σ : L →+* L) (a b : Lˣ) (δ : GL (Fin 2) L) :
    (((unitDiag a b)⁻¹ * δ * Matrix.GeneralLinearGroup.map σ (unitDiag a b) : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0
      = ((b⁻¹ : Lˣ) : L) * ((δ : Matrix (Fin 2) (Fin 2) L) 1 0 * σ a) := by
  rw [Units.val_mul, Units.val_mul, coe_unitDiag_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, coe_unitDiag]
  simp [Matrix.diagonal, mul_assoc]

private theorem coe_inv_mul_mul_map_apply_one_zero_eq_zero_iff (σ : L →+* L) (a b : Lˣ) (δ : GL (Fin 2) L) :
    (((unitDiag a b)⁻¹ * δ * Matrix.GeneralLinearGroup.map σ (unitDiag a b) : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ↔ (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [coe_inv_mul_mul_map_apply_one_zero, mul_eq_zero, mul_eq_zero]
  have ha : σ a ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  have hb : ((b⁻¹ : Lˣ) : L) ≠ 0 := Units.ne_zero _
  tauto

end Diagonal

section Classes

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem mem_setOf_borel_central_iff {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (a b : Lˣ) (δ : GL (Fin 2) L) :
    δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) F,
        γ ∈ AutomorphicForm.centralCell F ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
      ↔ (unitDiag a b)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (unitDiag a b)
        ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) F,
          γ ∈ AutomorphicForm.centralCell F ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  have hcls : LT.TwistedNorm.SigmaConjClasses.mk σ
      ((unitDiag a b)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (unitDiag a b))
        = LT.TwistedNorm.SigmaConjClasses.mk σ δ :=
    (LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨unitDiag a b, rfl⟩).symm
  simp only [Set.mem_setOf_eq, hcls, coe_inv_mul_mul_map_apply_one_zero_eq_zero_iff]

end Classes

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

omit [NumberField K] in
private theorem sigmaAdelicAct_globalPoints' (β : GL (Fin 2) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L β)
      = AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) β) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ β

omit [NumberField K] in

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * g = g * AutomorphicForm.centralScalar (𝓞 L) L z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun _ => Commute.all _ _) _).eq

omit [NumberField K] in

private theorem inv_mul_mul_sigmaAdelicAct_eq (β δ : GL (Fin 2) L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    (AutomorphicForm.globalPoints (𝓞 L) L β * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z *
          (AutomorphicForm.globalPoints (𝓞 L) L β * x))
      = x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L
          (β⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) β) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) := by
  have hc : AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L β * x)
      = AutomorphicForm.globalPoints (𝓞 L) L β * (AutomorphicForm.centralScalar (𝓞 L) L z * x) := by
    rw [← mul_assoc, centralScalar_mul_comm, mul_assoc]
  rw [hc]
  simp only [mul_inv_rev, map_mul, map_inv, sigmaAdelicAct_globalPoints', mul_assoc]

omit [NumberField K] in

private theorem ncard_inter_support_globalPoints_mul_eq (β : GL (Fin 2) L) (T : Set (GL (Fin 2) L))
    (hT : ∀ δ, δ ∈ T ↔ β⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) β ∈ T)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    (T ∩ Function.support fun δ => φ ((AutomorphicForm.globalPoints (𝓞 L) L β * x)⁻¹ *
        AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z *
          (AutomorphicForm.globalPoints (𝓞 L) L β * x)))).ncard
      = (T ∩ Function.support fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))).ncard := by
  set e : Equiv.Perm (GL (Fin 2) L) :=
    (Equiv.mulLeft β⁻¹).trans (Equiv.mulRight (Matrix.GeneralLinearGroup.map (σ : L →+* L) β)) with he
  have hset : (T ∩ Function.support fun δ => φ ((AutomorphicForm.globalPoints (𝓞 L) L β * x)⁻¹ *
      AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z *
        (AutomorphicForm.globalPoints (𝓞 L) L β * x))))
      = e ⁻¹' (T ∩ Function.support fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) := by
    ext δ
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_preimage, he, Equiv.trans_apply,
      Equiv.coe_mulLeft, Equiv.coe_mulRight]
    rw [inv_mul_mul_sigmaAdelicAct_eq, hT δ]
  rw [hset]
  exact Set.ncard_preimage_of_injective_subset_range e.injective
    (by rw [e.surjective.range_eq]; exact Set.subset_univ _)

omit [NumberField K] in
private theorem archComponent_globalPoints_apply (δ : GL (Fin 2) L) (w : InfinitePlace L) (i j : Fin 2) :
    ((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L δ)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = (((δ : Matrix (Fin 2) (Fin 2) L) i j : L) : w.Completion) := by
  rw [archComponent_apply, glArch_apply]
  rfl

omit [NumberField K] in

private theorem coe_archComponent_globalPoints_unitDiag_mul (a b : Lˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : InfinitePlace L) :
    ((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L (unitDiag a b) * x)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = Matrix.diagonal ![((a : L) : w.Completion), ((b : L) : w.Completion)] *
          ((archComponent L w (glArch (𝓞 L) L x) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) := by
  rw [map_mul, map_mul, Units.val_mul]
  congr 1
  ext i j
  rw [archComponent_globalPoints_apply, coe_unitDiag]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] [NumberField L] in

private theorem norm_coe_completion (w : InfinitePlace L) (y : L) : ‖((y : L) : w.Completion)‖ = w y :=
  NumberField.InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 y)

omit [NumberField K] in
private theorem norm_archComponent_globalPoints_unitDiag_mul_apply_zero (a b : Lˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : InfinitePlace L) (j : Fin 2) :
    ‖((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L (unitDiag a b) * x)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖
      = ‖((a : L) : w.Completion)‖ * ‖((archComponent L w (glArch (𝓞 L) L x) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖ := by
  rw [coe_archComponent_globalPoints_unitDiag_mul, Matrix.diagonal_mul, Matrix.cons_val_zero, norm_mul]

omit [NumberField K] in
private theorem norm_archComponent_globalPoints_unitDiag_mul_apply_one (a b : Lˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : InfinitePlace L) (j : Fin 2) :
    ‖((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L (unitDiag a b) * x)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖
      = ‖((b : L) : w.Completion)‖ * ‖((archComponent L w (glArch (𝓞 L) L x) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ := by
  rw [coe_archComponent_globalPoints_unitDiag_mul, Matrix.diagonal_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
    norm_mul]

omit [NumberField K] in
private theorem norm_det_archComponent_globalPoints_unitDiag_mul (a b : Lˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : InfinitePlace L) :
    ‖(((archComponent L w (glArch (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L (unitDiag a b) * x)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)).det‖
      = ‖((a : L) : w.Completion)‖ * ‖((b : L) : w.Completion)‖ *
          ‖(((archComponent L w (glArch (𝓞 L) L x) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion)).det‖ := by
  rw [coe_archComponent_globalPoints_unitDiag_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul, norm_mul]

omit [NumberField K] in

private theorem glFin_globalPoints_mem_finiteIntegralGL2 (β : GL (Fin 2) L)
    (hβ : ∀ i j, ∃ r : 𝓞 L, (r : L) = (β : Matrix (Fin 2) (Fin 2) L) i j)
    (hβ' : ∀ i j, ∃ r : 𝓞 L, (r : L) = ((β⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j) :
    glFin (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L β) ∈ finiteIntegralGL2 (𝓞 L) L := by

  have key : ∀ (γ : GL (Fin 2) L) (i j : Fin 2), (∃ r : 𝓞 L, (r : L) = (γ : Matrix (Fin 2) (Fin 2) L) i j) →
      ((glFin (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L γ) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
    intro γ i j hr v
    obtain ⟨r, hr⟩ := hr
    rw [glFin_apply]
    change (algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) i j)).2 v ∈ _
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => key β i j (hβ i j), fun i j => ?_⟩
  have h := key β⁻¹ i j (hβ' i j)
  rwa [map_inv, map_inv] at h

omit [NumberField K] in

private theorem glFin_globalPoints_unitDiag_mem_finiteIntegralGL2 (a b : Lˣ)
    (ha : ∃ r : 𝓞 L, (r : L) = a) (ha' : ∃ r : 𝓞 L, (r : L) = ((a⁻¹ : Lˣ) : L))
    (hb : ∃ r : 𝓞 L, (r : L) = b) (hb' : ∃ r : 𝓞 L, (r : L) = ((b⁻¹ : Lˣ) : L)) :
    glFin (𝓞 L) L (AutomorphicForm.globalPoints (𝓞 L) L (unitDiag a b)) ∈ finiteIntegralGL2 (𝓞 L) L := by
  have h0 : ∃ r : 𝓞 L, (r : L) = 0 := ⟨0, by simp⟩
  refine glFin_globalPoints_mem_finiteIntegralGL2 L _ (fun i j => ?_) (fun i j => ?_)
  · rw [coe_unitDiag]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact h0
    · exact h0
    · exact hb
  · rw [coe_unitDiag_inv]
    fin_cases i <;> fin_cases j
    · exact ha'
    · exact h0
    · exact h0
    · exact hb'

omit [NumberField K] [NumberField L] in

private theorem exists_coe_eq_val_map_and_inv (ε : (𝓞 L)ˣ) :
    (∃ r : 𝓞 L, (r : L) = (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ε : Lˣ)) ∧
      ∃ r : 𝓞 L, (r : L) = (((Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ε : Lˣ)⁻¹ : Lˣ) : L) :=
  ⟨⟨ε, rfl⟩, ⟨(ε⁻¹ : (𝓞 L)ˣ), by rw [← map_inv]; rfl⟩⟩

end Adelic

end UnitBalancing

end UnitBalancing

section ContributorExtraction

set_option autoImplicit false

open NumberField
open IsDedekindDomain
open scoped Pointwise

namespace ContributorExtraction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

omit [NumberField K] in
private theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

omit [NumberField K] in

private theorem isCompact_image_mul_inv_sigmaAdelicAct_centralScalar (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφs : HasCompactSupport φ) {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W) :
    IsCompact ((fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      p.1 * (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2))⁻¹) ''
        (tsupport φ ×ˢ W)) :=
  ((hφs : IsCompact (tsupport φ)).prod hW).image
    (continuous_fst.mul (((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      ((continuous_centralScalar L).comp continuous_snd)).inv))

omit [NumberField K] in

private theorem isCompact_image_mul_mul_inv_sigmaAdelicAct (tset : Finset (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    {Ξ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hΞ : IsCompact Ξ) :
    IsCompact ((fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      p.1 * p.2 * (AutomorphicForm.sigmaAdelicAct K L D σ p.1)⁻¹) '' ((tset : Set _) ×ˢ Ξ)) :=
  (tset.finite_toSet.isCompact.prod hΞ).image ((continuous_fst.mul continuous_snd).mul
    (((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp continuous_fst).inv))

omit [NumberField K] in

private theorem exists_mem_image_globalPoints_eq_of_ne_zero (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (tset : Finset (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (W : Set (AdeleRing (𝓞 L) L)ˣ)
    (t₀ : AutomorphicForm.AdelicGL2 (𝓞 L) L) {y : AutomorphicForm.AdelicGL2 (𝓞 L) L} (hy : y ∈ tset)
    {z : (AdeleRing (𝓞 L) L)ˣ} (hz : z ∈ W) (δ : GL (Fin 2) L)
    (hδ : φ ((t₀ * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (t₀ * y))) ≠ 0) :
    ∃ ξ' ∈ (fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        p.1 * p.2 * (AutomorphicForm.sigmaAdelicAct K L D σ p.1)⁻¹) '' ((tset : Set _) ×ˢ
          ((fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
            p.1 * (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2))⁻¹) ''
              (tsupport φ ×ˢ W))),
      AutomorphicForm.globalPoints (𝓞 L) L δ = t₀ * ξ' * (AutomorphicForm.sigmaAdelicAct K L D σ t₀)⁻¹ := by
  set k : AutomorphicForm.AdelicGL2 (𝓞 L) L := (t₀ * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (t₀ * y)) with hk
  have hkmem : k ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hδ)
  refine ⟨y * (k * (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z))⁻¹) *
    (AutomorphicForm.sigmaAdelicAct K L D σ y)⁻¹, ⟨(y, k *
      (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z))⁻¹),
      ⟨hy, ⟨(k, z), ⟨hkmem, hz⟩, rfl⟩⟩, rfl⟩, ?_⟩

  have hS : AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (t₀ * y))
      = AutomorphicForm.sigmaAdelicAct K L D σ t₀ * AutomorphicForm.sigmaAdelicAct K L D σ y *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) := by
    rw [UnitBalancing.centralScalar_mul_comm, map_mul, map_mul]
  rw [hk, hS]
  group

end ContributorExtraction

end ContributorExtraction

section RadiusToHeights

set_option autoImplicit false

open Finset

namespace RadiusToHeights

variable {ι : Type*} [Fintype ι]

private theorem one_add_pow_le_two_pow_mul {τ : ℝ} (hτ : 0 ≤ τ) (d : ℕ) :
    (1 + τ) ^ d ≤ 2 ^ d * (1 + τ ^ d) := by
  have h1 : 1 + τ ≤ 2 * max 1 τ := by
    have := le_max_left 1 τ
    have := le_max_right 1 τ
    linarith
  have h2 : (max 1 τ) ^ d ≤ 1 + τ ^ d := by
    rcases le_total τ 1 with h | h
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hτ d)
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left zero_le_one
  calc (1 + τ) ^ d ≤ (2 * max 1 τ) ^ d := pow_le_pow_left₀ (by linarith) h1 d
    _ = 2 ^ d * (max 1 τ) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (1 + τ ^ d) := mul_le_mul_of_nonneg_left h2 (by positivity)

private theorem one_add_pow_le_mul_prod_rpow (mult : ι → ℕ) (h : ι → ℝ) (hh : ∀ w, 0 ≤ h w) {κ' τ θ : ℝ}
    (hκ' : 0 ≤ κ') (hτ : 0 ≤ τ) (hθ : 0 ≤ θ) (hτd : τ ^ (∑ w, mult w) ≤ κ' * ∏ w, h w ^ mult w) (E : ℕ)
    (hdθ : ((∑ w, mult w : ℕ) : ℝ) * θ = E) :
    (1 + τ) ^ E ≤ (2 ^ (∑ w, mult w) * (1 + κ')) ^ θ * ∏ w, (1 + h w) ^ ((mult w : ℝ) * θ) := by
  set d : ℕ := ∑ w, mult w
  set P : ℝ := ∏ w, (1 + h w) ^ mult w with hP
  have hP1 : (1 : ℝ) ≤ P := by
    calc (1 : ℝ) = ∏ _w : ι, (1 : ℝ) := prod_const_one.symm
      _ ≤ P := prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_pow₀ (by linarith [hh w])
  have hP0 : (0 : ℝ) ≤ P := zero_le_one.trans hP1
  have hprod : ∏ w, h w ^ mult w ≤ P :=
    prod_le_prod (fun w _ => pow_nonneg (hh w) _) fun w _ => pow_le_pow_left₀ (hh w) (by linarith [hh w]) _

  have hstep : (1 + τ) ^ d ≤ 2 ^ d * (1 + κ') * P := by
    calc (1 + τ) ^ d ≤ 2 ^ d * (1 + τ ^ d) := one_add_pow_le_two_pow_mul hτ d
      _ ≤ 2 ^ d * ((1 + κ') * P) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc 1 + τ ^ d ≤ 1 + κ' * ∏ w, h w ^ mult w := by linarith [hτd]
            _ ≤ P + κ' * P := add_le_add hP1 (mul_le_mul_of_nonneg_left hprod hκ')
            _ = (1 + κ') * P := by ring
      _ = 2 ^ d * (1 + κ') * P := (mul_assoc _ _ _).symm

  have hτ1 : (0 : ℝ) ≤ 1 + τ := by linarith
  have hB0 : (0 : ℝ) ≤ 2 ^ d * (1 + κ') := by positivity
  have hleft : ((1 + τ) ^ d) ^ θ = (1 + τ) ^ E := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ1, hdθ, Real.rpow_natCast]
  have hright : (2 ^ d * (1 + κ') * P) ^ θ
      = (2 ^ d * (1 + κ')) ^ θ * ∏ w, (1 + h w) ^ ((mult w : ℝ) * θ) := by
    rw [Real.mul_rpow hB0 hP0, hP, ← Real.finsetProd_rpow Finset.univ (fun w => (1 + h w) ^ mult w)
      (fun w _ => pow_nonneg (by linarith [hh w]) _) θ]
    congr 1
    refine prod_congr rfl fun w _ => ?_
    rw [Real.rpow_mul (by linarith [hh w]), Real.rpow_natCast]
  rw [← hleft, ← hright]
  exact Real.rpow_le_rpow (pow_nonneg hτ1 d) hstep hθ

end RadiusToHeights

end RadiusToHeights

section SiegelPointCount

set_option autoImplicit false

open Module NumberField NumberField.AdelicLevel
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain

namespace SiegelPointCount

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem exists_forall_ncard_le_mul_prod {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    (tset : Finset (AutomorphicForm.AdelicGL2 (𝓞 L) L)) {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ y ∈ tset, ∀ s ∈ centreCutSiegelSet L c u d₁ d₂, ∀ z ∈ W,
      (({δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
          γ ∈ AutomorphicForm.centralCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ∩
        Function.support fun δ => φ ((s * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (s * y)))).ncard : ℝ)
        ≤ C * ∏ w : InfinitePlace L,
            (1 + localHeight (archComponent L w (glArch (𝓞 L) L s))) ^
              ((InfinitePlace.mult w : ℝ) * (((finrank ℚ L - 1 : ℕ) : ℝ) / (finrank ℚ L : ℝ))) := by

  have hΞ' := ContributorExtraction.isCompact_image_mul_mul_inv_sigmaAdelicAct K L D σ tset
    (ContributorExtraction.isCompact_image_mul_inv_sigmaAdelicAct_centralScalar K L D σ φ hφs hW)
  have hobt1 := AdelicExtraction.exists_forall_norm_archComponent_le L hΞ'
  obtain ⟨M, hM0, hM⟩ := hobt1
  have hobt2 := AdelicExtraction.exists_ne_zero_forall_algebraMap_mul_glFin_apply_mem L hΞ'
  obtain ⟨s₀, hs₀, hs₀Ξ⟩ := hobt2
  have hobt3 := UnitBalancing.exists_forall_exists_unit_mul_le_and_le_mul L
  obtain ⟨Cb, hCb1, hCb⟩ := hobt3
  have hCb0 : 0 < Cb := zero_lt_one.trans_le hCb1
  have hsκ0 : 0 < Real.sqrt (1 + u ^ 2 / c ^ 2) := Real.sqrt_pos.mpr (by positivity)
  set sκ : ℝ := Real.sqrt (1 + u ^ 2 / c ^ 2)
  set R₀ : ℝ := 4 * M * (Real.sqrt d₂ * Real.sqrt d₂ * (Cb * Cb * (Cb * Cb)) * sκ) / d₁ with hR₀
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; positivity
  have hobt4 := ContributorCount.exists_forall_ncard_le hgen s₀ hs₀ hR₀0
  obtain ⟨Cc, hCc⟩ := hobt4

  have hnpos : 0 < finrank ℚ L := finrank_pos
  set n : ℕ := finrank ℚ L
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  set θ : ℝ := ((n - 1 : ℕ) : ℝ) / (n : ℝ) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hd : ∑ w : InfinitePlace L, InfinitePlace.mult w = n := InfinitePlace.sum_mult_eq
  have hdθ : ((∑ w : InfinitePlace L, InfinitePlace.mult w : ℕ) : ℝ) * θ = ((n - 1 : ℕ) : ℝ) := by
    rw [hd, hθ, ← mul_div_assoc, mul_div_cancel_left₀ _ hn0]
  refine ⟨max Cc 0 * ((1 + R₀) ^ (n - 1) * (2 ^ (∑ w : InfinitePlace L, InfinitePlace.mult w) *
    (1 + sκ ^ (∑ w : InfinitePlace L, InfinitePlace.mult w))) ^ θ), fun y hy s hs z hz => ?_⟩
  have hobt5 := mem_centreCutSiegelSet_iff.mp hs
  obtain ⟨hsf, hsh, hsx, hsd⟩ := hobt5

  set a : InfinitePlace L → ℝ := fun w => Real.sqrt (u ^ 2 / c + localHeight (archComponent L w (glArch (𝓞 L) L s)))
  set b : InfinitePlace L → ℝ := fun w => (Real.sqrt (localHeight (archComponent L w (glArch (𝓞 L) L s))))⁻¹
  have ha : ∀ w, 0 < a w := fun w =>
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (by positivity) (hc.trans_le (hsh w)))
  have hb : ∀ w, 0 < b w := fun w => inv_pos.mpr (Real.sqrt_pos.mpr (hc.trans_le (hsh w)))
  have hobt6 := hCb a ha
  obtain ⟨ε₁, hε₁⟩ := hobt6
  have hobt7 := hCb b hb
  obtain ⟨ε₂, hε₂⟩ := hobt7
  have hAex0 : 0 < Real.exp (UnitBalancing.meanLog L a) := Real.exp_pos _
  have hDex0 : 0 < Real.exp (UnitBalancing.meanLog L b) := Real.exp_pos _
  set Aex : ℝ := Real.exp (UnitBalancing.meanLog L a)
  set Dex : ℝ := Real.exp (UnitBalancing.meanLog L b)
  set τ : ℝ := Aex / Dex with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  set α : Lˣ := Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ε₁
  set β : Lˣ := Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ε₂
  have hαcoe : ((α : Lˣ) : L) = ((ε₁ : 𝓞 L) : L) := rfl
  have hβcoe : ((β : Lˣ) : L) = ((ε₂ : 𝓞 L) : L) := rfl
  set t₀ : AutomorphicForm.AdelicGL2 (𝓞 L) L :=
    AutomorphicForm.globalPoints (𝓞 L) L (UnitBalancing.unitDiag α β) * s with ht₀

  rw [← UnitBalancing.ncard_inter_support_globalPoints_mul_eq K L D σ (UnitBalancing.unitDiag α β) _
    (UnitBalancing.mem_setOf_borel_central_iff hgen α β) φ (s * y) z]
  have hpt : AutomorphicForm.globalPoints (𝓞 L) L (UnitBalancing.unitDiag α β) * (s * y) = t₀ * y :=
    (mul_assoc _ _ _).symm
  rw [hpt]

  have hdet_s : ∀ w : InfinitePlace L, d₁ ≤ ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion)).det‖ ∧
      ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion)).det‖ ≤ d₂ := fun w => hsd w
  set A' : ℝ := Real.sqrt d₂ * (Cb * Aex) with hA'
  set D' : ℝ := Real.sqrt d₂ * (Cb * Dex) with hD'
  set m : ℝ := Aex * Dex * d₁ / (Cb * Cb * sκ) with hm
  have hA'0 : 0 ≤ A' := by rw [hA']; positivity
  have hD'0 : 0 ≤ D' := by rw [hD']; positivity
  have hden : 0 < Cb * Cb * sκ := by positivity
  have hm0 : 0 < m := by rw [hm]; positivity
  have htop : ∀ (w : InfinitePlace L) (j : Fin 2),
      ‖((archComponent L w (glArch (𝓞 L) L t₀) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖ ≤ A' := by
    intro w j
    rw [ht₀, UnitBalancing.norm_archComponent_globalPoints_unitDiag_mul_apply_zero,
      UnitBalancing.norm_coe_completion, hαcoe]
    calc w ((ε₁ : 𝓞 L) : L) * ‖((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) 0 j‖
        ≤ w ((ε₁ : 𝓞 L) : L) * (Real.sqrt d₂ * a w) :=
          mul_le_mul_of_nonneg_left
            (SiegelRowBounds.norm_apply_zero_le _ hc (hsh w) (hsx w) (hdet_s w).2 j) (apply_nonneg _ _)
      _ = Real.sqrt d₂ * (w ((ε₁ : 𝓞 L) : L) * a w) := by ring
      _ ≤ A' := mul_le_mul_of_nonneg_left (hε₁ w).1 (Real.sqrt_nonneg _)
  have hbot : ∀ (w : InfinitePlace L) (j : Fin 2),
      ‖((archComponent L w (glArch (𝓞 L) L t₀) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖ ≤ D' := by
    intro w j
    rw [ht₀, UnitBalancing.norm_archComponent_globalPoints_unitDiag_mul_apply_one,
      UnitBalancing.norm_coe_completion, hβcoe]
    calc w ((ε₂ : 𝓞 L) : L) * ‖((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) 1 j‖
        ≤ w ((ε₂ : 𝓞 L) : L) * (Real.sqrt d₂ * b w) :=
          mul_le_mul_of_nonneg_left
            (SiegelRowBounds.norm_apply_one_le _ hc (hsh w) (hdet_s w).2 j) (apply_nonneg _ _)
      _ = Real.sqrt d₂ * (w ((ε₂ : 𝓞 L) : L) * b w) := by ring
      _ ≤ D' := mul_le_mul_of_nonneg_left (hε₂ w).1 (Real.sqrt_nonneg _)
  have hdet : ∀ w : InfinitePlace L, m ≤ ‖(((archComponent L w (glArch (𝓞 L) L t₀) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion)).det‖ := by
    intro w
    rw [ht₀, UnitBalancing.norm_det_archComponent_globalPoints_unitDiag_mul, UnitBalancing.norm_coe_completion,
      UnitBalancing.norm_coe_completion, hαcoe, hβcoe, hm, div_le_iff₀ hden]
    have haw : 0 < a w := ha w
    have hbw : 0 < b w := hb w
    have hab : a w * b w ≤ sκ := BalancedExtraction.weight_mul_weight_le hc (hsh w)
    have h1 := (hε₁ w).2
    have h2 := (hε₂ w).2
    have hw1 : 0 ≤ w ((ε₁ : 𝓞 L) : L) := apply_nonneg _ _
    have hw2 : 0 ≤ w ((ε₂ : 𝓞 L) : L) := apply_nonneg _ _
    calc Aex * Dex * d₁
        ≤ (Cb * (w ((ε₁ : 𝓞 L) : L) * a w)) * (Cb * (w ((ε₂ : 𝓞 L) : L) * b w)) *
            ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion)).det‖ :=
          mul_le_mul (mul_le_mul h1 h2 hDex0.le (by positivity)) (hdet_s w).1 hd₁.le (by positivity)
      _ = Cb * Cb * (w ((ε₁ : 𝓞 L) : L) * w ((ε₂ : 𝓞 L) : L) *
            ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion)).det‖) * (a w * b w) := by ring
      _ ≤ Cb * Cb * (w ((ε₁ : 𝓞 L) : L) * w ((ε₂ : 𝓞 L) : L) *
            ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion)).det‖) * sκ :=
          mul_le_mul_of_nonneg_left hab (by positivity)
      _ = w ((ε₁ : 𝓞 L) : L) * w ((ε₂ : 𝓞 L) : L) *
            ‖(((archComponent L w (glArch (𝓞 L) L s) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion)).det‖ * (Cb * Cb * sκ) := by ring

  have hdiag_const : 4 * M * (A' * D') / m ≤ R₀ := by
    rw [hA', hD', hm, hR₀]
    refine le_of_eq ?_
    field_simp
  have hoff_const : 4 * M * (A' * A') / m ≤ R₀ * τ := by
    rw [hA', hm, hR₀, hτ]
    refine le_of_eq ?_
    field_simp

  have ht₀fin : glFin (𝓞 L) L t₀ ∈ finiteIntegralGL2 (𝓞 L) L := by
    rw [ht₀, map_mul]
    have hobt8 := UnitBalancing.exists_coe_eq_val_map_and_inv L ε₁
    obtain ⟨hα1, hα2⟩ := hobt8
    have hobt9 := UnitBalancing.exists_coe_eq_val_map_and_inv L ε₂
    obtain ⟨hβ1, hβ2⟩ := hobt9
    exact mul_mem (UnitBalancing.glFin_globalPoints_unitDiag_mem_finiteIntegralGL2 L α β hα1 hα2 hβ1 hβ2) hsf

  have hρ0 : 0 ≤ R₀ * τ := mul_nonneg hR₀0 hτ0
  refine (hCc (R₀ * τ) hρ0 _ ?_).2.trans ?_
  · intro δ hδ
    obtain ⟨⟨h10, hcentral⟩, hsupp⟩ := hδ
    have hobt10 := ContributorExtraction.exists_mem_image_globalPoints_eq_of_ne_zero K L D σ φ tset W
      t₀ hy hz δ (Function.mem_support.mp hsupp)
    obtain ⟨ξ', hξ'Ξ, hGδ⟩ := hobt10
    refine ⟨h10, hcentral, fun w => ?_, fun i j => ?_⟩
    · obtain ⟨h00, h01, h11⟩ := AdelicExtraction.place_apply_le_of_eq_mul_mul_inv K L D σ hA'0 hD'0 hm0 hM0 t₀ ξ'
        htop hbot hdet (hM ξ' hξ'Ξ) δ hGδ w
      exact ⟨h00.trans hdiag_const, h11.trans hdiag_const, h01.trans hoff_const⟩
    · exact AdelicExtraction.exists_eq_mul_apply_of_eq_mul_mul_inv K L D σ s₀ t₀ ξ' ht₀fin (hs₀Ξ ξ' hξ'Ξ) δ hGδ i j

  have hA : Aex ^ (∑ w : InfinitePlace L, InfinitePlace.mult w) = ∏ w : InfinitePlace L,
      Real.sqrt (u ^ 2 / c + localHeight (archComponent L w (glArch (𝓞 L) L s))) ^ InfinitePlace.mult w := by
    rw [hd]; exact UnitBalancing.exp_meanLog_pow L a ha
  have hD : Dex ^ (∑ w : InfinitePlace L, InfinitePlace.mult w) = ∏ w : InfinitePlace L,
      (Real.sqrt (localHeight (archComponent L w (glArch (𝓞 L) L s))))⁻¹ ^ InfinitePlace.mult w := by
    rw [hd]; exact UnitBalancing.exp_meanLog_pow L b hb
  have hbal := (BalancedExtraction.prod_height_le_div_pow hc
    (fun w => localHeight (archComponent L w (glArch (𝓞 L) L s))) hsh InfinitePlace.mult hA hD).2
  have hrad := RadiusToHeights.one_add_pow_le_mul_prod_rpow InfinitePlace.mult
    (fun w => localHeight (archComponent L w (glArch (𝓞 L) L s))) (fun w => (hc.trans_le (hsh w)).le)
    (pow_nonneg hsκ0.le _) hτ0 hθ0 hbal (n - 1) hdθ
  clear_value n
  have h1R : (1 + R₀ * τ) ^ (n - 1) ≤ (1 + R₀) ^ (n - 1) * (1 + τ) ^ (n - 1) := by
    rw [← mul_pow]
    have hRτ : 1 + R₀ * τ ≤ (1 + R₀) * (1 + τ) :=
      calc 1 + R₀ * τ ≤ 1 + R₀ * τ + (R₀ + τ) := le_add_of_nonneg_right (add_nonneg hR₀0 hτ0)
        _ = (1 + R₀) * (1 + τ) := by ring
    exact pow_le_pow_left₀ (by positivity) hRτ _
  calc Cc * (1 + R₀ * τ) ^ (n - 1)
      ≤ max Cc 0 * (1 + R₀ * τ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (add_nonneg zero_le_one (mul_nonneg hR₀0 hτ0)) _)
    _ ≤ max Cc 0 * ((1 + R₀) ^ (n - 1) * ((2 ^ (∑ w : InfinitePlace L, InfinitePlace.mult w) *
          (1 + sκ ^ (∑ w : InfinitePlace L, InfinitePlace.mult w))) ^ θ *
            ∏ w : InfinitePlace L, (1 + localHeight (archComponent L w (glArch (𝓞 L) L s))) ^
              ((InfinitePlace.mult w : ℝ) * θ))) := by
        refine mul_le_mul_of_nonneg_left (h1R.trans ?_) (le_max_right _ _)
        exact mul_le_mul_of_nonneg_left hrad (pow_nonneg (add_nonneg zero_le_one hR₀0) _)
    _ = _ := by ring

end SiegelPointCount

end SiegelPointCount

section SiegelContraction

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
open NumberField.SiegelVolume NumberField.AdelicVolume NumberField.AdelicLevel

namespace SiegelContraction

variable {L : Type} [Field L]

private theorem norm_natCast_completion (w : InfinitePlace L) (n : ℕ) : ‖(n : w.Completion)‖ = n := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    map_natCast, Complex.norm_natCast]

private theorem natCast_ne_zero_completion (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) : (n : w.Completion) ≠ 0 := by
  intro h
  have h' := norm_natCast_completion w n
  rw [h, norm_zero] at h'
  exact hn (by exact_mod_cast h'.symm)

private theorem det_upperUnit_natCast (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) (b : w.Completion) :
    ((upperUnit (n : w.Completion)⁻¹ b (n : w.Completion) (inv_ne_zero (natCast_ne_zero_completion w hn))
        (natCast_ne_zero_completion w hn) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det
      = 1 := by
  rw [show ((upperUnit (n : w.Completion)⁻¹ b (n : w.Completion) (inv_ne_zero (natCast_ne_zero_completion w hn))
      (natCast_ne_zero_completion w hn) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = !![(n : w.Completion)⁻¹, b; 0, (n : w.Completion)] from rfl, Matrix.det_fin_two_of]
  rw [inv_mul_cancel₀ (natCast_ne_zero_completion w hn)]
  ring

variable [NumberField L]

private noncomputable def contractionN (w : InfinitePlace L) (n : ℕ) (hn : n ≠ 0) (b : w.Completion) : AdelicGL2 (𝓞 L) L :=
  archEmbed L w (upperUnit (n : w.Completion)⁻¹ b (n : w.Completion)
    (inv_ne_zero (natCast_ne_zero_completion w hn)) (natCast_ne_zero_completion w hn))

private theorem localHeight_contractionN_mul (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) (b : w.Completion)
    (g : AdelicGL2 (𝓞 L) L) :
    localHeight (archComponent L w (glArch (𝓞 L) L (contractionN w n hn b * g)))
      = localHeight (archComponent L w (glArch (𝓞 L) L g)) / (n : ℝ) ^ 2 := by
  unfold contractionN
  rw [archComponent_glArch_archEmbed_mul_self,
    localHeight_upper_entries_mul (a := (n : w.Completion)⁻¹) (t := (n : w.Completion))
      (natCast_ne_zero_completion w hn) rfl rfl rfl, norm_inv, norm_natCast_completion]
  ring

private theorem localHeight_contractionN_mul_of_ne {w v : InfinitePlace L} (hv : v ≠ w) {n : ℕ} (hn : n ≠ 0)
    (b : w.Completion) (g : AdelicGL2 (𝓞 L) L) :
    localHeight (archComponent L v (glArch (𝓞 L) L (contractionN w n hn b * g)))
      = localHeight (archComponent L v (glArch (𝓞 L) L g)) := by
  unfold contractionN
  rw [archComponent_glArch_archEmbed_mul_of_ne hv]

private theorem xWindowSq_contractionN_mul_of_ne {w v : InfinitePlace L} (hv : v ≠ w) {n : ℕ} (hn : n ≠ 0)
    (b : w.Completion) (g : AdelicGL2 (𝓞 L) L) :
    xWindowSq (archComponent L v (glArch (𝓞 L) L (contractionN w n hn b * g)))
      = xWindowSq (archComponent L v (glArch (𝓞 L) L g)) := by
  unfold contractionN
  rw [archComponent_glArch_archEmbed_mul_of_ne hv]

private theorem archDetNorm_contractionN_mul (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) (b : w.Completion)
    (v : InfinitePlace L) (g : AdelicGL2 (𝓞 L) L) :
    archDetNorm v (contractionN w n hn b * g) = archDetNorm v g := by
  by_cases hv : v = w
  · subst hv
    unfold contractionN
    rw [archDetNorm_archEmbed_mul_self, det_upperUnit_natCast v hn b, norm_one, one_mul]
  · unfold contractionN
    rw [archDetNorm_archEmbed_mul_of_ne hv]

private theorem glFin_contractionN_mul (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) (b : w.Completion)
    (g : AdelicGL2 (𝓞 L) L) : glFin (𝓞 L) L (contractionN w n hn b * g) = glFin (𝓞 L) L g := by
  unfold contractionN
  rw [glFin_archEmbed_mul]

private theorem xAt_contractionN_mul (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) (b : w.Completion)
    (g : AdelicGL2 (𝓞 L) L) :
    xAt w (contractionN w n hn b * g)
      = xAt w g / (n : ℂ) ^ 2 + InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ) := by
  set φ := InfinitePlace.Completion.extensionEmbedding w
  set s : GL (Fin 2) w.Completion := upperUnit (n : w.Completion)⁻¹ b (n : w.Completion)
    (inv_ne_zero (natCast_ne_zero_completion w hn)) (natCast_ne_zero_completion w hn) with hs
  set h : GL (Fin 2) w.Completion := archComponent L w (glArch (𝓞 L) L g) with hh
  have hmap : ∀ k : GL (Fin 2) w.Completion, ((k : Matrix (Fin 2) (Fin 2) w.Completion).map φ)
      = ((Matrix.GeneralLinearGroup.map φ k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun k => rfl
  have hnφ : φ n = n := map_natCast φ n
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlaw := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ s) (a := (n : ℂ)⁻¹)
    (b := φ b) (t := n) hnC
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_zero_zero, map_inv₀, hnφ])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_zero_one])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_one_zero, map_zero])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_one_one, hnφ])
    (Matrix.GeneralLinearGroup.map φ h)
  unfold xAt
  rw [contractionN, ← hs, archComponent_glArch_archEmbed_mul_self, ← hh, hmap, hmap, map_mul, hlaw]
  ring

private theorem contractionN_mul_mem {c u d₁ d₂ : ℝ} (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) {b : w.Completion}
    (hb : ‖InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ)‖ ≤ |u| - |u| / (n : ℝ) ^ 2)
    {g : AdelicGL2 (𝓞 L) L} (hg : g ∈ centreCutSiegelSet L c u d₁ d₂)
    (hhigh : (n : ℝ) ^ 2 * c ≤ localHeight (archComponent L w (glArch (𝓞 L) L g))) :
    contractionN w n hn b * g ∈ centreCutSiegelSet L c u d₁ d₂ := by
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  obtain ⟨hK, hfl, hwin, hdet⟩ := hg
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [glFin_contractionN_mul]
    exact hK
  · by_cases hv : v = w
    · subst hv
      rw [localHeight_contractionN_mul, le_div_iff₀ hn2]
      linarith
    · rw [localHeight_contractionN_mul_of_ne hv]
      exact hfl v
  · by_cases hv : v = w
    · subst hv
      rw [xWindowSq_eq_norm_xAt_sq, xAt_contractionN_mul, ← sq_abs u]
      refine (sq_le_sq₀ (norm_nonneg _) (abs_nonneg u)).mpr ?_
      have hx := norm_xAt_le ⟨hK, hfl, hwin, hdet⟩ v
      have hn2C : ‖((n : ℂ) ^ 2)‖ = (n : ℝ) ^ 2 := by rw [norm_pow, Complex.norm_natCast]
      calc ‖xAt v g / (n : ℂ) ^ 2 + InfinitePlace.Completion.extensionEmbedding v b / (n : ℂ)‖
          ≤ ‖xAt v g / (n : ℂ) ^ 2‖ + ‖InfinitePlace.Completion.extensionEmbedding v b / (n : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖xAt v g‖ / (n : ℝ) ^ 2 + ‖InfinitePlace.Completion.extensionEmbedding v b / (n : ℂ)‖ := by
            rw [norm_div, hn2C]
        _ ≤ |u| / (n : ℝ) ^ 2 + (|u| - |u| / (n : ℝ) ^ 2) := by
            gcongr
        _ = |u| := by ring
    · rw [xWindowSq_contractionN_mul_of_ne hv]
      exact hwin v
  · rw [archDetNorm_contractionN_mul]
    exact hdet v

private theorem contractionN_mul_ne {c u d₁ d₂ : ℝ} (w : InfinitePlace L) {n : ℕ} (hn : n ≠ 0) {b b' : w.Completion}
    (hsep : 2 * |u| / (n : ℝ) ^ 2 < ‖InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ)
      - InfinitePlace.Completion.extensionEmbedding w b' / (n : ℂ)‖)
    {g g' : AdelicGL2 (𝓞 L) L} (hg : g ∈ centreCutSiegelSet L c u d₁ d₂)
    (hg' : g' ∈ centreCutSiegelSet L c u d₁ d₂) :
    contractionN w n hn b * g ≠ contractionN w n hn b' * g' := by
  intro he
  have hx : xAt w (contractionN w n hn b * g) = xAt w (contractionN w n hn b' * g') := by rw [he]
  rw [xAt_contractionN_mul, xAt_contractionN_mul] at hx
  have hdiff : InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ)
      - InfinitePlace.Completion.extensionEmbedding w b' / (n : ℂ) = (xAt w g' - xAt w g) / (n : ℂ) ^ 2 := by
    linear_combination hx
  have hn2C : ‖((n : ℂ) ^ 2)‖ = (n : ℝ) ^ 2 := by rw [norm_pow, Complex.norm_natCast]
  have hbound : ‖(xAt w g' - xAt w g) / (n : ℂ) ^ 2‖ ≤ 2 * |u| / (n : ℝ) ^ 2 := by
    rw [norm_div, hn2C]
    have h2 : ‖xAt w g' - xAt w g‖ ≤ 2 * |u| := by
      have := (norm_sub_le _ _).trans (add_le_add (norm_xAt_le hg' w) (norm_xAt_le hg w))
      linarith
    gcongr
  rw [hdiff] at hsep
  exact absurd hbound (not_le.mpr hsep)

end SiegelContraction

end SiegelContraction

section SiegelShifts

set_option autoImplicit false

open NumberField Finset

namespace SiegelShifts

variable {L : Type} [Field L]

private theorem one_le_abs_sub_of_ne {j j' : ℕ} (h : j ≠ j') : (1 : ℝ) ≤ |(j : ℝ) - j'| := by
  have hz : ((j : ℤ) - j' : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have h1 := Int.one_le_abs hz
  exact_mod_cast h1

private theorem steps_bounds {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 2 / 10 ≤ ((n ^ 2 - 1) / 6 : ℕ) ∧ 6 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = n ^ 2 := ⟨_, rfl⟩
  have hm16 : 16 ≤ m := by
    rw [hm]
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  rw [← hm]
  have h1 : m ≤ 6 * ((m - 1) / 6) + 6 := by omega
  have h2 : 6 * ((m - 1) / 6) + 1 ≤ m := by omega
  have h1' : (m : ℝ) ≤ 6 * (((m - 1) / 6 : ℕ) : ℝ) + 6 := by exact_mod_cast h1
  have h2' : 6 * (((m - 1) / 6 : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h2
  have hm16' : (16 : ℝ) ≤ m := by exact_mod_cast hm16
  have hmn : (m : ℝ) = (n : ℝ) ^ 2 := by rw [hm, Nat.cast_pow]
  rw [← hmn]
  constructor
  · linarith
  · exact h2'

private theorem exists_spacing {u : ℝ} (hu : u ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ δ : ℚ, 2 * |u| / (n : ℝ) ^ 2 < δ ∧ (δ : ℝ) < 3 * |u| / (n : ℝ) ^ 2 := by
  have hu' : 0 < |u| := abs_pos.2 hu
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  exact exists_rat_btwn (div_lt_div_of_pos_right (by linarith) hn2)

private theorem two_mul_steps_mul_spacing_le {u : ℝ} {n : ℕ} (hn : 4 ≤ n) {δ : ℚ}
    (hδ : (δ : ℝ) < 3 * |u| / (n : ℝ) ^ 2) (_ : 0 ≤ (δ : ℝ)) :
    2 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ) * δ ≤ |u| - |u| / (n : ℝ) ^ 2 := by
  obtain ⟨-, hJ⟩ := steps_bounds hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hn2' : (n : ℝ) ^ 2 ≠ 0 := hn2.ne'
  have hJ0 : (0 : ℝ) ≤ 2 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ) := by positivity
  calc 2 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ) * δ ≤ 2 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ) * (3 * |u| / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hδ.le hJ0
    _ = (6 * (((n ^ 2 - 1) / 6 : ℕ) : ℝ)) * |u| / (n : ℝ) ^ 2 := by ring
    _ ≤ ((n : ℝ) ^ 2 - 1) * |u| / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg u)) hn2.le
    _ = |u| - |u| / (n : ℝ) ^ 2 := by
        rw [div_eq_iff hn2', sub_mul _ _ ((n : ℝ) ^ 2), div_mul_cancel₀ _ hn2']
        ring

section OnePlace

variable (w : InfinitePlace L)

private def IsShiftFamily (u : ℝ) (n : ℕ) (B : Finset w.Completion) : Prop :=
  ((n : ℝ) ^ 2 / 10) ^ w.mult ≤ B.card ∧
    (∀ b ∈ B, ‖InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ)‖ ≤ |u| - |u| / (n : ℝ) ^ 2) ∧
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → 2 * |u| / (n : ℝ) ^ 2 <
      ‖InfinitePlace.Completion.extensionEmbedding w b / (n : ℂ)
        - InfinitePlace.Completion.extensionEmbedding w b' / (n : ℂ)‖

variable {w}

private theorem exists_shiftFamily_of_isReal (hw : w.IsReal) {u : ℝ} (hu : u ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    ∃ B : Finset w.Completion, IsShiftFamily w u n B := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  obtain ⟨δ, hδ1, hδ2⟩ := exists_spacing hu hn0
  have hδ0 : (0 : ℝ) < δ := lt_of_le_of_lt (by positivity) hδ1
  have hδq : δ ≠ 0 := by exact_mod_cast hδ0.ne'
  set J : ℕ := (n ^ 2 - 1) / 6
  set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
  let f : ℕ → w.Completion := fun j => (((j : ℚ) * δ * n : ℚ) : w.Completion)
  have hval : ∀ j : ℕ, φ (f j) / (n : ℂ) = (((j : ℝ) * δ : ℝ) : ℂ) := by
    intro j
    simp only [f, hφ, map_ratCast]
    push_cast
    exact mul_div_cancel_right₀ _ hnC
  have hinj : Function.Injective f := by
    intro j j' h
    have h1 := congrArg φ h
    simp only [f, hφ, map_ratCast] at h1
    have h2 := Rat.cast_injective h1
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have h3 : (j : ℚ) = j' := mul_right_cancel₀ hδq (mul_right_cancel₀ hnq h2)
    exact_mod_cast h3
  refine ⟨(range J).image f, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_range]
    have h1 : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hw⟩
    have hJ' : (n : ℝ) ^ 2 / 10 ≤ J := (steps_bounds hn).1
    rw [h1, pow_one]
    exact hJ'
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    rw [mem_range] at hj
    have hjδ : (0 : ℝ) ≤ (j : ℝ) * δ := by positivity
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hjδ]
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj.le
    have hJδ : (0 : ℝ) ≤ (J : ℝ) * δ := by positivity
    have hJu : 2 * (J : ℝ) * δ ≤ |u| - |u| / (n : ℝ) ^ 2 := two_mul_steps_mul_spacing_le hn hδ2 hδ0.le
    calc (j : ℝ) * δ ≤ J * δ := mul_le_mul_of_nonneg_right hjJ hδ0.le
      _ ≤ |u| - |u| / (n : ℝ) ^ 2 := by linarith
  · intro b hb b' hb' hne
    obtain ⟨j, -, rfl⟩ := mem_image.mp hb
    obtain ⟨j', -, rfl⟩ := mem_image.mp hb'
    have hjj' : j ≠ j' := fun h => hne (by rw [h])
    rw [hval, hval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ((j : ℝ) * δ - (j' : ℝ) * δ) = ((j : ℝ) - j') * δ := by ring
    rw [h1, abs_mul, abs_of_pos hδ0]
    calc 2 * |u| / (n : ℝ) ^ 2 < δ := hδ1
      _ = 1 * (δ : ℝ) := (one_mul _).symm
      _ ≤ |(j : ℝ) - j'| * δ := mul_le_mul_of_nonneg_right (one_le_abs_sub_of_ne hjj') hδ0.le

private theorem exists_shiftFamily_of_isComplex (hw : w.IsComplex) {u : ℝ} (hu : u ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    ∃ B : Finset w.Completion, IsShiftFamily w u n B := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  obtain ⟨δ, hδ1, hδ2⟩ := exists_spacing hu hn0
  have hδ0 : (0 : ℝ) < δ := lt_of_le_of_lt (by positivity) hδ1
  set J : ℕ := (n ^ 2 - 1) / 6
  set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
  obtain ⟨ι, hι⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw Complex.I
  let f : ℕ × ℕ → w.Completion := fun p =>
    (((p.1 : ℚ) * δ * n : ℚ) : w.Completion) + (((p.2 : ℚ) * δ * n : ℚ) : w.Completion) * ι
  have hval : ∀ p : ℕ × ℕ, φ (f p) / (n : ℂ)
      = (((p.1 : ℝ) * δ : ℝ) : ℂ) + (((p.2 : ℝ) * δ : ℝ) : ℂ) * Complex.I := by
    intro p
    simp only [f, hφ, map_add, map_mul, map_ratCast, hι]
    push_cast
    rw [div_eq_iff hnC]
    ring
  have hre : ∀ p : ℕ × ℕ, (φ (f p) / (n : ℂ)).re = (p.1 : ℝ) * δ := by
    intro p; rw [hval]; simp
  have him : ∀ p : ℕ × ℕ, (φ (f p) / (n : ℂ)).im = (p.2 : ℝ) * δ := by
    intro p; rw [hval]; simp
  have hinj : Function.Injective f := by
    intro p p' h
    have h1 : φ (f p) / (n : ℂ) = φ (f p') / (n : ℂ) := by rw [h]
    have hre' := hre p; rw [h1, hre p'] at hre'
    have him' := him p; rw [h1, him p'] at him'
    have e1 : (p'.1 : ℝ) = p.1 := mul_right_cancel₀ hδ0.ne' hre'
    have e2 : (p'.2 : ℝ) = p.2 := mul_right_cancel₀ hδ0.ne' him'
    exact Prod.ext (by exact_mod_cast e1.symm) (by exact_mod_cast e2.symm)
  refine ⟨(range J ×ˢ range J).image f, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_product, card_range]
    have h2 : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, hw⟩
    rw [h2]
    have hJ' : (n : ℝ) ^ 2 / 10 ≤ J := (steps_bounds hn).1
    calc ((n : ℝ) ^ 2 / 10) ^ 2 ≤ (J : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hJ' 2
      _ = ((J * J : ℕ) : ℝ) := by push_cast; ring
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    rw [mem_product, mem_range, mem_range] at hp
    have h1 : (p.1 : ℝ) ≤ J := by exact_mod_cast hp.1.le
    have h2 : (p.2 : ℝ) ≤ J := by exact_mod_cast hp.2.le
    have h1δ : (0 : ℝ) ≤ (p.1 : ℝ) * δ := by positivity
    have h2δ : (0 : ℝ) ≤ (p.2 : ℝ) * δ := by positivity
    have hJu : 2 * (J : ℝ) * δ ≤ |u| - |u| / (n : ℝ) ^ 2 := two_mul_steps_mul_spacing_le hn hδ2 hδ0.le
    have h1' : (p.1 : ℝ) * δ ≤ J * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
    have h2' : (p.2 : ℝ) * δ ≤ J * δ := mul_le_mul_of_nonneg_right h2 hδ0.le
    rw [hval]
    calc ‖(((p.1 : ℝ) * δ : ℝ) : ℂ) + (((p.2 : ℝ) * δ : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(((p.1 : ℝ) * δ : ℝ) : ℂ)‖ + ‖(((p.2 : ℝ) * δ : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = (p.1 : ℝ) * δ + (p.2 : ℝ) * δ := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg h1δ, abs_of_nonneg h2δ]
      _ ≤ |u| - |u| / (n : ℝ) ^ 2 := by linarith
  · intro b hb b' hb' hne
    obtain ⟨p, -, rfl⟩ := mem_image.mp hb
    obtain ⟨p', -, rfl⟩ := mem_image.mp hb'
    have hpp' : p ≠ p' := fun h => hne (by rw [h])
    set z := φ (f p) / (n : ℂ) - φ (f p') / (n : ℂ) with hz
    have hzre : z.re = ((p.1 : ℝ) - p'.1) * δ := by rw [hz, Complex.sub_re, hre, hre]; ring
    have hzim : z.im = ((p.2 : ℝ) - p'.2) * δ := by rw [hz, Complex.sub_im, him, him]; ring
    have hδle : ∀ {a a' : ℕ}, a ≠ a' → (δ : ℝ) ≤ |((a : ℝ) - a') * δ| := by
      intro a a' haa'
      rw [abs_mul, abs_of_pos hδ0]
      calc (δ : ℝ) = 1 * δ := (one_mul _).symm
        _ ≤ |(a : ℝ) - a'| * δ := mul_le_mul_of_nonneg_right (one_le_abs_sub_of_ne haa') hδ0.le
    refine hδ1.trans_le ?_
    by_cases h1 : p.1 = p'.1
    · have h2 : p.2 ≠ p'.2 := fun h => hpp' (Prod.ext h1 h)
      calc (δ : ℝ) ≤ |z.im| := by rw [hzim]; exact hδle h2
        _ ≤ ‖z‖ := Complex.abs_im_le_norm z
    · calc (δ : ℝ) ≤ |z.re| := by rw [hzre]; exact hδle h1
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z

private theorem exists_shiftFamily (w : InfinitePlace L) {u : ℝ} (hu : u ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    ∃ B : Finset w.Completion, IsShiftFamily w u n B :=
  (InfinitePlace.isReal_or_isComplex w).elim (fun hw => exists_shiftFamily_of_isReal hw hu hn)
    (fun hw => exists_shiftFamily_of_isComplex hw hu hn)

end OnePlace

end SiegelShifts

end SiegelShifts

section WeightedContractionDecay

set_option autoImplicit false

open MeasureTheory Set MeasureTheory.ContractionDecay
open scoped ENNReal

namespace WeightedContractionDecay

section Calculus

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {ι : Type*}

private theorem card_mul_measure_shell_succ_le (ν : Measure G) {S : Set G} (hS : MeasurableSet S) {φ : G → ℝ}
    (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {B : Finset ι} {p : ι → G}
    (hp : ∀ i ∈ B, ∀ g ∈ S, r * c ≤ φ g → p i * g ∈ S ∧ φ (p i * g) = φ g / r)
    (hsep : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p i * g ≠ p j * g')
    (hν : ∀ i ∈ B, ∀ T : Set G, MeasurableSet T → ν ((fun g => p i * g) '' T) = ν T) (k : ℕ) :
    (B.card : ℝ≥0∞) * ν (shell S φ c r (k + 1)) ≤ ν (shell S φ c r k) := by
  set T := shell S φ c r (k + 1)
  have hT : MeasurableSet T := measurableSet_shell hS hφ c r (k + 1)
  have hmeas : ∀ i ∈ B, MeasurableSet ((fun g => p i * g) '' T) := fun i _ => by
    rw [image_mul_left]
    exact measurable_const_mul _ hT
  have hdisj : (↑B : Set ι).PairwiseDisjoint fun i => (fun g => p i * g) '' T := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', he⟩
    exact hsep i hi j hj hij g hg.1 g' hg'.1 (mul_le_of_mem_shell_succ hc hr hg)
      (mul_le_of_mem_shell_succ hc hr hg') he.symm
  calc (B.card : ℝ≥0∞) * ν T = ∑ _i ∈ B, ν T := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ i ∈ B, ν ((fun g => p i * g) '' T) := Finset.sum_congr rfl fun i hi => (hν i hi T hT).symm
    _ = ν (⋃ i ∈ B, (fun g => p i * g) '' T) := (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ ν (shell S φ c r k) :=
        measure_mono (iUnion₂_subset fun i hi => image_mul_shell_succ_subset hc hr (hp i hi) k)

private theorem measure_shell_le_inv_pow_mul (ν : Measure G) {S : Set G} (hS : MeasurableSet S) {φ : G → ℝ}
    (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {B : Finset ι} (hB : B.Nonempty) {p : ι → G}
    (hp : ∀ i ∈ B, ∀ g ∈ S, r * c ≤ φ g → p i * g ∈ S ∧ φ (p i * g) = φ g / r)
    (hsep : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p i * g ≠ p j * g')
    (hν : ∀ i ∈ B, ∀ T : Set G, MeasurableSet T → ν ((fun g => p i * g) '' T) = ν T) (k : ℕ) :
    ν (shell S φ c r k) ≤ (B.card : ℝ≥0∞)⁻¹ ^ k * ν (shell S φ c r 0) := by
  have hN0 : (B.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hB.card_pos.ne'
  have hNtop : (B.card : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  induction k with
  | zero => simp
  | succ k ih =>
    calc ν (shell S φ c r (k + 1))
        = (B.card : ℝ≥0∞)⁻¹ * ((B.card : ℝ≥0∞) * ν (shell S φ c r (k + 1))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
      _ ≤ (B.card : ℝ≥0∞)⁻¹ * ν (shell S φ c r k) :=
          mul_le_mul_right (card_mul_measure_shell_succ_le ν hS hφ hc hr hp hsep hν k) _
      _ ≤ (B.card : ℝ≥0∞)⁻¹ * ((B.card : ℝ≥0∞)⁻¹ ^ k * ν (shell S φ c r 0)) := mul_le_mul_right ih _
      _ = (B.card : ℝ≥0∞)⁻¹ ^ (k + 1) * ν (shell S φ c r 0) := by rw [← mul_assoc, pow_succ']

private theorem setLIntegral_le_tsum_mul (ν : Measure G) {S : Set G} (hS : MeasurableSet S) {φ : G → ℝ}
    (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (hSc : ∀ g ∈ S, c ≤ φ g) {B : Finset ι}
    (hB : B.Nonempty) {p : ι → G}
    (hp : ∀ i ∈ B, ∀ g ∈ S, r * c ≤ φ g → p i * g ∈ S ∧ φ (p i * g) = φ g / r)
    (hsep : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p i * g ≠ p j * g')
    (hν : ∀ i ∈ B, ∀ T : Set G, MeasurableSet T → ν ((fun g => p i * g) '' T) = ν T)
    {F : G → ℝ≥0∞} {a : ℕ → ℝ≥0∞} (hF : ∀ k, ∀ g ∈ shell S φ c r k, F g ≤ a k) :
    ∫⁻ g in S, F g ∂ν ≤ (∑' k, a k * (B.card : ℝ≥0∞)⁻¹ ^ k) * ν S := by
  calc ∫⁻ g in S, F g ∂ν = ∫⁻ g in ⋃ k, shell S φ c r k, F g ∂ν := by rw [iUnion_shell hc hr hSc]
    _ ≤ ∑' k, ∫⁻ g in shell S φ c r k, F g ∂ν := lintegral_iUnion_le _ _
    _ ≤ ∑' k, a k * (B.card : ℝ≥0∞)⁻¹ ^ k * ν S := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc ∫⁻ g in shell S φ c r k, F g ∂ν ≤ ∫⁻ _ in shell S φ c r k, a k ∂ν :=
              setLIntegral_mono measurable_const (hF k)
          _ = a k * ν (shell S φ c r k) := setLIntegral_const _ _
          _ ≤ a k * ((B.card : ℝ≥0∞)⁻¹ ^ k * ν (shell S φ c r 0)) :=
              mul_le_mul_right (measure_shell_le_inv_pow_mul ν hS hφ hc hr hB hp hsep hν k) _
          _ ≤ a k * ((B.card : ℝ≥0∞)⁻¹ ^ k * ν S) :=
              mul_le_mul_right (mul_le_mul_right (measure_mono fun _ hg => hg.1) _) _
          _ = a k * (B.card : ℝ≥0∞)⁻¹ ^ k * ν S := by rw [mul_assoc]
    _ = (∑' k, a k * (B.card : ℝ≥0∞)⁻¹ ^ k) * ν S := ENNReal.tsum_mul_right

end Calculus

section Density

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

private theorem withDensity_image_mul_left_eq (μ : Measure G) [μ.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) {q : G} (hq : ∀ g, f (q * g) = f g) {T : Set G} (hT : MeasurableSet T) :
    μ.withDensity f ((fun g => q * g) '' T) = μ.withDensity f T := by
  have hT' : MeasurableSet ((fun g => q * g) '' T) := by
    rw [image_mul_left]
    exact measurable_const_mul _ hT
  have hinv : ∀ g, f (q⁻¹ * g) = f g := fun g => by
    conv_rhs => rw [← mul_inv_cancel_left q g]
    rw [hq (q⁻¹ * g)]
  rw [withDensity_apply _ hT', withDensity_apply _ hT, image_mul_left]
  calc ∫⁻ g in (fun g => q⁻¹ * g) ⁻¹' T, f g ∂μ
      = ∫⁻ g in (fun g => q⁻¹ * g) ⁻¹' T, f (q⁻¹ * g) ∂μ :=
        setLIntegral_congr_fun ((measurable_const_mul _) hT) fun g _ => (hinv g).symm
    _ = ∫⁻ g in T, f g ∂μ := (measurePreserving_mul_left μ q⁻¹).setLIntegral_comp_preimage hT hf

end Density

end WeightedContractionDecay

end WeightedContractionDecay

section SiegelHeightWeights

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField
open AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.SiegelVolume NumberField.AdelicLevel
open SiegelContraction WeightedContractionDecay SiegelShifts
open scoped ENNReal

namespace SiegelHeightWeights

section RealLemmas

private theorem weight_bound {h c r e : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c) (hr : 1 ≤ r) (he : 0 ≤ e) (k : ℕ)
    (hk : h ≤ r ^ (k + 1) * c) : (1 + h) ^ e ≤ (1 + c) ^ e * (r ^ e) ^ (k + 1) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have h1 : 1 ≤ r ^ (k + 1) := one_le_pow₀ hr
  have h2 : 1 + h ≤ (1 + c) * r ^ (k + 1) := by nlinarith
  have hc1 : (0 : ℝ) ≤ 1 + c := by linarith
  calc (1 + h) ^ e ≤ ((1 + c) * r ^ (k + 1)) ^ e := Real.rpow_le_rpow (by linarith) h2 he
    _ = (1 + c) ^ e * (r ^ (k + 1)) ^ e := Real.mul_rpow hc1 (pow_nonneg hr0 _)
    _ = (1 + c) ^ e * (r ^ e) ^ (k + 1) := by
        rw [← Real.rpow_natCast r (k + 1), ← Real.rpow_mul hr0, mul_comm (((k + 1 : ℕ)) : ℝ) e,
          Real.rpow_mul_natCast hr0 e (k + 1)]

private theorem exists_ratio {θ : ℝ} (hθ1 : θ < 1) :
    ∃ n : ℕ, 4 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → ((n : ℝ) ^ 2) ^ ((m : ℝ) * θ) < ((n : ℝ) ^ 2 / 10) ^ m := by
  have hepos : (0 : ℝ) < 2 * (1 - θ) := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((11 : ℝ) ^ (2 * (1 - θ))⁻¹)
  refine ⟨n₀ + 4, by omega, fun m hm => ?_⟩
  have hn0 : (0 : ℝ) ≤ ((n₀ + 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < ((n₀ + 4 : ℕ) : ℝ) := by positivity
  have hlt : (11 : ℝ) ^ (2 * (1 - θ))⁻¹ < ((n₀ + 4 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h11 := Real.rpow_lt_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 11) _) hlt hepos
  rw [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 11) hepos.ne'] at h11
  have hkey : (((n₀ + 4 : ℕ) : ℝ) ^ 2) ^ θ * ((n₀ + 4 : ℕ) : ℝ) ^ (2 * (1 - θ)) = ((n₀ + 4 : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hn0 2 θ, ← Real.rpow_add hnpos,
      show ((2 : ℕ) : ℝ) * θ + 2 * (1 - θ) = (2 : ℝ) by push_cast; ring, Real.rpow_two]
  have hx0 : (0 : ℝ) < ((n₀ + 4 : ℕ) : ℝ) ^ 2 := by positivity
  have hstep : (((n₀ + 4 : ℕ) : ℝ) ^ 2) ^ θ * 10 < ((n₀ + 4 : ℕ) : ℝ) ^ 2 := by
    calc (((n₀ + 4 : ℕ) : ℝ) ^ 2) ^ θ * 10
        < (((n₀ + 4 : ℕ) : ℝ) ^ 2) ^ θ * ((n₀ + 4 : ℕ) : ℝ) ^ (2 * (1 - θ)) :=
          mul_lt_mul_of_pos_left (by linarith) (Real.rpow_pos_of_pos hx0 θ)
      _ = ((n₀ + 4 : ℕ) : ℝ) ^ 2 := hkey
  have hlt' : (((n₀ + 4 : ℕ) : ℝ) ^ 2) ^ θ < ((n₀ + 4 : ℕ) : ℝ) ^ 2 / 10 :=
    (lt_div_iff₀ (by norm_num)).2 hstep
  rw [mul_comm (m : ℝ) θ, Real.rpow_mul_natCast hx0.le θ m]
  exact pow_lt_pow_left₀ hlt' (Real.rpow_nonneg hx0.le θ) (by omega)

private theorem tsum_ofReal_mul_inv_pow_lt_top {A q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) {N : ℕ} (hqN : q < N) :
    ∑' k : ℕ, ENNReal.ofReal (A * q ^ (k + 1)) * (N : ℝ≥0∞)⁻¹ ^ k < ⊤ := by
  have hN : (0 : ℝ) < N := hq.trans_lt hqN
  have hAq : 0 ≤ A * q := mul_nonneg hA hq
  have hterm : ∀ k : ℕ, ENNReal.ofReal (A * q ^ (k + 1)) * (N : ℝ≥0∞)⁻¹ ^ k
      = ENNReal.ofReal (A * q) * (ENNReal.ofReal q * (N : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have hsplit : A * q ^ (k + 1) = A * q * q ^ k := by ring
    rw [hsplit, ENNReal.ofReal_mul hAq, ENNReal.ofReal_pow hq, mul_assoc, ← mul_pow]
  have hρ : ENNReal.ofReal q * (N : ℝ≥0∞)⁻¹ < 1 := by
    rw [← ENNReal.ofReal_natCast, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hN]
    exact ENNReal.ofReal_lt_one.2 ((div_lt_one hN).2 hqN)
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))

end RealLemmas

section Weights

variable {L : Type} [Field L] [NumberField L]

private noncomputable def placeWeight (θ : ℝ) (w : InfinitePlace L) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + localHeight (archComponent L w (glArch (𝓞 L) L g))) ^ ((w.mult : ℝ) * θ))

private theorem prod_placeWeight_contractionN_mul (θ : ℝ) {P : Finset (InfinitePlace L)} {w : InfinitePlace L}
    (hw : w ∉ P) {n : ℕ} (hn : n ≠ 0) (b : w.Completion) (g : AdelicGL2 (𝓞 L) L) :
    ∏ v ∈ P, placeWeight θ v (contractionN w n hn b * g) = ∏ v ∈ P, placeWeight θ v g :=
  Finset.prod_congr rfl fun v hv => by
    have hvw : v ≠ w := fun h => hw (by rw [← h]; exact hv)
    unfold placeWeight
    rw [localHeight_contractionN_mul_of_ne hvw]

variable [MeasurableSpace (AdelicGL2 (𝓞 L) L)] [BorelSpace (AdelicGL2 (𝓞 L) L)]

private theorem measurable_placeWeight (θ : ℝ) (w : InfinitePlace L) : Measurable (placeWeight θ w) :=
  (((continuous_localHeight_place w).measurable.const_add 1).pow_const ((w.mult : ℝ) * θ)).ennreal_ofReal

private theorem measurable_prod_placeWeight (θ : ℝ) (P : Finset (InfinitePlace L)) :
    Measurable fun g : AdelicGL2 (𝓞 L) L => ∏ v ∈ P, placeWeight θ v g :=
  Finset.measurable_prod P fun v _ => measurable_placeWeight θ v

private theorem withDensity_prod_placeWeight_lt_top (μ : Measure (AdelicGL2 (𝓞 L) L)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {c u d₁ : ℝ} (hc : 0 < c) (hu : u ≠ 0)
    (hd₁ : 0 < d₁) (d₂ : ℝ) (P : Finset (InfinitePlace L)) :
    μ.withDensity (fun g => ∏ v ∈ P, placeWeight θ v g) (centreCutSiegelSet L c u d₁ d₂) < ⊤ := by
  classical
  have hS : MeasurableSet (centreCutSiegelSet L c u d₁ d₂) := measurableSet_centreCutSiegelSet c u d₁ d₂
  obtain ⟨n, hn4, hrate⟩ := exists_ratio hθ1
  have hn0 : n ≠ 0 := by omega
  have hr : (1 : ℝ) < (n : ℝ) ^ 2 := by
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    nlinarith
  refine Finset.induction_on P ?_ ?_
  · rw [withDensity_apply _ hS]
    simp only [Finset.prod_empty]
    rw [setLIntegral_one]
    exact measure_centreCutSiegelSet_lt_top μ hc u hd₁ d₂
  · intro w P hw ih
    obtain ⟨B, hcard, hshort, hsepB⟩ := exists_shiftFamily w hu hn4
    have hB : B.Nonempty := by
      have hpos : (0 : ℝ) < B.card :=
        lt_of_lt_of_le (pow_pos (div_pos (zero_lt_one.trans hr) (by norm_num)) _) hcard
      exact Finset.card_pos.1 (by exact_mod_cast hpos)
    have he0 : (0 : ℝ) ≤ (w.mult : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ0
    have hφ : Measurable fun g : AdelicGL2 (𝓞 L) L => localHeight (archComponent L w (glArch (𝓞 L) L g)) :=
      (continuous_localHeight_place w).measurable
    have hSc : ∀ g ∈ centreCutSiegelSet L c u d₁ d₂, c ≤ localHeight (archComponent L w (glArch (𝓞 L) L g)) :=
      fun g hg => hg.2.1 w
    have hstep : μ.withDensity (fun g => ∏ v ∈ insert w P, placeWeight θ v g) (centreCutSiegelSet L c u d₁ d₂)
        = ∫⁻ g in centreCutSiegelSet L c u d₁ d₂, placeWeight θ w g
            ∂(μ.withDensity fun g => ∏ v ∈ P, placeWeight θ v g) := by
      rw [withDensity_apply _ hS, restrict_withDensity hS,
        lintegral_withDensity_eq_lintegral_mul _ (measurable_prod_placeWeight θ P) (measurable_placeWeight θ w)]
      refine lintegral_congr fun g => ?_
      simp only [Pi.mul_apply]
      rw [Finset.prod_insert hw, mul_comm]
    have hmain := setLIntegral_le_tsum_mul (μ.withDensity fun g => ∏ v ∈ P, placeWeight θ v g) hS hφ hc hr hSc hB
      (p := contractionN w n hn0)
      (fun b hb g hg hhigh =>
        ⟨contractionN_mul_mem w hn0 (hshort b hb) hg hhigh, localHeight_contractionN_mul w hn0 b g⟩)
      (fun b hb b' hb' hbb' g hg g' hg' _ _ => contractionN_mul_ne w hn0 (hsepB b hb b' hb' hbb') hg hg')
      (fun b _ T hT => withDensity_image_mul_left_eq μ (measurable_prod_placeWeight θ P)
        (fun g => prod_placeWeight_contractionN_mul θ hw hn0 b g) hT)
      (F := placeWeight θ w)
      (a := fun k => ENNReal.ofReal ((1 + c) ^ ((w.mult : ℝ) * θ) * (((n : ℝ) ^ 2) ^ ((w.mult : ℝ) * θ)) ^ (k + 1)))
      (fun k g hg => ENNReal.ofReal_le_ofReal
        (weight_bound (localHeight_pos _).le hc.le hr.le he0 k hg.2.2.le))
    have hc1 : (0 : ℝ) ≤ 1 + c := by linarith
    have hgeom := tsum_ofReal_mul_inv_pow_lt_top (Real.rpow_nonneg hc1 ((w.mult : ℝ) * θ))
      (Real.rpow_nonneg (zero_lt_one.trans hr).le ((w.mult : ℝ) * θ))
      ((hrate w.mult (InfinitePlace.mult_pos (w := w))).trans_le hcard)
    rw [hstep]
    exact hmain.trans_lt (ENNReal.mul_lt_top hgeom ih)

private theorem lintegral_prod_placeWeight_lt_top (μ : Measure (AdelicGL2 (𝓞 L) L)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {c u d₁ : ℝ} (hc : 0 < c) (hu : u ≠ 0)
    (hd₁ : 0 < d₁) (d₂ : ℝ) :
    ∫⁻ g in centreCutSiegelSet L c u d₁ d₂, ∏ w : InfinitePlace L, placeWeight θ w g ∂μ < ⊤ := by
  rw [← withDensity_apply _ (measurableSet_centreCutSiegelSet c u d₁ d₂)]
  exact withDensity_prod_placeWeight_lt_top μ hθ0 hθ1 hc hu hd₁ d₂ Finset.univ

end Weights

end SiegelHeightWeights

end SiegelHeightWeights

section SiegelTranslateIntegrability

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField
open AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.SiegelVolume NumberField.AdelicLevel
open SiegelHeightWeights
open scoped ENNReal

namespace SiegelTranslateIntegrability

variable {L : Type} [Field L] [NumberField L]

private noncomputable def weight (θ : ℝ) (g : AdelicGL2 (𝓞 L) L) : ℝ :=
  ∏ w : InfinitePlace L, (1 + localHeight (archComponent L w (glArch (𝓞 L) L g))) ^ ((w.mult : ℝ) * θ)

private theorem one_add_localHeight_nonneg (w : InfinitePlace L) (g : AdelicGL2 (𝓞 L) L) :
    0 ≤ 1 + localHeight (archComponent L w (glArch (𝓞 L) L g)) := by
  linarith [localHeight_pos (archComponent L w (glArch (𝓞 L) L g))]

private theorem weight_nonneg (θ : ℝ) (g : AdelicGL2 (𝓞 L) L) : 0 ≤ weight θ g := by
  unfold weight
  exact Finset.prod_nonneg fun w _ => Real.rpow_nonneg (one_add_localHeight_nonneg w g) _

private theorem ofReal_weight (θ : ℝ) (g : AdelicGL2 (𝓞 L) L) :
    ENNReal.ofReal (weight θ g) = ∏ w : InfinitePlace L, placeWeight θ w g := by
  unfold weight
  have hnn : ∀ w ∈ (Finset.univ : Finset (InfinitePlace L)),
      (0 : ℝ) ≤ (1 + localHeight (archComponent L w (glArch (𝓞 L) L g))) ^ ((w.mult : ℝ) * θ) :=
    fun w _ => Real.rpow_nonneg (one_add_localHeight_nonneg w g) _
  rw [ENNReal.ofReal_prod_of_nonneg hnn]
  rfl

private theorem continuous_weight {θ : ℝ} (hθ0 : 0 ≤ θ) : Continuous (weight (L := L) θ) := by
  show Continuous fun g : AdelicGL2 (𝓞 L) L =>
    ∏ w : InfinitePlace L, (1 + localHeight (archComponent L w (glArch (𝓞 L) L g))) ^ ((w.mult : ℝ) * θ)
  exact continuous_finsetProd Finset.univ fun w _ =>
    (continuous_const.add (continuous_localHeight_place w)).rpow_const fun _ =>
      Or.inr (mul_nonneg (Nat.cast_nonneg _) hθ0)

private theorem one_le_weight {θ : ℝ} (hθ0 : 0 ≤ θ) (g : AdelicGL2 (𝓞 L) L) : 1 ≤ weight θ g := by
  unfold weight
  calc (1 : ℝ) = ∏ _w : InfinitePlace L, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ w : InfinitePlace L,
          (1 + localHeight (archComponent L w (glArch (𝓞 L) L g))) ^ ((w.mult : ℝ) * θ) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ =>
          Real.one_le_rpow (by linarith [localHeight_pos (archComponent L w (glArch (𝓞 L) L g))])
            (mul_nonneg (Nat.cast_nonneg _) hθ0)

private theorem le_ceil_of_cast_le {n : ℕ} {C₃ X : ℝ} (hX : 0 ≤ X) (h : (n : ℝ) ≤ C₃ * X) : n ≤ ⌈max C₃ 0 * X⌉₊ := by
  have h' : (n : ℝ) ≤ max C₃ 0 * X := h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
  exact Nat.cast_le.1 (h'.trans (Nat.le_ceil _))

private theorem le_mul_weight_of_le_mul_ceil {θ : ℝ} (hθ0 : 0 ≤ θ) (g : AdelicGL2 (𝓞 L) L) {v C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (C₃ : ℝ) (h : v ≤ C₂ * (⌈max C₃ 0 * weight θ g⌉₊ : ℝ)) : v ≤ C₂ * (max C₃ 0 + 1) * weight θ g := by
  have hR : 0 ≤ max C₃ 0 * weight θ g := mul_nonneg (le_max_right _ _) (weight_nonneg θ g)
  have hceil := Nat.ceil_lt_add_one hR
  have hw := one_le_weight hθ0 g
  have h2 : (⌈max C₃ 0 * weight θ g⌉₊ : ℝ) ≤ (max C₃ 0 + 1) * weight θ g := by linarith
  calc v ≤ C₂ * (⌈max C₃ 0 * weight θ g⌉₊ : ℝ) := h
    _ ≤ C₂ * ((max C₃ 0 + 1) * weight θ g) := mul_le_mul_of_nonneg_left h2 hC₂
    _ = C₂ * (max C₃ 0 + 1) * weight θ g := (mul_assoc _ _ _).symm

private theorem exponent_nonneg : (0 : ℝ) ≤ ((Module.finrank ℚ L - 1 : ℕ) : ℝ) / (Module.finrank ℚ L : ℝ) := by
  positivity

private theorem exponent_lt_one : ((Module.finrank ℚ L - 1 : ℕ) : ℝ) / (Module.finrank ℚ L : ℝ) < 1 := by
  have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hd' : (0 : ℝ) < (Module.finrank ℚ L : ℝ) := by exact_mod_cast hd
  rw [div_lt_one hd']
  have h1 : Module.finrank ℚ L - 1 < Module.finrank ℚ L := Nat.sub_lt hd one_pos
  exact_mod_cast h1

variable [MeasurableSpace (AdelicGL2 (𝓞 L) L)] [BorelSpace (AdelicGL2 (𝓞 L) L)]

private theorem integrableOn_weight (μ : Measure (AdelicGL2 (𝓞 L) L)) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {c u d₁ : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hd₁ : 0 < d₁) (d₂ : ℝ) :
    IntegrableOn (weight θ) (centreCutSiegelSet L c u d₁ d₂) μ := by
  refine ⟨(continuous_weight hθ0).aestronglyMeasurable, ?_⟩
  have hae : 0 ≤ᵐ[μ.restrict (centreCutSiegelSet L c u d₁ d₂)] weight θ :=
    Filter.Eventually.of_forall fun g => weight_nonneg θ g
  rw [hasFiniteIntegral_iff_ofReal hae]
  calc ∫⁻ g in centreCutSiegelSet L c u d₁ d₂, ENNReal.ofReal (weight θ g) ∂μ
      = ∫⁻ g in centreCutSiegelSet L c u d₁ d₂, ∏ w : InfinitePlace L, placeWeight θ w g ∂μ :=
        lintegral_congr fun g => ofReal_weight θ g
    _ < ⊤ := lintegral_prod_placeWeight_lt_top μ hθ0 hθ1 hc hu hd₁ d₂

private theorem integrableOn_iUnion_image_mul_of_norm_le (μ : Measure (AdelicGL2 (𝓞 L) L)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {c u d₁ : ℝ} (hc : 0 < c) (hu : u ≠ 0)
    (hd₁ : 0 < d₁) (d₂ : ℝ) (tset : Finset (AdelicGL2 (𝓞 L) L)) {F : AdelicGL2 (𝓞 L) L → ℂ}
    (hF : StronglyMeasurable F) (C : ℝ)
    (hbound : ∀ y ∈ tset, ∀ s ∈ centreCutSiegelSet L c u d₁ d₂, ‖F (s * y)‖ ≤ C * weight θ s) :
    IntegrableOn F (⋃ y ∈ tset, (· * y) '' centreCutSiegelSet L c u d₁ d₂) μ := by
  rw [integrableOn_finset_iUnion]
  intro y hy
  have himg : (· * y) '' centreCutSiegelSet L c u d₁ d₂ = (· * y⁻¹) ⁻¹' centreCutSiegelSet L c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  haveI : (Measure.map (· * y⁻¹) μ).IsMulLeftInvariant := isMulLeftInvariant_map_mul_right _
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * y⁻¹) μ) :=
    Measure.IsFiniteMeasureOnCompacts.map _ (Homeomorph.mulRight y⁻¹)
  have hmaj := (integrableOn_weight (Measure.map (· * y⁻¹) μ) hθ0 hθ1 hc hu hd₁ d₂).const_mul C
  have hG : IntegrableOn (fun s => F (s * y)) (centreCutSiegelSet L c u d₁ d₂) (Measure.map (· * y⁻¹) μ) := by
    refine Integrable.mono' hmaj (hF.comp_measurable (measurable_mul_const y)).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem (measurableSet_centreCutSiegelSet c u d₁ d₂) fun s hs => hbound y hy s hs
  have h2 := (measurableEmbedding_mulRight y⁻¹).integrableOn_map_iff.1 hG
  have hfun : ((fun s => F (s * y)) ∘ fun g => g * y⁻¹) = F := by
    funext g
    show F (g * y⁻¹ * y) = F g
    rw [inv_mul_cancel_right]
  rwa [hfun] at h2

private theorem integrableOn_iUnion_image_mul_of_norm_le_abs_add_one (μ : Measure (AdelicGL2 (𝓞 L) L))
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {c d₁ : ℝ} (hc : 0 < c)
    (u : ℝ) (hd₁ : 0 < d₁) (d₂ : ℝ) (tset : Finset (AdelicGL2 (𝓞 L) L)) {F : AdelicGL2 (𝓞 L) L → ℂ}
    (hF : StronglyMeasurable F) (C : ℝ)
    (hbound : ∀ y ∈ tset, ∀ s ∈ centreCutSiegelSet L c (|u| + 1) d₁ d₂, ‖F (s * y)‖ ≤ C * weight θ s) :
    IntegrableOn F (⋃ y ∈ tset, (· * y) '' centreCutSiegelSet L c u d₁ d₂) μ := by
  have hu : |u| + 1 ≠ 0 := by positivity
  have hsq : u ^ 2 ≤ (|u| + 1) ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  refine (integrableOn_iUnion_image_mul_of_norm_le μ hθ0 hθ1 hc hu hd₁ d₂ tset hF C hbound).mono_set ?_
  exact Set.iUnion₂_mono fun y _ => Set.image_mono (centreCutSiegelSet_mono_window hsq)

end SiegelTranslateIntegrability

end SiegelTranslateIntegrability

section Helpers

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight

namespace BorelCentralAssembly

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

private theorem ideleNorm_map_algebraMap (η : Lˣ) :
    NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1 := by
  have hpos : 0 < NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η))
      = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η *
          Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η := by
    apply Units.ext
    show Matrix.det (Matrix.scalar (Fin 2)
        ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L)))
      = (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L) *
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L)
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  have h1 : NumberField.TateGlobal.ideleNorm L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) *
      NumberField.TateGlobal.ideleNorm L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1 := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, ← hdet, CentralEllipticShell.centralScalar_map_algebraMap L η,
      AutomorphicForm.ideleNorm_det_globalPoints]
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · exact h
  · rw [h] at hpos
    norm_num at hpos

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem finsum_mem_eq_zero_of_notMem_shell (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) {a b : ℝ}
    (hsupp : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b)
    (T : Set (GL (Fin 2) L)) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (hz : z ∉ {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)}) :
    ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0 := by
  refine finsum_mem_of_eqOn_zero fun δ _ => ?_
  show φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0
  by_contra hne
  obtain ⟨g, hg, hgeq⟩ := CentralEllipticShell.ideleNorm_sq_mem_of_ne_zero K L D σ φ x z δ hne
  have h2 : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b := by
    rw [← hgeq]
    exact hsupp g hg
  exact hz (ShellVolume.mem_shell_of_mul_self_mem L z h2)

end BorelCentralAssembly

end Helpers

open AutomorphicForm in
open NumberField.AdelicHeight in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) (tset : Finset (AdelicGL2 (𝓞 L) L)) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (ns : HeightOneSpectrum (𝓞 K) → ℕ)
      (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
      (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
      (φ : AdelicGL2 (𝓞 L) L → ℂ)
      (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL))
        (⋃ y ∈ tset, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
        (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  intro T ws ns rTs zs ks js φ φf hfact
  have hobt1 :=
    KernelSplitting.continuous_and_hasCompactSupport_of_isSemiLocalFactorization K L _ hfact
  obtain ⟨hφc, hφs⟩ := hobt1
  have hfin : AutomorphicForm.AdelicKernelLocalFiniteness L := AutomorphicForm.adelicKernelLocalFiniteness L

  have hobt2 := ShellVolume.exists_forall_ideleNorm_det_mem_Icc L φ hφs
  obtain ⟨a, b, ha, hab, hsupp⟩ := hobt2
  have hZm : MeasurableSet {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} :=
    ShellVolume.measurableSet_shell L _ _
  have hobt3 :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      L νZL
  obtain ⟨Dm, _, hDm, htemp⟩ := hobt3
  have hobt4 := htemp 0
  obtain ⟨k, hk⟩ := hobt4
  have hvol : νZL ({z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} ∩ ΩL) < ⊤ :=
    ShellVolume.measure_shell_inter_lt_top L νZL (BorelCentralAssembly.ideleNorm_map_algebraMap L) ΩL hΩL
      Dm hDm ha hab k hk
  have hobt5 := KernelFoldBounds.exists_isCompact_forall_mem_shell_exists_eq_mul L
    (NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L)
    (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L)
    (a := ⟨Real.sqrt a, Real.sqrt_nonneg a⟩) (b := ⟨Real.sqrt b, Real.sqrt_nonneg b⟩)
    (by rw [← NNReal.coe_pos]; exact Real.sqrt_pos.mpr ha)
  obtain ⟨W, hW, hrepW⟩ := hobt5
  have hrep : ∀ z ∈ {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)}, ∃ η : Lˣ, ∃ w ∈ W,
        z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w :=
    fun z hz => hrepW z hz
  have hZ := BorelCentralAssembly.finsum_mem_eq_zero_of_notMem_shell K L D σ φ hsupp
  have hper : ∀ T' : Set (GL (Fin 2) L),
      (∀ δ ∈ T', ∀ c : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ T') →
      ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
        ∑ᶠ δ ∈ T', φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
            (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
        = ∑ᶠ δ ∈ T', φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) :=
    fun T' hT' x ζ z => CentralEllipticShell.finsum_mem_centralScalar_map_mul K L D σ φ T' hT' x ζ z

  have hTce : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∀ c : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈
        {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} :=
    fun δ hδ c => CellScalarStability.mul_scalar_mem_centralElliptic hgen hδ c
  have hTb : ∀ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∀ c : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈
        {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} :=
    fun δ hδ c => OffBorelFold.mem_borel_mul_scalar
      (Q := (fun δ : GL (Fin 2) L => ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ))
      (fun δ h c => hTce δ h c) hδ c

  refine ⟨fun x => KernelFoldBounds.integrableOn_mul_finsum_mem K L D σ νZL ΩL hfin φ hφc hφs _ ξL hξc hξt _
    hZm hvol hW hrep (hZ _) (hper _ hTb) x, ?_⟩

  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := IdeleTopology.secondCountableTopology_units_adeleRing L
  haveI : SigmaFinite νZL := inferInstance

  have hθ0 : (0 : ℝ) ≤ ((Module.finrank ℚ L - 1 : ℕ) : ℝ) / (Module.finrank ℚ L : ℝ) :=
    SiegelTranslateIntegrability.exponent_nonneg
  have hθ1 : ((Module.finrank ℚ L - 1 : ℕ) : ℝ) / (Module.finrank ℚ L : ℝ) < 1 :=
    SiegelTranslateIntegrability.exponent_lt_one

  have hset := BorelNormClasses.setOf_upper_ellipticOrCentral_eq_setOf_upper_central hgen

  have hobtC₂ := KernelCountReduction.exists_forall_norm_setIntegral_le_mul_of_ncard_le K L D σ hfin φ hφc hφs
    {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
    (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
    LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
    ξL hξc hξt νZL ΩL hZm hvol hW hrep (hZ _) (hper _ hTb)
  obtain ⟨C₂, hC₂0, hC₂⟩ := hobtC₂

  have hobtC₃ := SiegelPointCount.exists_forall_ncard_le_mul_prod K L D hgen φ hφs tset hW hc hd₁ (u := |u| + 1)
    (d₂ := d₂)
  obtain ⟨C₃, hC₃⟩ := hobtC₃

  have hF : StronglyMeasurable
      (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)) :=
    OffBorelFold.stronglyMeasurable_setIntegral_curried L νZL ΩL
      (fun (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
      (OffBorelFold.continuous_mul_comp₂ hξc
        (fun (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
          ∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * w))
        (KernelFoldBounds.continuous_finsum_mem L hfin φ hφc hφs
          {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
        (fun (z : (AdeleRing (𝓞 L) L)ˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        (KernelFoldBounds.continuous_sigmaAdelicAct_centralScalar_mul K L D σ))

  exact SiegelTranslateIntegrability.integrableOn_iUnion_image_mul_of_norm_le_abs_add_one
    (adelicGLHaar (Fin 2) (𝓞 L) L) hθ0 hθ1 hc u hd₁ d₂ tset hF _ fun y hy s hs =>
      SiegelTranslateIntegrability.le_mul_weight_of_le_mul_ceil hθ0 s hC₂0 C₃ (hC₂ (s * y) _ fun w hw => by
        rw [hset]
        exact SiegelTranslateIntegrability.le_ceil_of_cast_le (SiegelTranslateIntegrability.weight_nonneg _ s)
          (hC₃ y hy s hs w hw))

#print axioms solution

end S_AutomorphicForm_integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic (solution)
