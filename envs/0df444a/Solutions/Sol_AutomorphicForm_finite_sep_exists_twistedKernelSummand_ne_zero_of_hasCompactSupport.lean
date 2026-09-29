-- Prove2me | solution 1 for AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/01f9bb96-0f04-5805-b0f5-367ec01709cd

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
import Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R3Fin

open LT.TwistedNorm LT.TwistedNorm.GL2

section GroupLemmas

variable {G : Type*} [Group G]

theorem sigmaPartialNorm_mul_of_central (σ : G →* G) (a c : G) (hc : ∀ g : G, c * g = g * c) (r : ℕ) :
    sigmaPartialNorm σ (a * c) r = sigmaPartialNorm σ a r * sigmaPartialNorm σ c r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul,
        mul_assoc a c, ← mul_assoc c, hc (σ _)]
      simp only [mul_assoc]

theorem continuous_sigmaPartialNorm [TopologicalSpace G] [ContinuousMul G] (σ : G →* G)
    (hσ : Continuous σ) (r : ℕ) : Continuous fun x => sigmaPartialNorm σ x r := by
  induction r with
  | zero =>
      simp only [sigmaPartialNorm_zero]
      exact continuous_const
  | succ r ih =>
      simp only [sigmaPartialNorm_succ']
      exact continuous_id.mul (hσ.comp ih)

end GroupLemmas

section Family

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

abbrev sc : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev σG (σ : L ≃ₐ[F] L) : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem sc_comm (u : Lˣ) (g : GL (Fin 2) L) : sc u * g = g * sc u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : L) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) L)).eq

theorem mul_sc (g : GL (Fin 2) L) (u : Lˣ) : g * sc u = sc u * g := (sc_comm u g).symm

theorem mul_sc_left (g k : GL (Fin 2) L) (u : Lˣ) : g * (sc u * k) = sc u * (g * k) := by
  rw [← mul_assoc, mul_sc, mul_assoc]

theorem σG_sc (σ : L ≃ₐ[F] L) (u : Lˣ) : σG σ (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change σ ((Matrix.scalar (Fin 2) (u : L)) i j) = Matrix.scalar (Fin 2) (σ (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem family_sigmaConj (σ : L ≃ₐ[F] L) {δ₀ δ δ' : GL (Fin 2) L}
    (hδ : ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = sc u * (h⁻¹ * δ₀ * σG σ h))
    {k : GL (Fin 2) L} (hδ' : δ' = k⁻¹ * δ * σG σ k) :
    ∃ (h : GL (Fin 2) L) (u : Lˣ), δ' = sc u * (h⁻¹ * δ₀ * σG σ h) := by
  obtain ⟨h, u, rfl⟩ := hδ
  refine ⟨h * k, u, ?_⟩
  rw [hδ', map_mul, mul_inv_rev]
  simp only [mul_assoc, mul_sc_left]

theorem sigmaPartialNorm_sc_mul (σ : L ≃ₐ[F] L) (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (σG σ) (sc u * δ) r =
      sc (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) u r) * sigmaPartialNorm (σG σ) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_mul,
        σG_sc]
      rw [mul_assoc (sc u), ← mul_assoc δ, ← sc_comm _ δ]
      simp only [mul_assoc]

theorem trace_smul_one_fin_two (c : F) : (c • (1 : Matrix (Fin 2) (Fin 2) F)).trace = 2 * c := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

theorem det_smul_one_fin_two (c : F) : (c • (1 : Matrix (Fin 2) (Fin 2) F)).det = c ^ 2 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

theorem isRoot_charpoly_of_trace_eq_of_det_eq (M : Matrix (Fin 2) (Fin 2) F) (c : F) (htr : M.trace = 2 * c)
    (hdet : M.det = c ^ 2) : M.charpoly.IsRoot c := by
  rw [Matrix.charpoly_fin_two]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, htr, hdet]
  ring

theorem ne_smul_one_of_mem_ellipticCell {γ : GL (Fin 2) F} (hγ : γ ∈ AutomorphicForm.ellipticCell F) (c : F) :
    (γ : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have hγ' : AutomorphicForm.IsEllipticType (γ : Matrix (Fin 2) (Fin 2) F) := hγ
  refine hγ' c ?_
  rw [h]
  exact isRoot_charpoly_of_trace_eq_of_det_eq _ c (trace_smul_one_fin_two c) (det_smul_one_fin_two c)

theorem not_mem_ellipticCell_of_trace_eq_of_det_eq {γ γ' : GL (Fin 2) F}
    (hγ : γ ∈ AutomorphicForm.centralCell F)
    (htr : (γ : Matrix (Fin 2) (Fin 2) F).trace = (γ' : Matrix (Fin 2) (Fin 2) F).trace)
    (hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = (γ' : Matrix (Fin 2) (Fin 2) F).det) :
    γ' ∉ AutomorphicForm.ellipticCell F := by
  obtain ⟨c, hc⟩ := hγ
  intro hγ'
  have h' : AutomorphicForm.IsEllipticType (γ' : Matrix (Fin 2) (Fin 2) F) := hγ'
  refine h' c (isRoot_charpoly_of_trace_eq_of_det_eq _ c ?_ ?_)
  · rw [← htr, hc, trace_smul_one_fin_two]
  · rw [← hdet, hc, det_smul_one_fin_two]

theorem eq_of_mem_centralCell_of_trace_eq_of_det_eq {γ γ' : GL (Fin 2) F}
    (hγ : γ ∈ AutomorphicForm.centralCell F) (hγ' : γ' ∈ AutomorphicForm.centralCell F)
    (htr : (γ : Matrix (Fin 2) (Fin 2) F).trace = (γ' : Matrix (Fin 2) (Fin 2) F).trace)
    (hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = (γ' : Matrix (Fin 2) (Fin 2) F).det) : γ = γ' := by
  obtain ⟨c, hc⟩ := hγ
  obtain ⟨c', hc'⟩ := hγ'
  rw [hc, hc', trace_smul_one_fin_two, trace_smul_one_fin_two] at htr
  rw [hc, hc', det_smul_one_fin_two, det_smul_one_fin_two] at hdet
  have hsq : (c - c') ^ 2 = 0 := by linear_combination c * htr - hdet
  have hcc : c = c' := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  apply Units.ext
  rw [hc, hc', hcc]

theorem scalar_mul_mem_cells {γ : GL (Fin 2) F} (a : Fˣ)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.ellipticCell F ∨
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.centralCell F := by
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a : F) • (γ : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul]
    change Matrix.scalar (Fin 2) (a : F) * _ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rcases hγ with hγ | hγ
  · left
    rw [AutomorphicForm.mem_ellipticCell_iff, AutomorphicForm.IsEllipticType, hcoe]
    intro b hb
    apply hγ (b / a)
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hb ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at hb ⊢
    have ha : (a : F) ≠ 0 := a.ne_zero
    field_simp
    linear_combination hb
  · right
    obtain ⟨c, hc⟩ := AutomorphicForm.mem_centralCell_iff.mp hγ
    refine AutomorphicForm.mem_centralCell_iff.mpr ⟨a * c, ?_⟩
    rw [hcoe, hc, smul_smul]

theorem algebraMap_trace_eq_trace_of_conj_eq_map {N : GL (Fin 2) L} {γ : GL (Fin 2) F} {P : GL (Fin 2) L}
    (hγ : P⁻¹ * N * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ) :
    algebraMap F L (γ : Matrix (Fin 2) (Fin 2) F).trace = (N : Matrix (Fin 2) (Fin 2) L).trace := by
  have h := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L).trace) hγ
  simp only [Units.val_mul, Matrix.trace_units_conj'] at h
  rw [h]
  exact AddMonoidHom.map_trace (algebraMap F L : F →+* L) (γ : Matrix (Fin 2) (Fin 2) F)

variable [FiniteDimensional F L] [IsGalois F L]

theorem isNormRep_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (hN : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hN
  obtain ⟨Q, hQ⟩ := hN
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
  rw [← hQ, map_mul, map_mul, map_inv, ← hP]
  group

theorem coe_sc_norm (σ : L ≃ₐ[F] L) (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    ((sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F (u : L)) • (1 : Matrix (Fin 2) (Fin 2) L) := by
  rw [← coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  ext i j
  change Matrix.scalar (Fin 2) _ i j = _
  rw [Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

def normUnit (u : Lˣ) : Fˣ :=
  Units.mk0 (Algebra.norm F (u : L)) (Algebra.norm_ne_zero_iff.mpr u.ne_zero)

@[scoped simp] theorem coe_normUnit (u : Lˣ) : ((normUnit (F := F) u : Fˣ) : F) = Algebra.norm F (u : L) := rfl

theorem isNormRep_sc_mul {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (u : Lˣ) :
    IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (normUnit (F := F) u) * γ) (sc u * δ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_def, sigmaPartialNorm_sc_mul, ← sigmaNormPow_def, ← sigmaNormPow_def, map_mul]
  have hnorm : P⁻¹ * (sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) *
      sigmaNormPow (σG σ) (Module.finrank F L) δ) * P =
      sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) *
        (P⁻¹ * sigmaNormPow (σG σ) (Module.finrank F L) δ * P) := by
    simp only [mul_assoc, mul_sc_left]
  rw [hnorm]
  erw [hP]
  congr 1
  apply Units.ext
  rw [coe_sc_norm σ hgen u]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change _ = algebraMap F L (Matrix.scalar (Fin 2) _ i j)
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sc_mul_mem_I {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (u : Lˣ) :
    ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ)) = ConjClasses.mk γ := by
  obtain ⟨γ, hγ, hN⟩ := hδ
  refine ⟨_, scalar_mul_mem_cells (normUnit (F := F) u) hγ, ?_⟩
  exact normClassMap_mk_eq_of_isNormRep hgen (isNormRep_sc_mul hgen (isNormRep_of_normClassMap_mk_eq hgen hN) u)

theorem mem_I_of_mem_family {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ₀ δ : GL (Fin 2) L}
    (hδ₀ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk γ)
    (hδ : ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = sc u * (h⁻¹ * δ₀ * σG σ h)) :
    ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ := by
  obtain ⟨h, u, rfl⟩ := hδ
  apply sc_mul_mem_I hgen
  have hmk : SigmaConjClasses.mk σ (h⁻¹ * δ₀ * σG σ h) = SigmaConjClasses.mk σ δ₀ :=
    (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm
  rwa [hmk]

theorem mk_eq_mk_of_trace_eq_of_det_eq [Infinite F] {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ δ' : GL (Fin 2) L}
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ)
    (hδ' : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ') = ConjClasses.mk γ)
    (htr : ((sigmaNormPow (σG σ) (Module.finrank F L) δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace =
      ((sigmaNormPow (σG σ) (Module.finrank F L) δ' : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace)
    (hdet : ((sigmaNormPow (σG σ) (Module.finrank F L) δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det =
      ((sigmaNormPow (σG σ) (Module.finrank F L) δ' : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det) :
    SigmaConjClasses.mk σ δ = SigmaConjClasses.mk σ δ' := by
  obtain ⟨γ, hγc, hγ⟩ := hδ
  obtain ⟨γ', hγc', hγ'⟩ := hδ'
  obtain ⟨P, hP⟩ := isNormRep_of_normClassMap_mk_eq hgen hγ
  obtain ⟨P', hP'⟩ := isNormRep_of_normClassMap_mk_eq hgen hγ'
  have htr' : (γ : Matrix (Fin 2) (Fin 2) F).trace = (γ' : Matrix (Fin 2) (Fin 2) F).trace :=
    (algebraMap F L).injective (by
      rw [algebraMap_trace_eq_trace_of_conj_eq_map hP, algebraMap_trace_eq_trace_of_conj_eq_map hP', htr])
  have hdet' : (γ : Matrix (Fin 2) (Fin 2) F).det = (γ' : Matrix (Fin 2) (Fin 2) F).det :=
    (algebraMap F L).injective (by
      rw [algebraMap_det_eq_det_of_conj_eq_map hP, algebraMap_det_eq_det_of_conj_eq_map hP', hdet])
  rcases hγc with he | hc
  · rcases hγc' with he' | hc'
    · obtain ⟨Q, hQ⟩ := exists_conj_of_trace_eq_det_eq γ γ' (ne_smul_one_of_mem_ellipticCell he)
        (ne_smul_one_of_mem_ellipticCell he') htr' hdet'
      have hcl : ConjClasses.mk γ' = ConjClasses.mk γ :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨Q, by rw [hQ]; group⟩)
      rw [hcl] at hγ'
      exact sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell hgen γ he δ δ' hγ hγ'
    · exact absurd he (not_mem_ellipticCell_of_trace_eq_of_det_eq hc' htr'.symm hdet'.symm)
  · rcases hγc' with he' | hc'
    · exact absurd he' (not_mem_ellipticCell_of_trace_eq_of_det_eq hc htr' hdet')
    · have hγγ : γ = γ' := eq_of_mem_centralCell_of_trace_eq_of_det_eq hc hc' htr' hdet'
      subst hγγ
      exact sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell hgen γ hc δ δ' hγ hγ'

end Family

section Modulus

open MeasureTheory NumberField
open scoped Pointwise ENNReal NNReal

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      NumberField.TateGlobal.ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance

  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne

  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b

  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl

  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    exact θ.apply_symm_apply _

  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1

  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    beta_reduce at this
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

end Modulus

section Adelic

open NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * y = y * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * AutomorphicForm.centralScalar (𝓞 L) L w = AutomorphicForm.centralScalar (𝓞 L) L w * g :=
  (centralScalar_comm L w g).symm

theorem mul_cs_left (g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (AutomorphicForm.centralScalar (𝓞 L) L w * y) = AutomorphicForm.centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, mul_cs, mul_assoc]

theorem globalPoints_sc (u : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (sc u) = AutomorphicForm.centralScalar (𝓞 L) L (princ L u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (u : L) i j) =
    Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaAdelicAct_centralScalar_princ (u : Lˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L (princ L u)) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L (Units.map ((σ : L →+* L) : L →* L) u)) := by
  rw [← globalPoints_sc, ← globalPoints_sc]
  have h := AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ (sc u)
  have h2 : Matrix.GeneralLinearGroup.map (σ : L →+* L) (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) :=
    σG_sc σ u
  rw [h2] at h
  exact h

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simpa [Matrix.scalar_apply] using continuous_id'
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem continuous_actU : Continuous (actU K L D σ) :=
  Continuous.units_map _ (D.continuous_act σ)

theorem det_sigmaAdelicAct (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.sigmaAdelicAct K L D σ y) =
      actU K L D σ (Matrix.GeneralLinearGroup.det y) :=
  Matrix.GeneralLinearGroup.map_det _ y

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem iterate_sigmaAdelicAct (r : ℕ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (AutomorphicForm.sigmaAdelicAct K L D σ)^[r] g = AutomorphicForm.sigmaAdelicAct K L D (σ ^ r) g := by
  induction r with
  | zero => rw [Function.iterate_zero, pow_zero, AutomorphicForm.sigmaAdelicAct_one]; rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', AutomorphicForm.sigmaAdelicAct_mul]; rfl

variable [FiniteDimensional K L] [IsGalois K L]

theorem iterate_sigmaAdelicAct_finrank (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (AutomorphicForm.sigmaAdelicAct K L D σ)^[Module.finrank K L] g = g := by
  have horder : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  rw [iterate_sigmaAdelicAct, ← horder, pow_orderOf_eq_one, AutomorphicForm.sigmaAdelicAct_one]
  rfl

theorem sigmaNormPow_adelic_sigmaConj (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x m : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L)
        (x⁻¹ * m * AutomorphicForm.sigmaAdelicAct K L D σ x) =
      x⁻¹ * sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L) m * x :=
  sigmaNormPow_sigmaConjElt _ _ (iterate_sigmaAdelicAct_finrank K L D σ hgen x) m

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_globalPoints (n : ℕ) (δ : GL (Fin 2) L) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.globalPoints (𝓞 L) L δ) =
      AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) n δ) :=
  (hom_sigmaNormPow (σG σ) (AutomorphicForm.sigmaAdelicAct K L D σ) (AutomorphicForm.globalPoints (𝓞 L) L)
    (fun g => (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g).symm) n δ).symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_centralScalar (n : ℕ) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.centralScalar (𝓞 L) L w) =
      AutomorphicForm.centralScalar (𝓞 L) L (sigmaNormPow (actU K L D σ) n w) :=
  (hom_sigmaNormPow (actU K L D σ) (AutomorphicForm.sigmaAdelicAct K L D σ)
    (AutomorphicForm.centralScalar (𝓞 L) L) (fun w => (sigmaAdelicAct_centralScalar K L D σ w).symm) n w).symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_mul_centralScalar (n : ℕ) (m : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (m * AutomorphicForm.centralScalar (𝓞 L) L w) =
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n m *
        sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.centralScalar (𝓞 L) L w) :=
  sigmaPartialNorm_mul_of_central _ m _ (centralScalar_comm L w) n

omit [FiniteDimensional K L] [IsGalois K L] in
theorem continuous_sigmaNormPow_adelic (n : ℕ) :
    Continuous fun s : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n s :=
  continuous_sigmaPartialNorm _ (AutomorphicForm.continuous_sigmaAdelicAct K L D σ) n

theorem normalizedNorm_kernelArg (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ₁ : GL (Fin 2) L) (κ : (AdeleRing (𝓞 L) L)ˣ) :
    (sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L)
        (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ)))⁻¹ *
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L)
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₁ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ * x)) =
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) (Module.finrank K L) δ₁) * x := by
  set n := Module.finrank K L
  rw [sigmaAdelicAct_centralScalar]
  have harg : x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₁ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ * x) =
      x⁻¹ * (AutomorphicForm.globalPoints (𝓞 L) L δ₁ *
        AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ κ)) * AutomorphicForm.sigmaAdelicAct K L D σ x := by
    rw [map_mul, sigmaAdelicAct_centralScalar]
    simp only [mul_assoc]
  rw [harg, sigmaNormPow_adelic_sigmaConj K L D σ hgen, sigmaNormPow_adelic_mul_centralScalar,
    sigmaNormPow_adelic_globalPoints, sigmaNormPow_adelic_centralScalar]
  set c := AutomorphicForm.centralScalar (𝓞 L) L (sigmaNormPow (actU K L D σ) n (actU K L D σ κ))
  set A := AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) n δ₁)
  calc c⁻¹ * (x⁻¹ * (A * c) * x) = c⁻¹ * (c * (x⁻¹ * A * x)) := by
        simp only [c, mul_assoc, mul_cs_left, mul_cs]
    _ = x⁻¹ * A * x := inv_mul_cancel_left _ _

omit [FiniteDimensional K L] [IsGalois K L] in
theorem trace_val_globalPoints (γ : GL (Fin 2) L) :
    Matrix.trace ((AutomorphicForm.globalPoints (𝓞 L) L γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      algebraMap L (AdeleRing (𝓞 L) L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) L)) :=
  (AddMonoidHom.map_trace (algebraMap L (AdeleRing (𝓞 L) L)) (γ : Matrix (Fin 2) (Fin 2) L)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
theorem det_val_globalPoints (γ : GL (Fin 2) L) :
    Matrix.det ((AutomorphicForm.globalPoints (𝓞 L) L γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      algebraMap L (AdeleRing (𝓞 L) L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) L)) :=
  ((algebraMap L (AdeleRing (𝓞 L) L)).map_det (γ : Matrix (Fin 2) (Fin 2) L)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
theorem trace_val_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.trace ((x⁻¹ * g * x : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem det_val_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.det ((x⁻¹ * g * x : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))

omit [FiniteDimensional K L] [IsGalois K L] in
theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := L) 1).ne' (h.symm.trans (mul_one _).symm)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem ideleNorm_inv (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem ideleNorm_det_kernelArg (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) =
      NumberField.TateGlobal.ideleNorm L z ^ 2 := by
  rw [map_mul, map_mul, map_inv, det_sigmaAdelicAct, map_mul, det_centralScalar, map_mul, map_pow,
    NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, AutomorphicForm.ideleNorm_det_globalPoints,
    pow_two, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_unitsMap_act, ideleNorm_unitsMap_act, mul_one,
    ← pow_two]
  have hx : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos (F := L) _).ne'
  field_simp

omit [FiniteDimensional K L] [IsGalois K L] in

theorem kernelArg_princ_mul (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ₀ : GL (Fin 2) L) (a : Lˣ)
    (κ : (AdeleRing (𝓞 L) L)ˣ) :
    x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L (princ L a * κ) * x) =
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (sc (Units.map ((σ : L →+* L) : L →* L) a) * δ₀) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ * x) := by
  rw [map_mul (AutomorphicForm.centralScalar (𝓞 L) L), mul_assoc (AutomorphicForm.centralScalar (𝓞 L) L _),
    map_mul (AutomorphicForm.sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar_princ, ← globalPoints_sc,
    sc_comm, map_mul (AutomorphicForm.globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

end Adelic

section Lift

open NumberField
open scoped NNReal Pointwise

variable (L : Type) [Field L] [NumberField L]

theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Lˣ) (c : (AdeleRing (𝓞 L) L)ˣ), c ∈ C ∧ z = princ L a * c := by
  have hC :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  obtain ⟨C₁, hC₁c, -, hC₁⟩ := hC
  have hs := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
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
  have hzpos : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos (F := L) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨NumberField.TateGlobal.ideleNorm L z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : NumberField.TateGlobal.ideleNorm L (s r) = NumberField.TateGlobal.ideleNorm L z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, hsr,
      mul_inv_cancel₀ hzpos.ne']
  have hκ' := hC₁ _ hz₁
  obtain ⟨η, κ, hκ, hzκ⟩ := hκ'
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

end Lift

section Main

open NumberField

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (R : Set (GL (Fin 2) L))
    (hRsub : R ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (hR : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) :
    {δ₀ ∈ R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite := by
  classical
  set n := Module.finrank K L with hn
  have hSc : IsCompact (tsupport φ) := hφc

  obtain ⟨m₀, hm₀, hlo⟩ : ∃ m₀ > 0, ∀ g ∈ tsupport φ,
      m₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
    by_cases hne : (tsupport φ).Nonempty
    · obtain ⟨g₀, -, hmin⟩ :=
        hSc.exists_isMinOn hne (NumberField.TateGlobal.continuous_ideleNorm_det L).continuousOn
      exact ⟨_, NumberField.TateGlobal.ideleNorm_pos (F := L) _, fun g hg => hmin hg⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun g hg => by rw [hne] at hg; exact absurd hg (Set.notMem_empty g)⟩
  obtain ⟨M₀, hhi⟩ : ∃ M₀, ∀ g ∈ tsupport φ,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤ M₀ := by
    obtain ⟨M, hM⟩ := (hSc.image (NumberField.TateGlobal.continuous_ideleNorm_det L)).bddAbove
    exact ⟨M, fun g hg => hM ⟨g, hg, rfl⟩⟩
  have hm₁pos : 0 < Real.sqrt m₀ := Real.sqrt_pos.mpr hm₀

  obtain ⟨C₁, hC₁c, hlift⟩ := exists_isCompact_forall_mem_exists_princ_mul L (M₁ := Real.sqrt M₀) hm₁pos

  set Ψ : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L → AutomorphicForm.AdelicGL2 (𝓞 L) L :=
    fun p => (sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n
        (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.1)))⁻¹ *
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n p.2 with hΨ
  have hNc := continuous_sigmaNormPow_adelic K L D σ n
  have hΨc : Continuous Ψ :=
    ((hNc.comp ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      ((continuous_centralScalar L).comp continuous_fst))).inv).mul (hNc.comp continuous_snd)
  have hΨv : Continuous fun p : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ((Ψ p : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    Units.continuous_val.comp hΨc
  set Tset : Set (AdeleRing (𝓞 L) L) :=
    (fun p : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      Matrix.trace ((Ψ p : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))) ''
      (C₁ ×ˢ tsupport φ) with hTset
  set Dset : Set (AdeleRing (𝓞 L) L) :=
    (fun p : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      Matrix.det ((Ψ p : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))) ''
      (C₁ ×ˢ tsupport φ) with hDset
  have hTc : IsCompact Tset := (hC₁c.prod hSc).image hΨv.matrix_trace
  have hDc : IsCompact Dset := (hC₁c.prod hSc).image hΨv.matrix_det
  have hT₀ := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hTc
  have hD₀ := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hDc

  set Γ : Set (GL (Fin 2) L) := {δ₁ | ∃ x : AutomorphicForm.AdelicGL2 (𝓞 L) L, ∃ κ ∈ C₁,
    x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₁ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ * x) ∈ tsupport φ}
    with hΓ

  have hinv : ∀ δ₁ ∈ Γ,
      Matrix.trace ((sigmaNormPow (σG σ) n δ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ∈
        {ξ : L | algebraMap L (AdeleRing (𝓞 L) L) ξ ∈ Tset} ∧
      Matrix.det ((sigmaNormPow (σG σ) n δ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ∈
        {ξ : L | algebraMap L (AdeleRing (𝓞 L) L) ξ ∈ Dset} := by
    rintro δ₁ ⟨x, κ, hκ, hmem⟩
    have key : Ψ (κ, x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₁ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L κ * x)) =
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) n δ₁) * x :=
      normalizedNorm_kernelArg K L D σ hgen x δ₁ κ
    constructor
    · refine ⟨(κ, _), ⟨hκ, hmem⟩, ?_⟩
      show Matrix.trace ((Ψ (κ, _) : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = _
      rw [key, trace_val_conj, trace_val_globalPoints]
    · refine ⟨(κ, _), ⟨hκ, hmem⟩, ?_⟩
      show Matrix.det ((Ψ (κ, _) : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = _
      rw [key, det_val_conj, det_val_globalPoints]

  set Rc : Set (GL (Fin 2) L) := {δ₀ | δ₀ ∈ R ∧ ∃ δ₁ ∈ Γ, ∃ (h : GL (Fin 2) L) (u : Lˣ),
    δ₁ = sc u * (h⁻¹ * δ₀ * σG σ h)} with hRc
  have hRc_fin : Rc.Finite := by
    have hwit : ∀ δ₀ ∈ Rc, ∃ δ₁, δ₁ ∈ Γ ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ), δ₁ = sc u * (h⁻¹ * δ₀ * σG σ h) :=
      fun δ₀ h => h.2
    choose! wit hwitΓ hwitfam using hwit
    refine Set.Finite.of_finite_image (f := fun δ₀ =>
      (Matrix.trace ((sigmaNormPow (σG σ) n (wit δ₀) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L),
        Matrix.det ((sigmaNormPow (σG σ) n (wit δ₀) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))) ?_ ?_
    · refine (hT₀.prod hD₀).subset ?_
      rintro _ ⟨δ₀, hδ₀, rfl⟩
      exact ⟨(hinv _ (hwitΓ δ₀ hδ₀)).1, (hinv _ (hwitΓ δ₀ hδ₀)).2⟩
    · intro δ₀ hδ₀ δ₀' hδ₀' heq
      simp only [Prod.mk.injEq] at heq
      have hI := mem_I_of_mem_family hgen (hRsub hδ₀.1) (hwitfam δ₀ hδ₀)
      have hI' := mem_I_of_mem_family hgen (hRsub hδ₀'.1) (hwitfam δ₀' hδ₀')
      have hmk : SigmaConjClasses.mk σ (wit δ₀) = SigmaConjClasses.mk σ (wit δ₀') :=
        mk_eq_mk_of_trace_eq_of_det_eq hgen hI hI' heq.1 heq.2
      obtain ⟨k, hk⟩ := SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mp hmk
      have h2 : ∃ (h : GL (Fin 2) L) (u : Lˣ), wit δ₀' = sc u * (h⁻¹ * δ₀ * σG σ h) :=
        family_sigmaConj σ (hwitfam δ₀ hδ₀) hk
      obtain ⟨δs, -, huniq⟩ := hR (wit δ₀') hI'
      exact (huniq δ₀ ⟨hδ₀.1, h2⟩).trans (huniq δ₀' ⟨hδ₀'.1, hwitfam δ₀' hδ₀'⟩).symm

  refine hRc_fin.subset ?_
  rintro δ₀ ⟨hδ₀R, x, z, hne⟩
  refine ⟨hδ₀R, ?_⟩
  have hmem : x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∈ tsupport φ :=
    subset_tsupport φ hne
  have hz2 : NumberField.TateGlobal.ideleNorm L z ^ 2 ∈ Set.Icc m₀ M₀ := by
    rw [← ideleNorm_det_kernelArg K L D σ x δ₀ z]
    exact ⟨hlo _ hmem, hhi _ hmem⟩
  have hz : NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
    mem_Icc_sqrt_of_sq_mem_Icc (NumberField.TateGlobal.ideleNorm_pos (F := L) z).le hz2
  obtain ⟨a, κ, hκ, rfl⟩ := hlift z hz
  refine ⟨sc (Units.map ((σ : L →+* L) : L →* L) a) * δ₀, ⟨x, κ, hκ, ?_⟩,
    ⟨1, Units.map ((σ : L →+* L) : L →* L) a, by simp⟩⟩
  rwa [kernelArg_princ_mul] at hmem

end Main

end R3Fin
p2m_reactivate "P2MW.S_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport.R3Fin"

end
p2m_reactivate "P2MW.S_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport.R3Fin"

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (R : Set (GL (Fin 2) L))
    (hRsub : R ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (hR : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) :
    {δ₀ ∈ R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite :=
  R3Fin.main K L σ hgen D φ hφc R hRsub hR

end S_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport (solution)
