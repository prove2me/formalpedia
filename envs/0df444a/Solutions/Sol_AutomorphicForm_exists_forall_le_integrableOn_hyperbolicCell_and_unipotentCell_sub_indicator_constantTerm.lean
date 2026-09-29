-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e3f956d5-3d8d-5a6a-9d7e-1bdb1e4493b3

import Theorems.Thm_AutomorphicForm_exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
import Theorems.Thm_AutomorphicForm_integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
import Theorems.Thm_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R1IntCellsK

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHeight NumberField.TateGlobal IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Function Set
open scoped Topology ENNReal NNReal Pointwise

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem subsingleton_algEquiv : Subsingleton (K ≃ₐ[K] K) :=
  ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩

attribute [local instance] subsingleton_algEquiv

def D₀ : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K := M4aHerbrand.identityDescent (𝓞 K) K K

theorem sigmaAdelicAct_D₀ : sigmaAdelicAct K K (D₀ K) 1 = MonoidHom.id _ := sigmaAdelicAct_one K K (D₀ K)

section Cells

open Polynomial Matrix

variable {F : Type*} [Field F]

theorem diag_ne_zero (γ : GL (Fin 2) F) (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem charpoly_upper (γ : GL (Fin 2) F) (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) F).charpoly =
      (X - C ((γ : Matrix (Fin 2) (Fin 2) F) 0 0)) * (X - C ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, h10, mul_zero, sub_zero, map_add,
    map_mul]
  ring

theorem eq_of_mul_eq_sq {a b e : F} (h : (X - C a) * (X - C b) = (X - C e) * (X - C e)) : a = e ∧ b = e := by
  have ha := congrArg (Polynomial.eval a) h
  have hb := congrArg (Polynomial.eval b) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  exact ⟨sub_eq_zero.mp (mul_self_eq_zero.mp ha.symm), sub_eq_zero.mp (mul_self_eq_zero.mp hb.symm)⟩

theorem trace_det_of_charpoly_eq (M : Matrix (Fin 2) (Fin 2) F) (r₁ r₂ : F)
    (h : M.charpoly = (X - C r₁) * (X - C r₂)) : M.trace = r₁ + r₂ ∧ M.det = r₁ * r₂ := by
  have key : (X ^ 2 - C M.trace * X + C M.det : F[X]) = X ^ 2 - C (r₁ + r₂) * X + C (r₁ * r₂) := by
    rw [← Matrix.charpoly_fin_two, h, map_add, map_mul]; ring
  have h1 := congrArg (fun p : F[X] => p.coeff 1) key
  have h0 := congrArg (fun p : F[X] => p.coeff 0) key
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C_zero, coeff_C_succ,
    coeff_X_zero, mul_one, mul_zero] at h1 h0
  norm_num at h1 h0
  refine ⟨?_, h0⟩
  have := neg_inj.mpr h1
  simp only [neg_neg, neg_add, add_comm] at this ⊢
  exact this

theorem charpoly_smul_of_eq (M : Matrix (Fin 2) (Fin 2) F) (a r₁ r₂ : F)
    (h : M.charpoly = (X - C r₁) * (X - C r₂)) :
    (a • M).charpoly = (X - C (a * r₁)) * (X - C (a * r₂)) := by
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq M r₁ r₂ h
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, htr, hdet, Fintype.card_fin, smul_eq_mul]
  simp only [map_add, map_mul, map_pow]
  ring

theorem coe_mul_scalar (γ : GL (Fin 2) F) (a : Fˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a : F) • (γ : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul]
  change (γ : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) (a : F) = _
  rw [Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) F} {a : F} (ha : a ≠ 0) :
    IsCentralType (a • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨a⁻¹ * c, ?_⟩
    have : M = a⁻¹ • (a • M) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this, hc, smul_smul]
  · rintro ⟨c, hc⟩
    exact ⟨a * c, by rw [hc, smul_smul]⟩

theorem mul_scalar_mem_hyperbolicCell (γ : GL (Fin 2) F) (hγ : γ ∈ hyperbolicCell F) (a : Fˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ hyperbolicCell F := by
  obtain ⟨r₁, r₂, hne, hp⟩ := hγ
  refine ⟨a * r₁, a * r₂, fun h => hne (mul_left_cancel₀ a.ne_zero h), ?_⟩
  rw [coe_mul_scalar]
  exact charpoly_smul_of_eq _ _ _ _ hp

theorem mul_scalar_mem_unipotentCell_union_centralCell (γ : GL (Fin 2) F)
    (hγ : γ ∈ unipotentCell F ∪ centralCell F) (a : Fˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ unipotentCell F ∪ centralCell F := by
  rcases hγ with hu | hc
  · left
    obtain ⟨hnc, r, hp⟩ := hu
    refine ⟨?_, a * r, ?_⟩
    · rw [coe_mul_scalar, isCentralType_smul_iff a.ne_zero]; exact hnc
    · rw [coe_mul_scalar, sq, charpoly_smul_of_eq _ _ _ _ (by rw [hp, sq])]
  · right
    show IsCentralType _
    rw [coe_mul_scalar, isCentralType_smul_iff a.ne_zero]
    exact hc

theorem mem_hyperbolicCell_iff_of_upper (γ : GL (Fin 2) F) (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    γ ∈ hyperbolicCell F ↔
      (γ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ {r : F | r ≠ 1} := by
  obtain ⟨-, h11⟩ := diag_ne_zero γ h10
  rw [Set.mem_setOf_eq, Ne, div_eq_one_iff_eq h11]
  constructor
  · rintro ⟨r₁, r₂, hne, hp⟩ heq
    rw [charpoly_upper γ h10, heq] at hp
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_sq hp.symm
    exact hne (h1.trans h2.symm)
  · intro hne
    exact ⟨_, _, hne, charpoly_upper γ h10⟩

theorem mem_unipotentCell_union_centralCell_iff_of_upper (γ : GL (Fin 2) F)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    γ ∈ unipotentCell F ∪ centralCell F ↔
      (γ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ {r : F | r = 1} := by
  obtain ⟨-, h11⟩ := diag_ne_zero γ h10
  rw [Set.mem_setOf_eq, div_eq_one_iff_eq h11]
  constructor
  · rintro (⟨-, r, hp⟩ | ⟨c, hc⟩)
    · rw [charpoly_upper γ h10, sq] at hp
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_sq hp
      exact h1.trans h2.symm
    · have h0 : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by rw [hc]; simp
      have h1 : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = c := by rw [hc]; simp
      rw [h0, h1]
  · intro heq
    by_cases hc : IsCentralType (γ : Matrix (Fin 2) (Fin 2) F)
    · exact Or.inr hc
    · refine Or.inl ⟨hc, (γ : Matrix (Fin 2) (Fin 2) F) 1 1, ?_⟩
      rw [charpoly_upper γ h10, heq, sq]

theorem exists_eq_scalar_of_mem_centralCell (γ : GL (Fin 2) F) (hγ : γ ∈ centralCell F) :
    ∃ c : Fˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  obtain ⟨c, hc⟩ := hγ
  have hc0 : c ≠ 0 := by
    intro h
    have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det γ).ne_zero
    rw [hc, h, zero_smul, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  change (γ : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) ((Units.mk0 c hc0 : Fˣ) : F)
  rw [hc, Units.val_mk0, Matrix.scalar_apply, smul_one_eq_diagonal]

theorem scalar_mem_centralCell (c : Fˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ centralCell F := by
  refine ⟨c, ?_⟩
  change Matrix.scalar (Fin 2) (c : F) = _
  rw [Matrix.scalar_apply, smul_one_eq_diagonal]

theorem disjoint_unipotentCell_centralCell : Disjoint (unipotentCell F) (centralCell F) :=
  Set.disjoint_left.mpr fun _ hu hc => hu.1 hc

end Cells

section Algebra

theorem coe_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) := rfl

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 K) K → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simpa [Matrix.scalar_apply] using continuous_id'
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_centralScalar]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 K) K) (fun r' => Commute.all _ r') _).eq

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem ideleNorm_one : ideleNorm K 1 = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h.symm.trans (mul_one _).symm)

theorem ideleNorm_inv (u : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K u⁻¹ = (ideleNorm K u)⁻¹ := by
  have h := ideleNorm_mul (F := K) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ideleNorm_pow_two (u : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K (u ^ 2) = ideleNorm K u ^ 2 := by
  rw [pow_two, pow_two, ideleNorm_mul]

theorem ideleNorm_det_karg (x : AdelicGL2 (𝓞 K) K) (γ : GL (Fin 2) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) =
      ideleNorm K z ^ 2 := by
  rw [map_mul, map_mul, map_inv, ideleNorm_mul, ideleNorm_mul, ideleNorm_inv,
    AutomorphicForm.ideleNorm_det_globalPoints, map_mul, det_centralScalar, ideleNorm_mul, ideleNorm_pow_two, mul_one]
  have hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ≠ 0 := (ideleNorm_pos (F := K) _).ne'
  field_simp

abbrev princ : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)

theorem globalPoints_scalar (a : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = centralScalar (𝓞 K) K (princ K a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) =
    Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Kˣ) (c : (AdeleRing (𝓞 K) K)ˣ), c ∈ C ∧ z = princ K a * c := by
  obtain ⟨C₁, hC₁c, -, hC₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul K
  obtain ⟨s, hs_cont, hs_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
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
  have hzpos : 0 < ideleNorm K z := ideleNorm_pos (F := K) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨ideleNorm K z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : ideleNorm K (s r) = ideleNorm K z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ normOneIdeles K := by
    rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_inv, hsr, mul_inv_cancel₀ hzpos.ne']
  obtain ⟨η, κ, hκ, hzκ⟩ := hC₁ _ hz₁
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

theorem finite_karg_mem {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) (x y : AdelicGL2 (𝓞 K) K) :
    {γ : GL (Fin 2) K | x⁻¹ * globalPoints (𝓞 K) K γ * y ∈ C}.Finite :=
  AutomorphicForm.adelicKernelLocalFiniteness K C hC x y

theorem finite_karg_mem_of_isCompact {P : Type*} [TopologicalSpace P] {a b : P → AdelicGL2 (𝓞 K) K}
    (ha : Continuous a) (hb : Continuous b) {N : Set P} (hN : IsCompact N)
    {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    {γ : GL (Fin 2) K | ∃ p ∈ N, (a p)⁻¹ * globalPoints (𝓞 K) K γ * b p ∈ C}.Finite := by
  set ψ : P × AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K := fun q => a q.1 * q.2 * (b q.1)⁻¹ with hψ
  have hψc : Continuous ψ :=
    ((ha.comp continuous_fst).mul continuous_snd).mul (hb.comp continuous_fst).inv
  have hC' : IsCompact (ψ '' (N ×ˢ C)) := (hN.prod hC).image hψc
  refine (finite_karg_mem K hC' 1 1).subset ?_
  rintro γ ⟨p, hp, hmem⟩
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨(p, (a p)⁻¹ * globalPoints (𝓞 K) K γ * b p), ⟨hp, hmem⟩, ?_⟩
  simp only [hψ]
  group

theorem continuous_finsum_mem_along {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P]
    {a b : P → AdelicGL2 (𝓞 K) K} (ha : Continuous a) (hb : Continuous b)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (I : Set (GL (Fin 2) K)) :
    Continuous fun p : P => ∑ᶠ γ ∈ I, f ((a p)⁻¹ * globalPoints (𝓞 K) K γ * b p) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  have hfin := finite_karg_mem_of_isCompact K ha hb hN hfc.isCompact
  set T : Finset (GL (Fin 2) K) := hfin.toFinset.filter (· ∈ I) with hTdef
  have heq : Set.EqOn
      (fun p : P => ∑ γ ∈ T, f ((a p)⁻¹ * globalPoints (𝓞 K) K γ * b p))
      (fun p : P => ∑ᶠ γ ∈ I, f ((a p)⁻¹ * globalPoints (𝓞 K) K γ * b p)) N := by
    intro p hp
    refine (finsum_mem_eq_sum_of_subset _ ?_ ?_).symm
    · rintro γ ⟨hγI, hγ⟩
      rw [Finset.mem_coe, hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨p, hp, subset_tsupport _ hγ⟩, hγI⟩
    · intro γ hγ
      rw [Finset.mem_coe, hTdef, Finset.mem_filter] at hγ
      exact hγ.2
  have hcont : Continuous fun p : P => ∑ γ ∈ T, f ((a p)⁻¹ * globalPoints (𝓞 K) K γ * b p) :=
    continuous_finsetSum _ fun γ _ => hf.comp ((ha.inv.mul continuous_const).mul hb)
  exact hcont.continuousAt.congr_of_eventuallyEq
    ((Filter.eventuallyEq_of_mem hNp heq).symm)

end Algebra

section Central

variable (f : AdelicGL2 (𝓞 K) K → ℂ)

theorem karg_central (x : AdelicGL2 (𝓞 K) K) (a : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    x⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * (centralScalar (𝓞 K) K z * x) =
      centralScalar (𝓞 K) K (princ K a * z) := by
  rw [globalPoints_scalar, map_mul, mul_assoc, centralScalar_comm K z x,
    ← mul_assoc (centralScalar (𝓞 K) K (princ K a)), centralScalar_comm K (princ K a) x, mul_assoc x,
    inv_mul_cancel_left]

def centralFn (z : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∑ᶠ γ ∈ centralCell K, f ((1 : AdelicGL2 (𝓞 K) K)⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * 1))

theorem finsum_centralCell_eq_centralFn (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ∑ᶠ γ ∈ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x)) = centralFn K f z := by
  refine finsum_mem_congr rfl fun γ hγ => ?_
  obtain ⟨a, rfl⟩ := exists_eq_scalar_of_mem_centralCell γ hγ
  rw [karg_central, karg_central]

theorem centralFn_princ_mul (a : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    centralFn K f (princ K a * z) = centralFn K f z := by
  unfold centralFn
  symm
  refine finsum_mem_eq_of_bijOn (fun γ => γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹) ⟨?_, ?_, ?_⟩ ?_
  · intro γ hγ
    obtain ⟨c, rfl⟩ := exists_eq_scalar_of_mem_centralCell γ hγ
    show Matrix.GeneralLinearGroup.scalar (Fin 2) c * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ ∈ _
    rw [← map_mul]; exact scalar_mem_centralCell _
  · intro γ _ γ' _ h
    exact mul_right_cancel h
  · intro γ hγ
    refine ⟨γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a, ?_, ?_⟩
    · obtain ⟨c, rfl⟩ := exists_eq_scalar_of_mem_centralCell γ hγ
      rw [← map_mul]; exact scalar_mem_centralCell _
    · show γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ = γ
      rw [map_inv, mul_inv_cancel_right]
  · intro γ hγ
    obtain ⟨c, rfl⟩ := exists_eq_scalar_of_mem_centralCell γ hγ
    show f (1⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (centralScalar (𝓞 K) K z * 1)) =
      f (1⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
        Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹) * (centralScalar (𝓞 K) K (princ K a * z) * 1))
    rw [← map_mul, karg_central, karg_central, map_mul (princ K), map_inv, mul_assoc, inv_mul_cancel_left]

theorem continuous_centralFn (hf : Continuous f) (hfc : HasCompactSupport f) : Continuous (centralFn K f) := by
  unfold centralFn
  exact continuous_finsum_mem_along K continuous_const ((continuous_centralScalar K).mul continuous_const) hf hfc _

theorem centralFn_eq_zero_of_not_mem {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : ideleNorm K z ^ 2 ∉ (fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g)) '' tsupport f) :
    centralFn K f z = 0 := by
  unfold centralFn
  refine finsum_mem_eq_zero_of_forall_eq_zero ?_
  intro γ _
  by_contra hne
  exact hz ⟨_, subset_tsupport _ hne, ideleNorm_det_karg K 1 γ z⟩

theorem exists_bound_centralPart (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ Cc : ℝ, ∀ (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      ‖∑ᶠ γ ∈ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))‖ ≤ Cc := by
  set Dn : Set ℝ := (fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g)) '' tsupport f
    with hDn
  have hDnc : IsCompact Dn := hfc.isCompact.image (NumberField.TateGlobal.continuous_ideleNorm_det K)
  rcases Dn.eq_empty_or_nonempty with hDe | hDne
  · refine ⟨0, fun x z => ?_⟩
    rw [finsum_centralCell_eq_centralFn, centralFn_eq_zero_of_not_mem K f (by rw [← hDn, hDe]; exact Set.notMem_empty _),
      norm_zero]
  set a : ℝ := Real.sqrt (sInf Dn) with ha
  set b : ℝ := Real.sqrt (sSup Dn) with hb
  have hDpos : ∀ d ∈ Dn, 0 < d := by
    rintro _ ⟨g, _, rfl⟩; exact ideleNorm_pos (F := K) _
  have ha0 : 0 < a := Real.sqrt_pos.mpr (hDpos _ (hDnc.sInf_mem hDne))
  have hband : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K z ^ 2 ∈ Dn → ideleNorm K z ∈ Set.Icc a b := fun z hz =>
    mem_Icc_sqrt_of_sq_mem_Icc (ideleNorm_pos (F := K) z).le ⟨csInf_le hDnc.bddBelow hz, le_csSup hDnc.bddAbove hz⟩
  obtain ⟨Z₀, hZ₀c, hZ₀⟩ := exists_isCompact_forall_mem_exists_princ_mul K (M₁ := b) ha0
  obtain ⟨M, hM⟩ := hZ₀c.exists_bound_of_continuousOn (f := centralFn K f) (continuous_centralFn K f hf hfc).continuousOn
  refine ⟨max M 0, fun x z => ?_⟩
  rw [finsum_centralCell_eq_centralFn]
  by_cases hzD : ideleNorm K z ^ 2 ∈ Dn
  · obtain ⟨a₀, z₀, hz₀, rfl⟩ := hZ₀ z (hband z hzD)
    rw [centralFn_princ_mul]
    exact (hM z₀ hz₀).trans (le_max_left _ _)
  · rw [centralFn_eq_zero_of_not_mem K f hzD, norm_zero]
    exact le_max_right _ _

end Central

section Slab

theorem nullMeasurableSet_of_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (ht : MeasurableSet t) (hst : s ⊆ t) (h : NullMeasurableSet s (μ.restrict t)) : NullMeasurableSet s μ := by
  obtain ⟨s', hs'm, hs'⟩ := h
  refine ⟨s' ∩ t, hs'm.inter ht, ?_⟩
  have h2 : ∀ᵐ x ∂μ, x ∈ t → (x ∈ s) = (x ∈ s') := (ae_restrict_iff' ht).mp hs'
  filter_upwards [h2] with x hx
  by_cases hxt : x ∈ t
  · have := hx hxt
    show (x ∈ s) = (x ∈ s' ∩ t)
    rw [this]; simp [hxt]
  · have hxs : x ∉ s := fun h => hxt (hst h)
    show (x ∈ s) = (x ∈ s' ∩ t)
    simp [hxs, hxt]

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det K).measurable measurableSet_Icc

theorem nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (hΦs : Φ ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 K) K) ∧ adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤ := by
  refine ⟨nullMeasurableSet_of_restrict _ (measurableSet_slab K α β) hΦs hΦ.nullMeasurableSet, ?_⟩
  have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    K α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_self_of_subset_left (show Φ ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
    Set.Icc α β} from hΦs)] at h

end Slab

section Main

theorem exp_ge_of_log_max_le {T₀ R : ℝ} (hR : Real.log (max T₀ 1) ≤ R) : T₀ ≤ Real.exp R := by
  have h1 : (0 : ℝ) < max T₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc T₀ ≤ max T₀ 1 := le_max_left _ _
    _ = Real.exp (Real.log (max T₀ 1)) := (Real.exp_log h1).symm
    _ ≤ Real.exp R := Real.exp_le_exp.mpr hR

theorem finsum_unipotentCell_union_centralCell {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : HasCompactSupport f)
    (x y : AdelicGL2 (𝓞 K) K) :
    ∑ᶠ γ ∈ unipotentCell K ∪ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * y) =
      (∑ᶠ γ ∈ unipotentCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * y)) +
        ∑ᶠ γ ∈ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * y) := by
  have hfin : (Function.support fun γ : GL (Fin 2) K => f (x⁻¹ * globalPoints (𝓞 K) K γ * y)).Finite :=
    (finite_karg_mem K hfc.isCompact x y).subset fun γ hγ => subset_tsupport _ hγ
  exact finsum_mem_union' disjoint_unipotentCell_centralCell (hfin.subset Set.inter_subset_right)
    (hfin.subset Set.inter_subset_right)

theorem mainK (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ hyperbolicCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
              Set.indicator (highSet (adelicHeight K) (Real.exp R))
              (@constantTerm _
                (productionPinsOf K ΦK (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).ν
                (fun t => unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
              (centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ hyperbolicCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
              Set.indicator (highSet (adelicHeight K) (Real.exp R))
              (@constantTerm _ (adeleBorel (𝓞 K) K) _ _
                (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun t => unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
              (centralScalar (𝓞 K) K z * x)) ∂νZK))
        (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ unipotentCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
              Set.indicator (highSet (adelicHeight K) (Real.exp R))
              (@constantTerm _
                (productionPinsOf K ΦK (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).ν
                (fun t => unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
              (centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ unipotentCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
              Set.indicator (highSet (adelicHeight K) (Real.exp R))
              (@constantTerm _ (adeleBorel (𝓞 K) K) _ _
                (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun t => unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
              (centralScalar (𝓞 K) K z * x)) ∂νZK))
        (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical

  obtain ⟨hf, hfc⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hff
  obtain ⟨hc, hTc, hcov, hslab, hfd⟩ := canonicalTruncationData_isTruncationDatum K α β hα hαβ
  obtain ⟨hΦm, hΦμ⟩ := nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab K hα hαβ hslab hfd

  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
      K K (D₀ K) 1 _ _ _ _ hc _ hTc _ hcov f hff

  obtain ⟨Cc, hCc⟩ := exists_bound_centralPart K f hf hfc
  refine ⟨Real.log (max T₀ 1), fun R hR => ?_⟩
  obtain ⟨C, hC⟩ := hT₀ (Real.exp R) (exp_ge_of_log_max_le hR)
  rw [sigmaAdelicAct_D₀] at hC
  simp only [MonoidHom.id_apply] at hC

  have hH : ∀ x ∈ canonicalTruncationDomain K α β, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖(∑ᶠ γ ∈ hyperbolicCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
          Set.indicator (highSet (adelicHeight K) (Real.exp R))
            (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r ≠ 1}},
                f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
            (centralScalar (𝓞 K) K z * x)‖ ≤ C :=
    hC {r : K | r ≠ 1} (hyperbolicCell K) (fun γ hγ a => mul_scalar_mem_hyperbolicCell γ hγ a)
      (fun γ h10 => mem_hyperbolicCell_iff_of_upper γ h10)
  have hHint :=
    AutomorphicForm.integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
      K (MonoidHom.id _) continuous_id (fun g => rfl) _ hΦμ hΦm νZK ΩK hΩK ξ hξc hξt f hf hfc
      (hyperbolicCell K)
      {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r ≠ 1}}
      (Real.exp R) C hH

  have hUC : ∀ x ∈ canonicalTruncationDomain K α β, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖(∑ᶠ γ ∈ unipotentCell K ∪ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
          Set.indicator (highSet (adelicHeight K) (Real.exp R))
            (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r = 1}},
                f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
            (centralScalar (𝓞 K) K z * x)‖ ≤ C :=
    hC {r : K | r = 1} (unipotentCell K ∪ centralCell K)
      (fun γ hγ a => mul_scalar_mem_unipotentCell_union_centralCell γ hγ a)
      (fun γ h10 => mem_unipotentCell_union_centralCell_iff_of_upper γ h10)
  have hU : ∀ x ∈ canonicalTruncationDomain K α β, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖(∑ᶠ γ ∈ unipotentCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) -
          Set.indicator (highSet (adelicHeight K) (Real.exp R))
            (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r = 1}},
                f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
            (centralScalar (𝓞 K) K z * x)‖ ≤ C + Cc := by
    intro x hx z
    have h1 := hUC x hx z
    have h2 := hCc x z
    rw [finsum_unipotentCell_union_centralCell K hfc] at h1
    set A := ∑ᶠ γ ∈ unipotentCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x)) with hA
    set Z := ∑ᶠ γ ∈ centralCell K, f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x)) with hZ
    set B := Set.indicator (highSet (adelicHeight K) (Real.exp R))
            (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r = 1}},
                f (x⁻¹ * globalPoints (𝓞 K) K γ * y)))
            (centralScalar (𝓞 K) K z * x) with hB
    have heq : A - B = (A + Z - B) - Z := by ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hUint :=
    AutomorphicForm.integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
      K (MonoidHom.id _) continuous_id (fun g => rfl) _ hΦμ hΦm νZK ΩK hΩK ξ hξc hξt f hf hfc
      (unipotentCell K)
      {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ {r : K | r = 1}}
      (Real.exp R) (C + Cc) hU

  have hHi : ∀ x : AdelicGL2 (𝓞 K) K, _ := fun x => by
    have h := AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
      K K ΦK νZK ΩK hΩK (D₀ K) 1 ξ hξc hξt f hf hfc
      (hyperbolicCell K) {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1} R x
    rw [sigmaAdelicAct_D₀] at h
    simp only [MonoidHom.id_apply] at h
    exact h
  have hUi : ∀ x : AdelicGL2 (𝓞 K) K, _ := fun x => by
    have h := AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
      K K ΦK νZK ΩK hΩK (D₀ K) 1 ξ hξc hξt f hf hfc
      (unipotentCell K) {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1} R x
    rw [sigmaAdelicAct_D₀] at h
    simp only [MonoidHom.id_apply] at h
    exact h
  exact ⟨hHi, hHint.2, hUi, hUint.2⟩

end Main

end R1IntCellsK

end

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option linter.unusedVariables false in
open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
  R1IntCellsK.mainK K α β hα hαβ ΦK νZK ΩK hΩK ξ hξc hξt f hff

end

end S_AutomorphicForm_exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm (solution)
