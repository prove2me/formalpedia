-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/59f247ef-5b3d-5b38-a4d1-44809415b5e6

import Theorems.Thm_AutomorphicForm_exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
import Theorems.Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
import Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
import Theorems.Thm_AutomorphicForm_existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

noncomputable section

namespace R4CuspDefect

set_option maxHeartbeats 1600000

open Matrix

section Alg

variable {L : Type} [Field L]

theorem coe_mul (g h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = (g : Matrix (Fin 2) (Fin 2) L) * (h : Matrix _ _ L) :=
  rfl

theorem mul_apply' (g h : GL (Fin 2) L) (i j : Fin 2) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (g : Matrix (Fin 2) (Fin 2) L) i 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 j +
        (g : Matrix (Fin 2) (Fin 2) L) i 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

def up (g : GL (Fin 2) L) : Prop := (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0

theorem up_iff (g : GL (Fin 2) L) : up g ↔ (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := Iff.rfl

theorem up_mul {g h : GL (Fin 2) L} (hg : up g) (hh : up h) : up (g * h) :=
  (AutomorphicForm.borelSubgroup L).mul_mem hg hh

theorem up_inv {g : GL (Fin 2) L} (hg : up g) : up g⁻¹ := (AutomorphicForm.borelSubgroup L).inv_mem hg

theorem mul_apply_00 (g : GL (Fin 2) L) {h : GL (Fin 2) L} (hh : up h) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 := by
  rw [mul_apply', show (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 from hh, mul_zero, add_zero]

theorem mul_apply_11 {g : GL (Fin 2) L} (hg : up g) (h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  rw [mul_apply', show (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 from hg, zero_mul, zero_add]

theorem mul_apply_01 (g h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) L) 0 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 1 :=
  mul_apply' g h 0 1

theorem det_ne_zero (g : GL (Fin 2) L) : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _

theorem apply_00_ne_zero {g : GL (Fin 2) L} (hg : up g) : (g : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  have h := det_ne_zero g
  rw [Matrix.det_fin_two, show (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 from hg, mul_zero, sub_zero] at h
  exact left_ne_zero_of_mul h

theorem apply_11_ne_zero {g : GL (Fin 2) L} (hg : up g) : (g : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have h := det_ne_zero g
  rw [Matrix.det_fin_two, show (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 from hg, mul_zero, sub_zero] at h
  exact right_ne_zero_of_mul h

theorem inv_apply_00 {g : GL (Fin 2) L} (hg : up g) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((g : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ := by
  have h1 : ((g⁻¹ * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    rw [inv_mul_cancel]; rfl
  rw [mul_apply_00 _ hg] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem inv_apply_11 {g : GL (Fin 2) L} (hg : up g) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = ((g : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ := by
  have h1 : ((g⁻¹ * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
    rw [inv_mul_cancel]; rfl
  rw [mul_apply_11 (up_inv hg)] at h1
  exact eq_inv_of_mul_eq_one_left h1

abbrev sc (u : Lˣ) : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) u

theorem sc_apply (u : Lˣ) (i j : Fin 2) :
    ((sc u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = if i = j then (u : L) else 0 := by
  show Matrix.scalar (Fin 2) (u : L) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem up_sc (u : Lˣ) : up (sc u) := by rw [up_iff, sc_apply]; simp

theorem sc_comm (u : Lˣ) (g : GL (Fin 2) L) : sc u * g = g * sc u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (u : L) (fun r' => Commute.all _ r') _).eq

theorem sc_mem_center (u : Lˣ) : sc u ∈ Subgroup.center (GL (Fin 2) L) :=
  Subgroup.mem_center_iff.mpr fun g => (sc_comm u g).symm

theorem exists_sc_of_mem_center {s : GL (Fin 2) L} (hs : s ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ u : Lˣ, s = sc u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, hu.symm⟩

abbrev un (s : L) : GL (Fin 2) L := AutomorphicForm.unipotentGL2 s

theorem un_apply (s : L) (i j : Fin 2) :
    ((un s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = !![(1 : L), s; 0, 1] i j := by
  rw [AutomorphicForm.unipotentGL2_coe]

theorem un_apply_00 (s : L) : ((un s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
  rw [un_apply]; rfl
theorem un_apply_11 (s : L) : ((un s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
  rw [un_apply]; rfl
theorem un_apply_10 (s : L) : ((un s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [un_apply]; rfl
theorem up_un (s : L) : up (un s) := un_apply_10 s

theorem un_inv (s : L) : (un s : GL (Fin 2) L)⁻¹ = un (-s) := by
  refine inv_eq_of_mul_eq_one_right ?_
  show AutomorphicForm.unipotentGL2 s * AutomorphicForm.unipotentGL2 (-s) = 1
  rw [← AutomorphicForm.unipotentGL2_add, add_neg_cancel, AutomorphicForm.unipotentGL2_zero]

abbrev wL : GL (Fin 2) L := AutomorphicForm.gl2Weyl

theorem mul_wL_apply (m : GL (Fin 2) L) (i : Fin 2) :
    ((m * wL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0 = (m : Matrix (Fin 2) (Fin 2) L) i 1 ∧
      ((m * wL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 1 = (m : Matrix (Fin 2) (Fin 2) L) i 0 := by
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.gl2Weyl_val]

theorem wL_mul_apply (m : GL (Fin 2) L) (j : Fin 2) :
    ((wL * m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 j = (m : Matrix (Fin 2) (Fin 2) L) 1 j ∧
      ((wL * m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j = (m : Matrix (Fin 2) (Fin 2) L) 0 j := by
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.gl2Weyl_val]

end Alg

section Twist

variable {K L : Type} [Field K] [Field L] [Algebra K L]

abbrev σG (σ : L ≃ₐ[K] L) : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem σG_apply (σ : L ≃ₐ[K] L) (m : GL (Fin 2) L) (i j : Fin 2) :
    ((σG σ m : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = σ ((m : Matrix (Fin 2) (Fin 2) L) i j) := rfl

theorem up_σG (σ : L ≃ₐ[K] L) {m : GL (Fin 2) L} (hm : up m) : up (σG σ m) := by
  rw [up_iff, σG_apply, (up_iff m).1 hm, map_zero]

theorem σG_un (σ : L ≃ₐ[K] L) (s : L) : σG σ (un s) = un (σ s) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((σG σ (un s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = ((un (σ s) : GL (Fin 2) L) : Matrix _ _ L) i j
  rw [σG_apply, un_apply, un_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem σG_sc (σ : L ≃ₐ[K] L) (u : Lˣ) : σG σ (sc u) = sc (Units.map (σ : L →* L) u) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((σG σ (sc u) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = ((sc _ : GL (Fin 2) L) : Matrix _ _ L) i j
  rw [σG_apply, sc_apply, sc_apply]
  split_ifs <;> simp

theorem norm_div [FiniteDimensional K L] (x y : L) (hy : y ≠ 0) :
    Algebra.norm K (x / y) = Algebra.norm K x / Algebra.norm K y := by
  have hNy : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  rw [eq_div_iff hNy, ← map_mul, div_mul_cancel₀ _ hy]

theorem norm_σ [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : L) : Algebra.norm K (σ x) = Algebra.norm K x :=
  Algebra.norm_eq_of_algEquiv σ x

def ratio (g : GL (Fin 2) L) : L := (g : Matrix (Fin 2) (Fin 2) L) 0 0 / (g : Matrix (Fin 2) (Fin 2) L) 1 1

theorem norm_ratio_eq [FiniteDimensional K L] (σ : L ≃ₐ[K] L) {t γ b : GL (Fin 2) L}
    (ht : up t) (hγ : up γ) (hb : up b)
    (h : t⁻¹ * (b⁻¹ * γ * σG σ b) ∈ Subgroup.center (GL (Fin 2) L)) :
    Algebra.norm K (ratio γ) = Algebra.norm K (ratio t) := by
  obtain ⟨u, hu⟩ := exists_sc_of_mem_center h
  have hm : b⁻¹ * γ * σG σ b = t * sc u := by rw [← hu]; group

  have hb00 := apply_00_ne_zero hb
  have hb11 := apply_11_ne_zero hb
  have e00 : ((b : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) L) 0 0 *
      σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) = (t : Matrix (Fin 2) (Fin 2) L) 0 0 * u := by
    have l := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) hm
    beta_reduce at l
    rw [mul_apply_00 _ (up_σG σ hb), mul_apply_00 _ hγ, inv_apply_00 hb, σG_apply,
      mul_apply_00 _ (up_sc u), sc_apply] at l
    simpa using l
  have e11 : ((b : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) L) 1 1 *
      σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) = (t : Matrix (Fin 2) (Fin 2) L) 1 1 * u := by
    have l := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 1 1) hm
    beta_reduce at l
    rw [mul_apply_11 (up_mul (up_inv hb) hγ), mul_apply_11 (up_inv hb), inv_apply_11 hb, σG_apply,
      mul_apply_11 ht, sc_apply] at l
    simpa using l

  have hσb00 : σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := by
    intro h0; exact hb00 (by simpa using congrArg σ.symm h0)
  have hσb11 : σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := by
    intro h0; exact hb11 (by simpa using congrArg σ.symm h0)
  have g00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (t : Matrix (Fin 2) (Fin 2) L) 0 0 * u * (b : Matrix (Fin 2) (Fin 2) L) 0 0 *
        (σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0))⁻¹ := by
    field_simp
    have := e00
    field_simp at this
    linear_combination this
  have g11 : (γ : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (t : Matrix (Fin 2) (Fin 2) L) 1 1 * u * (b : Matrix (Fin 2) (Fin 2) L) 1 1 *
        (σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1))⁻¹ := by
    field_simp
    have := e11
    field_simp at this
    linear_combination this

  have hN00 : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0) =
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K (u : L) := by
    rw [g00, map_mul, map_mul, map_mul, ← map_inv₀ (σ : L ≃ₐ[K] L), norm_σ, mul_assoc,
      ← map_mul (Algebra.norm K) ((b : Matrix (Fin 2) (Fin 2) L) 0 0), mul_inv_cancel₀ hb00, map_one, mul_one]
  have hN11 : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 1 1) =
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) * Algebra.norm K (u : L) := by
    rw [g11, map_mul, map_mul, map_mul, ← map_inv₀ (σ : L ≃ₐ[K] L), norm_σ, mul_assoc,
      ← map_mul (Algebra.norm K) ((b : Matrix (Fin 2) (Fin 2) L) 1 1), mul_inv_cancel₀ hb11, map_one, mul_one]
  have hNu : Algebra.norm K (u : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr u.ne_zero
  unfold ratio
  rw [norm_div _ _ (apply_11_ne_zero hγ), norm_div _ _ (apply_11_ne_zero ht), hN00, hN11,
    mul_div_mul_right _ _ hNu]

variable [FiniteDimensional K L]

omit [FiniteDimensional K L] in

theorem mem_of_conj (σ : L ≃ₐ[K] L) {δ₀ : GL (Fin 2) L} {I : Set (GL (Fin 2) L)}
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L, δ₀⁻¹ * (g⁻¹ * δ * σG σ g) ∈ Subgroup.center (GL (Fin 2) L))
    {δ : GL (Fin 2) L} (hδ : δ ∈ I) (m : GL (Fin 2) L) : m * δ * (σG σ m)⁻¹ ∈ I := by
  obtain ⟨g, hg⟩ := (hI δ).1 hδ
  refine (hI _).2 ⟨m * g, ?_⟩
  have : (m * g)⁻¹ * (m * δ * (σG σ m)⁻¹) * σG σ (m * g) = g⁻¹ * δ * σG σ g := by
    rw [map_mul]; group
  rw [this]; exact hg

omit [FiniteDimensional K L] in

theorem mem_of_mul_sc (σ : L ≃ₐ[K] L) {δ₀ : GL (Fin 2) L} {I : Set (GL (Fin 2) L)}
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L, δ₀⁻¹ * (g⁻¹ * δ * σG σ g) ∈ Subgroup.center (GL (Fin 2) L))
    {δ : GL (Fin 2) L} (hδ : δ ∈ I) (u : Lˣ) : δ * sc u ∈ I := by
  obtain ⟨g, hg⟩ := (hI δ).1 hδ
  refine (hI _).2 ⟨g, ?_⟩
  have : δ₀⁻¹ * (g⁻¹ * (δ * sc u) * σG σ g) = δ₀⁻¹ * (g⁻¹ * δ * σG σ g) * sc u := by
    rw [show g⁻¹ * (δ * sc u) * σG σ g = g⁻¹ * δ * (sc u * σG σ g) by group, sc_comm]; group
  rw [this]
  exact Subgroup.mul_mem _ hg (sc_mem_center u)

theorem exists_un_diag (σ : L ≃ₐ[K] L) {γ : GL (Fin 2) L} (hγ : up γ) (hN : Algebra.norm K (ratio γ) ≠ 1) :
    ∃ (s : L) (d : GL (Fin 2) L), up d ∧ (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (d : Matrix (Fin 2) (Fin 2) L) 0 0 = (γ : Matrix (Fin 2) (Fin 2) L) 0 0 ∧
      (d : Matrix (Fin 2) (Fin 2) L) 1 1 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∧
      γ = (un s)⁻¹ * d * σG σ (un s) := by
  obtain ⟨s, hs, -⟩ :=
    AutomorphicForm.existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
      (F := K) σ γ hγ hN
  set d : GL (Fin 2) L := un s * γ * (σG σ (un s))⁻¹ with hd
  have hd' : AutomorphicForm.sigmaConj (σ : L →+* L) (AutomorphicForm.unipotentGL2 s) γ = d := rfl
  rw [hd'] at hs
  have hσinv : (σG σ (un s))⁻¹ = un (-(σ s)) := by rw [σG_un, un_inv]
  have hupd : up d := up_mul (up_mul (up_un s) hγ) (by rw [hσinv]; exact up_un _)
  refine ⟨s, d, hupd, hs, ?_, ?_, ?_⟩
  · rw [hd, hσinv, mul_apply_00 _ (up_un _), mul_apply_00 _ hγ, un_apply_00, un_apply_00, one_mul, mul_one]
  · rw [hd, hσinv, mul_apply_11 (up_mul (up_un s) hγ), mul_apply_11 (up_un s), un_apply_11, un_apply_11,
      one_mul, mul_one]
  · rw [hd]; group

theorem diag_eq_mul_sc {d d' : GL (Fin 2) L} (hd : up d) (hd01 : (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hd' : up d') (hd'01 : (d' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (hr : ratio d = ratio d') :
    ∃ u : Lˣ, d = d' * sc u := by
  have h00 := apply_00_ne_zero hd
  have h00' := apply_00_ne_zero hd'
  have h11 := apply_11_ne_zero hd
  have h11' := apply_11_ne_zero hd'
  refine ⟨Units.mk0 ((d : Matrix (Fin 2) (Fin 2) L) 0 0 / (d' : Matrix (Fin 2) (Fin 2) L) 0 0)
    (div_ne_zero h00 h00'), Units.ext (Matrix.ext fun i j => ?_)⟩
  show (d : Matrix (Fin 2) (Fin 2) L) i j = ((d' * sc _ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
  rw [mul_apply', sc_apply, sc_apply]
  unfold ratio at hr
  rw [div_eq_div_iff h11 h11'] at hr
  fin_cases i <;> fin_cases j
  · simp; field_simp
  · simp [hd01, hd'01]
  · simp [(up_iff d).1 hd, (up_iff d').1 hd']
  · simp; field_simp; linear_combination -hr

end Twist

section ClassCosets

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def ratioSet (I : Set (GL (Fin 2) L)) : Set L := {ρ | ∃ γ : GL (Fin 2) L, up γ ∧ γ ∈ I ∧ ratio γ = ρ}

variable {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  {δ₀ : GL (Fin 2) L} (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
  (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
  {I : Set (GL (Fin 2) L)}
  (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L, δ₀⁻¹ * (g⁻¹ * δ * σG σ g) ∈ Subgroup.center (GL (Fin 2) L))

include hgen hδ₀u hδ₀l hreg hI

theorem norm_ratio_ne_one {γ : GL (Fin 2) L} (hγ : up γ) (hγI : γ ∈ I) : Algebra.norm K (ratio γ) ≠ 1 := by
  set tw : GL (Fin 2) L := wL * δ₀ * wL with htw_def
  have htw10 : (tw : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    rw [htw_def, (mul_wL_apply (wL * δ₀) 1).1, (wL_mul_apply δ₀ 1).2, hδ₀l]
  have htw01 : (tw : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    rw [htw_def, (mul_wL_apply (wL * δ₀) 0).2, (wL_mul_apply δ₀ 0).1, hδ₀u]
  have htw00 : (tw : Matrix (Fin 2) (Fin 2) L) 0 0 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [htw_def, (mul_wL_apply (wL * δ₀) 0).1, (wL_mul_apply δ₀ 1).1]
  have htw11 : (tw : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    rw [htw_def, (mul_wL_apply (wL * δ₀) 1).2, (wL_mul_apply δ₀ 0).2]
  obtain ⟨hunion, -, -⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
      hgen δ₀ tw hδ₀u hδ₀l hreg ⟨htw10, htw01⟩ htw00 htw11
  have hmem : γ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
    ⟨hγ, (hI γ).1 hγI⟩
  rw [hunion] at hmem
  rcases hmem with ⟨b, hb, hbc⟩ | ⟨b, hb, hbc⟩
  · rw [norm_ratio_eq σ hδ₀u hγ hb hbc]; exact hreg
  · rw [norm_ratio_eq σ htw10 hγ hb hbc]
    unfold ratio
    rw [htw00, htw11]
    intro h1
    apply hreg
    rwa [norm_div _ _ (apply_00_ne_zero hδ₀u), ← inv_div, ← norm_div _ _ (apply_11_ne_zero hδ₀u),
      inv_eq_one] at h1

theorem norm_ne_one_of_mem_ratioSet {ρ : L} (hρ : ρ ∈ ratioSet I) : Algebra.norm K ρ ≠ 1 := by
  obtain ⟨γ, hγ, hγI, rfl⟩ := hρ
  exact norm_ratio_ne_one hgen hδ₀u hδ₀l hreg hI hγ hγI

theorem setOf_up_and_mem_eq :
    {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I} =
      {γ : Matrix.GeneralLinearGroup (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ ratioSet I} := by
  ext γ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hγ, hγI⟩
    exact ⟨hγ, γ, hγ, hγI, rfl⟩
  · rintro ⟨hγ, γ', hγ', hγ'I, hr⟩
    refine ⟨hγ, ?_⟩
    have hN' : Algebra.norm K (ratio γ') ≠ 1 := norm_ratio_ne_one hgen hδ₀u hδ₀l hreg hI hγ' hγ'I
    have hN : Algebra.norm K (ratio γ) ≠ 1 := by unfold ratio; rw [← hr]; exact hN'
    obtain ⟨s, d, hd, hd01, hd00, hd11, hγeq⟩ := exists_un_diag σ hγ hN
    obtain ⟨s', d', hd', hd'01, hd'00, hd'11, hγ'eq⟩ := exists_un_diag σ hγ' hN'
    have hrd : ratio d = ratio d' := by
      unfold ratio at hr ⊢
      rw [hd00, hd11, hd'00, hd'11]
      exact hr.symm
    obtain ⟨u, hdu⟩ := diag_eq_mul_sc hd hd01 hd' hd'01 hrd

    have hd'eq : d' = un s' * γ' * (σG σ (un s'))⁻¹ := by rw [hγ'eq]; group
    set m : GL (Fin 2) L := (un s)⁻¹ * un s' with hm
    have key : γ = m * γ' * (σG σ m)⁻¹ * sc u := by
      rw [hγeq, hdu, hd'eq, hm, map_mul, map_inv]
      have hc := sc_comm u (σG σ (un s))
      calc (un s)⁻¹ * (un s' * γ' * (σG σ (un s'))⁻¹ * sc u) * σG σ (un s)
          = (un s)⁻¹ * (un s' * γ' * (σG σ (un s'))⁻¹) * (sc u * σG σ (un s)) := by group
        _ = (un s)⁻¹ * (un s' * γ' * (σG σ (un s'))⁻¹) * (σG σ (un s) * sc u) := by rw [hc]
        _ = (un s)⁻¹ * un s' * γ' * ((σG σ (un s))⁻¹ * σG σ (un s'))⁻¹ * sc u := by group
    rw [key]
    exact mem_of_mul_sc σ hI (mem_of_conj σ hI hγ'I m) u

end ClassCosets

section Invariance

open MeasureTheory NumberField

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * g = g * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (w : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L w) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) w) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L → _)
      (Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L → _) w) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sigmaAdelicAct_globalPoints' (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L g) =
      AutomorphicForm.globalPoints (𝓞 L) L (σG σ g) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g

theorem kernelArg_conj (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (b γ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (AutomorphicForm.globalPoints (𝓞 L) L b * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * x)) =
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (b⁻¹ * γ * σG σ b) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) := by
  have h1 : AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * x)) =
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) *
        AutomorphicForm.globalPoints (𝓞 L) L (σG σ b) * AutomorphicForm.sigmaAdelicAct K L D σ x := by
    rw [map_mul, map_mul, sigmaAdelicAct_globalPoints', ← mul_assoc]
  have h2 : AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) *
        AutomorphicForm.sigmaAdelicAct K L D σ x := map_mul _ _ _
  have hcomm : AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) *
        AutomorphicForm.globalPoints (𝓞 L) L (σG σ b) =
      AutomorphicForm.globalPoints (𝓞 L) L (σG σ b) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) := by
    rw [sigmaAdelicAct_centralScalar]; exact centralScalar_comm _ _
  rw [h1, h2, _root_.mul_inv_rev, hcomm, map_mul, map_mul, map_inv]
  simp only [mul_assoc]

theorem fold_globalPoints_mul [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (ξ : (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (J : Set (GL (Fin 2) L)) (hJ : ∀ b : GL (Fin 2) L, up b → ∀ γ ∈ J, b⁻¹ * γ * σG σ b ∈ J)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (∫ z in ΩL, ξ z * ∑ᶠ γ ∈ J, φ ((AutomorphicForm.globalPoints (𝓞 L) L b * x)⁻¹ *
        AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * x))) ∂νZL) =
      ∫ z in ΩL, ξ z * ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL := by
  have hbij : Set.BijOn (fun γ : GL (Fin 2) L => b⁻¹ * γ * σG σ b) J J := by
    refine ⟨fun γ hγ => hJ b hb γ hγ, fun γ _ γ' _ h => ?_, fun γ' hγ' => ?_⟩
    · simpa using h
    · refine ⟨b * γ' * (σG σ b)⁻¹, ?_, by simp only []; group⟩
      have := hJ b⁻¹ (up_inv hb) γ' hγ'
      rwa [map_inv, inv_inv] at this
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only []
  congr 1
  refine finsum_mem_eq_of_bijOn (fun γ : GL (Fin 2) L => b⁻¹ * γ * σG σ b) hbij fun γ _ => ?_
  rw [kernelArg_conj]

end Invariance

section Assemble

open MeasureTheory

theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] {μ : Measure X} {s E : Set X}
    (hs : NullMeasurableSet s (μ.restrict E)) (hsE : s ⊆ E) (hE : MeasurableSet E) : NullMeasurableSet s μ := by
  obtain ⟨t, hts, htm, hteq⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : (μ.restrict E) (t \ s) = 0 := (ae_eq_set.1 hteq).1
  rw [Measure.restrict_apply' hE] at h1
  refine (htm.inter hE).nullMeasurableSet.congr ?_
  rw [ae_eq_set]
  constructor
  · have : (t ∩ E) \ s = (t \ s) ∩ E := by
      ext x; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [this]; exact h1
  · have : s \ (t ∩ E) = ∅ := Set.diff_eq_empty.2 fun x hx => ⟨hts hx, hsE hx⟩
    rw [this]; exact measure_empty

theorem assemble {G : Type*} [MeasurableSpace G] {μ : Measure G} {Φ₀ s : Set G} (a aT aN : G → ℂ)
    (hsm : MeasurableSet s) (hΦ₀ : NullMeasurableSet Φ₀ μ) (hfin : μ Φ₀ < ⊤)
    (ha : Measurable a) (hat : Measurable aT) (C : ℝ)
    (hbd : ∀ x ∈ Φ₀, x ∈ s → ‖a x - aT x‖ ≤ C) (hNeq : ∀ x, aN x = aT x)
    (hvan : IntegrableOn (fun x => (a x - aN x) * (fun _ => (1 : ℂ)) x) (Φ₀ ∩ s) μ →
      ∫ x in Φ₀ ∩ s, (a x - aN x) * (fun _ => (1 : ℂ)) x ∂μ = 0) :
    IntegrableOn (fun x => s.indicator (fun _ => (1 : ℂ)) x * (a x - aT x)) Φ₀ μ ∧
      ∫ x in Φ₀, s.indicator (fun _ => (1 : ℂ)) x * (a x - aT x) ∂μ = 0 := by
  have hind : (fun x => s.indicator (fun _ => (1 : ℂ)) x * (a x - aT x)) = s.indicator (fun x => a x - aT x) := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

  have hint : IntegrableOn (fun x => a x - aT x) (s ∩ Φ₀) μ := by
    refine Measure.integrableOn_of_bounded (M := C) ?_ (ha.sub hat).aestronglyMeasurable ?_
    · exact ((measure_mono Set.inter_subset_right).trans_lt hfin).ne
    · have hmem : ∀ᵐ x ∂μ.restrict (s ∩ Φ₀), x ∈ s ∩ Φ₀ :=
        ae_restrict_mem₀ (hsm.nullMeasurableSet.inter hΦ₀)
      filter_upwards [hmem] with x hx using hbd x hx.2 hx.1
  have e : (fun x => (a x - aN x) * (fun _ => (1 : ℂ)) x) = fun x => a x - aT x :=
    funext fun x => by simp only [hNeq x, mul_one]
  have hint' : IntegrableOn (fun x => (a x - aN x) * (fun _ => (1 : ℂ)) x) (Φ₀ ∩ s) μ := by
    rw [e, Set.inter_comm]; exact hint
  constructor
  · rw [hind, IntegrableOn, integrable_indicator_iff hsm, IntegrableOn, Measure.restrict_restrict hsm]
    exact hint
  · rw [hind, setIntegral_indicator hsm]
    refine Eq.trans ?_ (hvan hint')
    rw [e]

end Assemble

section Main

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _
          (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀,
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφ

  have hI' : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L, δ₀⁻¹ * (g⁻¹ * δ * σG σ g) ∈ Subgroup.center (GL (Fin 2) L) := hI
  set A : Set L := ratioSet I with hA_def
  have hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1 := fun ρ hρ =>
    norm_ne_one_of_mem_ratioSet hgen hδ₀u hδ₀l hreg hI' hρ
  have hJA : {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I} =
      {γ : Matrix.GeneralLinearGroup (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A} :=
    setOf_up_and_mem_eq hgen hδ₀u hδ₀l hreg hI'

  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
      K L νZL ΩL hΩL D σ hgen ξL hξc hξt A hA φ hφc hφs
  obtain ⟨T₁, hP1⟩ :=
    AutomorphicForm.exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
      K L νZL ΩL hΩL D σ ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S φ hφ
  obtain ⟨C, hC⟩ := hP1 0
  obtain ⟨T₀, -, hP3⟩ :=
    AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet
      L α β c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀

  dsimp only [AutomorphicForm.productionPinsOf]
  simp only [hJA]
  refine ⟨h1, h2, max T₁ T₀, fun R hR => ?_⟩

  have hexp : R + 1 ≤ Real.exp R := Real.add_one_le_exp R
  have hRT₁ : T₁ < Real.exp R := by
    have := le_max_left T₁ T₀; linarith
  have hRT₀ : T₀ ≤ Real.exp R := by
    have := le_max_right T₁ T₀; linarith

  set s : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} with hs_def
  have hsm : MeasurableSet s :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight L).measurable

  set slab : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab
  have hslab_m : MeasurableSet slab :=
    (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc
  have hΦ₀null : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) :=
    nullMeasurableSet_of_restrict hΦ₀.nullMeasurableSet hΦ₀s hslab_m
  have hfin : adelicGLHaar (Fin 2) (𝓞 L) L Φ₀ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      L α β hα hαβ Φ₀ hΦ₀
    rwa [Set.inter_eq_left.2 hΦ₀s] at h

  have hJstab : ∀ b : GL (Fin 2) L, up b →
      ∀ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
      b⁻¹ * γ * σG σ b ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A} := by
    intro b hb γ hγ
    rw [← hJA] at hγ ⊢
    obtain ⟨hγu, hγI⟩ := hγ
    refine ⟨up_mul (up_mul (up_inv hb) hγu) (up_σG σ hb), ?_⟩
    have := mem_of_conj σ hI' hγI b⁻¹
    rwa [map_inv, inv_inv] at this

  refine assemble _ _ _ hsm hΦ₀null hfin h3 h4 C ?_ h5 ?_
  · intro x hx hxs
    have hHx : T₁ < NumberField.AdelicHeight.adelicHeight L x := lt_trans hRT₁ hxs
    have hb := hC A x hx hHx
    rw [pow_zero, mul_one] at hb
    refine le_trans (le_of_eq ?_) hb
    congr 1
    refine Eq.trans (integral_sub (h1 x) (h2 x)).symm ?_
    congr 1
    funext z
    exact (mul_sub _ _ _).symm
  · intro hint
    refine hP3 (Real.exp R) hRT₀ _ (fun _ => (1 : ℂ)) h3 measurable_const ?_ (fun _ _ _ => rfl) (fun _ _ => rfl) hint
    intro γ hγ g
    exact fold_globalPoints_mul νZL ΩL D σ _ _ hJstab φ hγ g

end Main

end R4CuspDefect

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))

    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _
          (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀,
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (AutomorphicForm.productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 :=
  R4CuspDefect.main K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ δ₀ hδ₀u hδ₀l
    hreg I hI φ hφ

end
end S_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero (solution)
