-- Prove2me | solution 1 for AutomorphicForm.exists_torusSection_forall_normString_diagUnits2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f44398bf-44a9-5b0f-9039-233f3b391d1f

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
import Theorems.Thm_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter Set
open scoped NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mUnitWeightK

open AutomorphicForm

section Norms

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qv : 1 < qv K v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

theorem qv_pos : 0 < qv K v := lt_trans zero_lt_one (one_lt_qv K v)

theorem qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem exists_norm_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
  push_cast
  rfl

theorem norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · exact Or.inr (exists_norm_eq_zpow K v hx)

theorem norm_le_zpow_sub_one_of_lt {x : v.adicCompletion K} {n : ℤ} (h : ‖x‖ < qv K v ^ n) :
    ‖x‖ ≤ qv K v ^ (n - 1) := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0]; exact zpow_nonneg (qv_pos K v).le _
  · rw [hk] at h ⊢
    have hlt : k < n := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem exists_norm_eq_inv : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  refine ⟨(π : v.adicCompletion K), ?_⟩
  have hval : (Valued.v (π : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  have hv0 : (Valued.v (π : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 := by
    rw [hval]; exact WithZero.coe_ne_zero
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
  push_cast
  have h3 : WithZero.unzero hv0 = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero hv0, hval]
    rfl
  have : Multiplicative.toAdd (WithZero.unzero hv0) = -1 := by rw [h3]; rfl
  rw [this, zpow_neg, zpow_one]

end Norms

section Residue

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev kv : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers K)

scoped instance : Finite (kv K v) := inferInstance

noncomputable scoped instance : Fintype (kv K v) := Fintype.ofFinite _

theorem card_kv : Fintype.card (kv K v) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card,
    ← Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

def rep (c : kv K v) : v.adicCompletion K :=
  ((Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K)) c :
    v.adicCompletionIntegers K) : v.adicCompletion K)

theorem residue_rep (c : kv K v) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K)) c) = c :=
  Function.surjInv_eq _ c

theorem norm_rep_le_one (c : kv K v) : ‖rep K v c‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (Subtype.coe_prop _)

theorem norm_lt_one_iff_residue_eq_zero (y : v.adicCompletionIntegers K) :
    ‖(y : v.adicCompletion K)‖ < 1 ↔ IsLocalRing.residue (v.adicCompletionIntegers K) y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valued.toNormedField.norm_lt_one_iff]
  exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := y)).symm

theorem norm_sub_rep_lt_one {y : v.adicCompletion K} (hy : ‖y‖ ≤ 1) :
    ‖y - rep K v (IsLocalRing.residue (v.adicCompletionIntegers K) ⟨y, (mem_integers_iff_norm K v y).2 hy⟩)‖ < 1 := by
  set y' : v.adicCompletionIntegers K := ⟨y, (mem_integers_iff_norm K v y).2 hy⟩ with hy'
  set r' : v.adicCompletionIntegers K :=
    Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K))
      (IsLocalRing.residue (v.adicCompletionIntegers K) y') with hr'
  have hres : IsLocalRing.residue (v.adicCompletionIntegers K) (y' - r') = 0 := by
    rw [map_sub, hr', residue_rep, sub_self]
  have := (norm_lt_one_iff_residue_eq_zero K v (y' - r')).2 hres
  simpa [rep, hy', hr'] using this

theorem rep_eq_of_norm_sub_lt_one {c c' : kv K v} (h : ‖rep K v c - rep K v c'‖ < 1) : c = c' := by
  set r : v.adicCompletionIntegers K :=
    Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K)) c with hr
  set r' : v.adicCompletionIntegers K :=
    Function.surjInv (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K)) c' with hr'
  have h' : ‖((r - r' : v.adicCompletionIntegers K) : v.adicCompletion K)‖ < 1 := by
    simpa [rep, hr, hr'] using h
  have h2 := (norm_lt_one_iff_residue_eq_zero K v (r - r')).1 h'
  rw [map_sub, sub_eq_zero, hr, hr', residue_rep, residue_rep] at h2
  exact h2

theorem norm_lt_one_iff_le_inv (x : v.adicCompletion K) : ‖x‖ < 1 ↔ ‖x‖ ≤ (qv K v)⁻¹ := by
  constructor
  · intro h
    have := norm_le_zpow_sub_one_of_lt K v (n := 0) (by simpa using h)
    simpa using this
  · intro h
    exact lt_of_le_of_lt h (inv_lt_one_of_one_lt₀ (one_lt_qv K v))

end Residue

section IntegralPoints

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_mul_max (M : Matrix (Fin 2) (Fin 2) Kv) :
    ‖M.det‖ ≤ max ‖M 0 0‖ ‖M 0 1‖ * max ‖M 1 0‖ ‖M 1 1‖ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 :=
  (norm_det_le_mul_max K v M).trans
    (mul_le_one₀ (max_le (hM 0 0) (hM 0 1)) (le_max_of_le_left (norm_nonneg _)) (max_le (hM 1 0) (hM 1 1)))

theorem norm_det_mul_norm_det_inv (g : GL (Fin 2) Kv) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ * ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 := norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hn := norm_det_mul_norm_det_inv K v g
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ < 1 := lt_of_le_of_ne h1 hne
  exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2).ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) Kv}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) Kv} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem unipotentGL2_mem_iff (y : Kv) : unipotentGL2 y ∈ localIntegralSet K v ↔ ‖y‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero, norm_one]
  constructor
  · rintro ⟨h1, -⟩
    simpa using h1 0 1
  · intro hy
    refine ⟨fun i j => ?_, trivial⟩
    fin_cases i <;> fin_cases j <;> simp [hy]

end IntegralPoints

section Algebra

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_centralizer_iff {a b : Kvˣ} (hab : a ≠ b) (t : GL (Fin 2) Kv) :
    t ∈ localCentralizer K v (diagUnits2 a b) ↔
      (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0 := by
  rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  have hab' : (a : Kv) ≠ b := fun h => hab (Units.ext h)
  have hba : (b : Kv) - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab')
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 2) Kv => (g : Matrix (Fin 2) (Fin 2) Kv)) h
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    refine ⟨?_, ?_⟩
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, e01, mul_comm]
      exact (mul_eq_zero.1 this).resolve_right hba
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, mul_comm, e10]
      exact (mul_eq_zero.1 this).resolve_right hba
  · rintro ⟨h01, h10⟩
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem centralizer_entries {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0 ∧
      ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0 :=
  (mem_centralizer_iff K v hab _).1 t.2

theorem centralizer_diag_ne_zero {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 ∧
      ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := by
  obtain ⟨h01, h10⟩ := centralizer_entries K v hab t
  have hdet : ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 :=
    (Matrix.isUnits_det_units (t : GL (Fin 2) Kv)).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem centralizer_comm {a b : Kvˣ} (hab : a ≠ b) (s t : localCentralizer K v (diagUnits2 a b)) :
    s * t = t * s := by
  obtain ⟨s01, s10⟩ := centralizer_entries K v hab s
  obtain ⟨t01, t10⟩ := centralizer_entries K v hab t
  apply Subtype.ext
  apply Units.ext
  change ((s : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) * ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) * ((s : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, t01, t10, mul_comm]

theorem diagUnits2_mem_centralizer {a b : Kvˣ} (hab : a ≠ b) (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localCentralizer K v (diagUnits2 a b) := by
  rw [mem_centralizer_iff K v hab, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  simp

theorem centralizer_eq_diagUnits2 {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    (t : GL (Fin 2) Kv) =
      diagUnits2 (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).1)
        (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).2) := by
  obtain ⟨h01, h10⟩ := centralizer_entries K v hab t
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem diagUnits2_mul_unipotentGL2 (t₁ t₂ : Kvˣ) (y : Kv) :
    diagUnits2 t₁ t₂ * unipotentGL2 y = unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotentGL2_inv (y : Kv) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem coe_unipotent_conj (a b : Kvˣ) (y : Kv) :
    (((unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
      !![(a : Kv), ((a : Kv) - b) * y; 0, (b : Kv)] := by
  rw [unipotentGL2_inv, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem unipotent_conj_mem_iff (a b : Kvˣ) (y : Kv) :
    (unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y ∈ localIntegralSet K v ↔
      ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1 ∧ ‖((a : Kv) - b) * y‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, coe_unipotent_conj, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero, norm_mul]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : ‖(a : Kv)‖ ≤ 1 := by simpa using h1 0 0
    have hb : ‖(b : Kv)‖ ≤ 1 := by simpa using h1 1 1
    have hy : ‖(a : Kv) - b‖ * ‖y‖ ≤ 1 := by simpa using h1 0 1
    have ha1 : ‖(a : Kv)‖ = 1 := by
      by_contra hne
      exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (lt_of_le_of_ne ha hne) hb).ne h2
    exact ⟨ha1, by rwa [ha1, one_mul] at h2, hy⟩
  · rintro ⟨ha, hb, hy⟩
    refine ⟨fun i j => ?_, by rw [ha, hb, one_mul]⟩
    fin_cases i <;> fin_cases j
    · simpa using ha.le
    · simpa using hy
    · simp
    · simpa using hb.le

end Algebra

section Iwasawa

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_localIntegralSet_of_mem_integralSubgroup {g : GL (Fin 2) Kv}
    (hg : g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) Kv) : g ∈ localIntegralSet K v := by
  obtain ⟨k, rfl⟩ := hg
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2
  · rw [← map_inv]
    exact (((k⁻¹ : GL (Fin 2) (v.adicCompletionIntegers K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2

theorem iwasawa (x : GL (Fin 2) Kv) :
    ∃ (t₁ t₂ : Kvˣ) (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧
      x = diagUnits2 t₁ t₂ * unipotentGL2 y * k := by
  obtain ⟨b, k, hk, hb10, rfl⟩ :=
    LocalGL2.iwasawa_decomposition (v.adicCompletionIntegers K) Kv x
  have hdet : (b : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero] at hdet
  have h00 : (b : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (b : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11,
    (b : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0)⁻¹, k,
    mem_localIntegralSet_of_mem_integralSubgroup K v hk, ?_⟩
  congr 1
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb10]
  rw [mul_comm ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0), mul_assoc, inv_mul_cancel₀ h00, mul_one]

end Iwasawa

namespace WeightKit

open AutomorphicForm.LocalWeight

variable {F : Type*} [NormedField F]

theorem det_norm_pos (x : GL (Fin 2) F) : 0 < ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero

theorem row0_ne_zero (x : GL (Fin 2) F) :
    ¬ ((x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  exact (Matrix.isUnits_det_units x).ne_zero hdet

theorem topMax_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ := by
  rcases lt_or_ge 0 (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖) with h | h
  · exact h
  · exfalso
    have h0 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ 0 := (le_max_left _ _).trans h
    have h1 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ 0 := (le_max_right _ _).trans h
    exact row0_ne_zero x ⟨norm_le_zero_iff.mp h0, norm_le_zero_iff.mp h1⟩

theorem arg_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) / ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  div_pos (mul_pos (topMax_pos x) (AdelicHeight.rowMaxNorm_pos x)) (det_norm_pos x)

theorem continuous_weight : Continuous (weight : GL (Fin 2) F → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  unfold weight
  refine continuous_const.mul (Continuous.log ?_ fun x => (arg_pos x).ne')
  exact (((hc 0 0).max (hc 0 1)).mul ((hc 1 0).max (hc 1 1))).div hdet fun x => (det_norm_pos x).ne'

theorem weight_eq (x : GL (Fin 2) F) :
    weight x = 2 * Real.log
      (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        max ‖(x : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 1 1‖ /
        ‖(x : Matrix (Fin 2) (Fin 2) F).det‖) := rfl

theorem weight_diagUnits2_mul (t₁ t₂ : Fˣ) (x : GL (Fin 2) F) :
    weight (diagUnits2 t₁ t₂ * x) = weight x := by
  rw [weight_eq, weight_eq]
  congr 2
  have hM : ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0, (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1;
        (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0, (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hM, Matrix.det_fin_two_of]
  have h1 : 0 < ‖(t₁ : F)‖ := norm_pos_iff.2 t₁.ne_zero
  have h2 : 0 < ‖(t₂ : F)‖ := norm_pos_iff.2 t₂.ne_zero
  have hdet : (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1) -
      (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0) =
      (t₁ : F) * (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.det_fin_two]; ring
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul]
  rw [hdet, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ h1.le, ← mul_max_of_nonneg _ _ h2.le]
  field_simp

section Ultra

variable [IsUltrametricDist F]

theorem norm_mul_entry_le_rowMax (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) :
    ‖(M * N) i j‖ ≤ max ‖M i 0‖ ‖M i 1‖ := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 0 j)).trans (le_max_left _ _)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 1 j)).trans (le_max_right _ _)

theorem rowMax_mul_le (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i : Fin 2) :
    max ‖(M * N) i 0‖ ‖(M * N) i 1‖ ≤ max ‖M i 0‖ ‖M i 1‖ :=
  max_le (norm_mul_entry_le_rowMax M N hN i 0) (norm_mul_entry_le_rowMax M N hN i 1)

theorem rowMax_mul_eq (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1) (i : Fin 2) :
    max ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 1‖ =
      max ‖(x : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) i 1‖ := by
  refine le_antisymm ?_ ?_
  · rw [Units.val_mul]; exact rowMax_mul_le _ _ hk i
  · have hx : (x : Matrix (Fin 2) (Fin 2) F) = ((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    conv_lhs => rw [hx]
    exact rowMax_mul_le _ _ hk' i

theorem weight_mul_of_norm_le_one (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hdet : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ = 1) :
    weight (x * k) = weight x := by
  rw [weight_eq, weight_eq]
  have h0 := rowMax_mul_eq x k hk hk' 0
  have h1 := rowMax_mul_eq x k hk hk' 1
  rw [h0, h1, Units.val_mul, Matrix.det_mul, norm_mul, hdet, mul_one]

end Ultra

theorem weight_unipotentGL2 (y : F) : weight (unipotentGL2 y) = 2 * Real.log (max 1 ‖y‖) := by
  rw [weight_eq, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

end WeightKit

section Shells

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) Kv) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kv))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

theorem continuous_unipotentGL2' : Continuous (fun y : Kv => (unipotentGL2 y : GL (Fin 2) Kv)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun y : Kv => ((unipotentGL2 y : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv))
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun y : Kv => (((unipotentGL2 y)⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv)) =
        fun y => !![1, -y; 0, 1] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

def U (s : ℕ) : Set (GL (Fin 2) Kv) :=
  {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), ‖y‖ ≤ qv K v ^ s ∧ k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem mul_mem_U {s : ℕ} {y : Kv} {k : GL (Fin 2) Kv} (hy : ‖y‖ ≤ qv K v ^ s) (hk : k ∈ localIntegralSet K v) :
    unipotentGL2 y * k ∈ U K v s :=
  ⟨y, k, hy, hk, rfl⟩

theorem U_zero : U K v 0 = localIntegralSet K v := by
  ext x
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩
    rw [pow_zero] at hy
    exact mul_mem_localIntegralSet K v ((unipotentGL2_mem_iff K v y).2 hy) hk
  · intro hx
    refine ⟨0, x, by simp, hx, by rw [unipotentGL2_zero, one_mul]⟩

theorem U_mono (s : ℕ) : U K v s ⊆ U K v (s + 1) := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  exact ⟨y, k, hy.trans (pow_le_pow_right₀ (one_lt_qv K v).le (Nat.le_succ s)), hk, rfl⟩

theorem U_eq_image (s : ℕ) :
    U K v s = (fun p : Kv × GL (Fin 2) Kv => unipotentGL2 p.1 * p.2) ''
      ({y : Kv | ‖y‖ ≤ qv K v ^ s} ×ˢ localIntegralSet K v) := by
  ext x
  simp only [U, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists]
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩; exact ⟨y, k, ⟨hy, hk⟩, rfl⟩
  · rintro ⟨y, k, ⟨hy, hk⟩, rfl⟩; exact ⟨y, k, hy, hk, rfl⟩

theorem isCompact_U (s : ℕ) : IsCompact (U K v s) := by
  rw [U_eq_image]
  refine IsCompact.image (IsCompact.prod ?_ (isCompact_localIntegralSet K v)) ?_
  · have : {y : Kv | ‖y‖ ≤ qv K v ^ s} = Metric.closedBall 0 (qv K v ^ s) := by
      ext y; simp
    rw [this]
    exact isCompact_closedBall _ _
  · exact ((continuous_unipotentGL2' K v).comp continuous_fst).mul continuous_snd

theorem U_eq_iUnion (s : ℕ) :
    U K v s = ⋃ y : {y : Kv // ‖y‖ ≤ qv K v ^ s}, (fun k => unipotentGL2 (y : Kv) * k) '' localIntegralSet K v := by
  ext x
  simp only [U, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩; exact ⟨y, hy, k, hk, rfl⟩
  · rintro ⟨y, hy, k, hk, rfl⟩; exact ⟨y, k, hy, hk, rfl⟩

theorem isOpen_U (s : ℕ) : IsOpen (U K v s) := by
  rw [U_eq_iUnion]
  exact isOpen_iUnion fun y => (isOpenMap_mul_left _) _ (isOpen_localIntegralSet K v)

theorem measurableSet_U (s : ℕ) : MeasurableSet (U K v s) := (isOpen_U K v s).measurableSet

theorem norm_sub_le_one_of_eq {y y' : Kv} {k k' : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v)
    (hk' : k' ∈ localIntegralSet K v) (h : unipotentGL2 y * k = unipotentGL2 y' * k') : ‖y' - y‖ ≤ 1 := by
  have h2 : unipotentGL2 (y' - y) = k * k'⁻¹ := by
    rw [sub_eq_neg_add, unipotentGL2_add, ← unipotentGL2_inv K v, eq_mul_inv_iff_mul_eq, mul_assoc, ← h,
      ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← unipotentGL2_mem_iff K v, h2]
  exact mul_mem_localIntegralSet K v hk (inv_mem_localIntegralSet K v hk')

theorem norm_eq_of_not_mem {s : ℕ} {y : Kv} {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v)
    (hy : ‖y‖ ≤ qv K v ^ (s + 1)) (hx : unipotentGL2 y * k ∉ U K v s) : ‖y‖ = qv K v ^ (s + 1) := by
  refine le_antisymm hy ?_
  have hlt : qv K v ^ s < ‖y‖ := by
    by_contra hle
    exact hx (mul_mem_U K v (not_lt.1 hle) hk)
  have := zpow_add_one_le_norm_of_lt K v (n := (s : ℤ)) (by exact_mod_cast hlt)
  exact_mod_cast this

theorem weight_of_mem_diff {s : ℕ} {x : GL (Fin 2) Kv} (hx : x ∈ U K v (s + 1) \ U K v s) :
    LocalWeight.weight x = 2 * ((s + 1 : ℕ) : ℝ) * Real.log (qv K v) := by
  obtain ⟨⟨y, k, hy, hk, rfl⟩, hx2⟩ := hx
  have hn := norm_eq_of_not_mem K v hk hy hx2
  have hK := (mem_localIntegralSet_iff_norm K v k).1 hk
  have hK' := (mem_localIntegralSet_iff_norm K v k⁻¹).1 (inv_mem_localIntegralSet K v hk)
  rw [WeightKit.weight_mul_of_norm_le_one _ _ hK.1 hK'.1 hK.2, WeightKit.weight_unipotentGL2, hn,
    max_eq_right (one_le_pow₀ (one_lt_qv K v).le), Real.log_pow]
  ring

theorem weight_of_mem_U_zero {x : GL (Fin 2) Kv} (hx : x ∈ U K v 0) : LocalWeight.weight x = 0 := by
  obtain ⟨y, k, hy, hk, rfl⟩ := hx
  have hK := (mem_localIntegralSet_iff_norm K v k).1 hk
  have hK' := (mem_localIntegralSet_iff_norm K v k⁻¹).1 (inv_mem_localIntegralSet K v hk)
  rw [pow_zero] at hy
  rw [WeightKit.weight_mul_of_norm_le_one _ _ hK.1 hK'.1 hK.2, WeightKit.weight_unipotentGL2,
    max_eq_left hy, Real.log_one, mul_zero]

def wrep (ϖ : Kv) (s : ℕ) (c : kv K v) : Kv := ϖ⁻¹ ^ (s + 1) * rep K v c

def coset (ϖ : Kv) (s : ℕ) (c : kv K v) : Set (GL (Fin 2) Kv) :=
  (fun x => unipotentGL2 (wrep K v ϖ s c) * x) '' U K v s

theorem norm_pow_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (n : ℕ) : ‖ϖ ^ n‖ = (qv K v ^ n)⁻¹ := by
  rw [norm_pow, hϖ, inv_pow]

theorem norm_inv_pow_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (n : ℕ) : ‖ϖ⁻¹ ^ n‖ = qv K v ^ n := by
  rw [norm_pow, norm_inv, hϖ, inv_inv]

theorem uniformizer_ne_zero {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) : ϖ ≠ 0 := by
  intro h; rw [h, norm_zero] at hϖ; exact (inv_ne_zero (qv_ne_zero K v)) hϖ.symm

theorem coset_subset {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (s : ℕ) (c : kv K v) : coset K v ϖ s c ⊆ U K v (s + 1) := by
  rintro x ⟨x', ⟨y, k, hy, hk, rfl⟩, rfl⟩
  refine ⟨wrep K v ϖ s c + y, k, ?_, hk, by rw [unipotentGL2_add, mul_assoc]⟩
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [wrep, norm_mul, norm_inv_pow_uniformizer K v hϖ]
    exact mul_le_of_le_one_right (pow_nonneg (qv_pos K v).le _) (norm_rep_le_one K v c)
  · exact hy.trans (pow_le_pow_right₀ (one_lt_qv K v).le (Nat.le_succ s))

theorem U_succ_subset_iUnion {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (s : ℕ) :
    U K v (s + 1) ⊆ ⋃ c : kv K v, coset K v ϖ s c := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  have hϖ0 := uniformizer_ne_zero K v hϖ
  set z : Kv := ϖ ^ (s + 1) * y with hz
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_pow_uniformizer K v hϖ]
    calc (qv K v ^ (s + 1))⁻¹ * ‖y‖ ≤ (qv K v ^ (s + 1))⁻¹ * qv K v ^ (s + 1) :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.2 (pow_nonneg (qv_pos K v).le _))
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ (qv_ne_zero K v))
  set c : kv K v := IsLocalRing.residue (v.adicCompletionIntegers K) ⟨z, (mem_integers_iff_norm K v z).2 hz1⟩
    with hc
  have hzr : ‖z - rep K v c‖ ≤ (qv K v)⁻¹ :=
    (norm_lt_one_iff_le_inv K v _).1 (norm_sub_rep_lt_one K v hz1)
  have hy' : y = wrep K v ϖ s c + ϖ⁻¹ ^ (s + 1) * (z - rep K v c) := by
    rw [wrep, mul_sub, ← add_sub_assoc, add_sub_cancel_left, hz, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0,
      one_pow, one_mul]
  refine Set.mem_iUnion.2 ⟨c, ⟨unipotentGL2 (ϖ⁻¹ ^ (s + 1) * (z - rep K v c)) * k, ⟨_, k, ?_, hk, rfl⟩, ?_⟩⟩
  · rw [norm_mul, norm_inv_pow_uniformizer K v hϖ, pow_succ]
    calc qv K v ^ s * qv K v * ‖z - rep K v c‖ ≤ qv K v ^ s * qv K v * (qv K v)⁻¹ :=
          mul_le_mul_of_nonneg_left hzr (mul_nonneg (pow_nonneg (qv_pos K v).le _) (qv_pos K v).le)
      _ = qv K v ^ s := by rw [mul_assoc, mul_inv_cancel₀ (qv_ne_zero K v), mul_one]
  · change unipotentGL2 (wrep K v ϖ s c) * (unipotentGL2 (ϖ⁻¹ ^ (s + 1) * (z - rep K v c)) * k) = _
    rw [← mul_assoc, ← unipotentGL2_add, ← hy']

theorem U_succ_eq_iUnion {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (s : ℕ) :
    U K v (s + 1) = ⋃ c : kv K v, coset K v ϖ s c :=
  Set.Subset.antisymm (U_succ_subset_iUnion K v hϖ s) (Set.iUnion_subset fun c => coset_subset K v hϖ s c)

theorem pairwise_disjoint_coset {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) (s : ℕ) :
    Pairwise (Function.onFun Disjoint fun c : kv K v => coset K v ϖ s c) := by
  intro c c' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨x₁, ⟨y₁, k₁, hy₁, hk₁, rfl⟩, rfl⟩ ⟨x₂, ⟨y₂, k₂, hy₂, hk₂, rfl⟩, h⟩
  apply hne
  change unipotentGL2 (wrep K v ϖ s c') * (unipotentGL2 y₂ * k₂) =
    unipotentGL2 (wrep K v ϖ s c) * (unipotentGL2 y₁ * k₁) at h
  rw [← mul_assoc, ← unipotentGL2_add, ← mul_assoc, ← unipotentGL2_add] at h
  have h1 : ‖(wrep K v ϖ s c + y₁) - (wrep K v ϖ s c' + y₂)‖ ≤ 1 := norm_sub_le_one_of_eq K v hk₂ hk₁ h
  have h2 : ‖wrep K v ϖ s c - wrep K v ϖ s c'‖ ≤ qv K v ^ s := by
    have : wrep K v ϖ s c - wrep K v ϖ s c' =
        ((wrep K v ϖ s c + y₁) - (wrep K v ϖ s c' + y₂)) + (y₂ - y₁) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans (one_le_pow₀ (one_lt_qv K v).le)) ?_)
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy₂ (by rw [norm_neg]; exact hy₁))
  have h3 : ‖rep K v c - rep K v c'‖ ≤ (qv K v)⁻¹ := by
    have hw : wrep K v ϖ s c - wrep K v ϖ s c' = ϖ⁻¹ ^ (s + 1) * (rep K v c - rep K v c') := by
      simp only [wrep]; ring
    rw [hw, norm_mul, norm_inv_pow_uniformizer K v hϖ, pow_succ] at h2
    have hpos : 0 < qv K v ^ s * qv K v := mul_pos (pow_pos (qv_pos K v) _) (qv_pos K v)
    rw [mul_comm] at h2
    have h4 : ‖rep K v c - rep K v c'‖ * (qv K v ^ s * qv K v) ≤ (qv K v)⁻¹ * (qv K v ^ s * qv K v) :=
      calc ‖rep K v c - rep K v c'‖ * (qv K v ^ s * qv K v) ≤ qv K v ^ s := h2
        _ = (qv K v)⁻¹ * (qv K v ^ s * qv K v) := by
          rw [mul_comm (qv K v ^ s), ← mul_assoc, inv_mul_cancel₀ (qv_ne_zero K v), one_mul]
    exact le_of_mul_le_mul_right h4 hpos
  exact rep_eq_of_norm_sub_lt_one K v ((norm_lt_one_iff_le_inv K v _).2 h3)

theorem measure_coset (ϖ : Kv) (s : ℕ) (c : kv K v) : localHaar K v (coset K v ϖ s c) = localHaar K v (U K v s) := by
  rw [coset, Set.image_mul_left]
  exact measure_preimage_mul _ _ _

theorem measure_U_succ (s : ℕ) :
    localHaar K v (U K v (s + 1)) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) * localHaar K v (U K v s) := by
  obtain ⟨ϖ, hϖ⟩ := exists_norm_eq_inv K v
  rw [U_succ_eq_iUnion K v hϖ s, measure_iUnion (pairwise_disjoint_coset K v hϖ s)
    (fun c => by rw [coset, Set.image_mul_left]; exact measurableSet_preimage (measurable_const_mul _) (measurableSet_U K v s)),
    tsum_fintype]
  simp only [measure_coset]
  rw [Finset.sum_const, Finset.card_univ, card_kv, nsmul_eq_mul]

theorem measure_U (s : ℕ) : localHaar K v (U K v s) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ s := by
  induction s with
  | zero => rw [U_zero, pow_zero]; exact localHaar_localIntegralSet K v
  | succ s ih => rw [measure_U_succ, ih, pow_succ, mul_comm]

theorem measureReal_U (s : ℕ) : (localHaar K v).real (U K v s) = qv K v ^ s := by
  rw [measureReal_def, measure_U, ENNReal.toReal_pow, ENNReal.toReal_natCast]

theorem measure_U_lt_top (s : ℕ) : localHaar K v (U K v s) < ⊤ := by
  rw [measure_U]; exact ENNReal.pow_lt_top (ENNReal.natCast_lt_top _)

theorem integrableOn_weight_U (s : ℕ) : IntegrableOn LocalWeight.weight (U K v s) (localHaar K v) :=
  ContinuousOn.integrableOn_compact (isCompact_U K v s) WeightKit.continuous_weight.continuousOn

def shellSum (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (m + 1), (s : ℝ) * (qv K v ^ s - qv K v ^ s / qv K v)

theorem integral_weight_U (m : ℕ) :
    ∫ x in U K v m, LocalWeight.weight x ∂(localHaar K v) = 2 * Real.log (qv K v) * shellSum K v m := by
  induction m with
  | zero =>
    rw [shellSum, Finset.sum_range_one, Nat.cast_zero, zero_mul, mul_zero]
    rw [setIntegral_congr_fun (measurableSet_U K v 0) (fun x hx => weight_of_mem_U_zero K v hx)]
    simp
  | succ m ih =>
    have hsub := U_mono K v m
    have hsplit : ∫ x in U K v (m + 1), LocalWeight.weight x ∂(localHaar K v) =
        (∫ x in U K v m, LocalWeight.weight x ∂(localHaar K v)) +
          ∫ x in U K v (m + 1) \ U K v m, LocalWeight.weight x ∂(localHaar K v) := by
      rw [← setIntegral_union disjoint_sdiff_right ((measurableSet_U K v (m + 1)).diff (measurableSet_U K v m))
        (integrableOn_weight_U K v m) ((integrableOn_weight_U K v (m + 1)).mono_set Set.diff_subset),
        Set.union_diff_cancel hsub]
    have hshell : ∫ x in U K v (m + 1) \ U K v m, LocalWeight.weight x ∂(localHaar K v) =
        (qv K v ^ (m + 1) - qv K v ^ m) * (2 * ((m + 1 : ℕ) : ℝ) * Real.log (qv K v)) := by
      rw [setIntegral_congr_fun ((measurableSet_U K v (m + 1)).diff (measurableSet_U K v m))
        (fun x hx => weight_of_mem_diff K v hx), setIntegral_const, smul_eq_mul,
        measureReal_diff hsub (measurableSet_U K v m) (measure_U_lt_top K v _).ne,
        measureReal_U, measureReal_U]
    rw [hsplit, ih, hshell, shellSum, shellSum, Finset.sum_range_succ _ (m + 1), pow_succ,
      mul_div_assoc, div_self (qv_ne_zero K v), mul_one]
    ring

end Shells

section SectionFn

open scoped Classical

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

def Fγ (a b : Kvˣ) (x : GL (Fin 2) Kv) : ℂ :=
  (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 a b * x)

theorem Fγ_apply (a b : Kvˣ) (x : GL (Fin 2) Kv) :
    Fγ K v a b x = if x⁻¹ * diagUnits2 a b * x ∈ localIntegralSet K v then 1 else 0 := by
  rw [Fγ, Set.indicator_apply]

theorem Fγ_ne_zero_iff (a b : Kvˣ) (x : GL (Fin 2) Kv) :
    Fγ K v a b x ≠ 0 ↔ x⁻¹ * diagUnits2 a b * x ∈ localIntegralSet K v := by
  rw [Fγ_apply]; split_ifs with h <;> simp [h]

theorem Fγ_eq_one_of_mem {a b : Kvˣ} {x : GL (Fin 2) Kv} (h : x⁻¹ * diagUnits2 a b * x ∈ localIntegralSet K v) :
    Fγ K v a b x = 1 := by
  rw [Fγ_apply, if_pos h]

theorem norm_Fγ_le_one (a b : Kvˣ) (x : GL (Fin 2) Kv) : ‖Fγ K v a b x‖ ≤ 1 := by
  rw [Fγ_apply]; split_ifs <;> simp

theorem continuous_conj (γ : GL (Fin 2) Kv) : Continuous fun x : GL (Fin 2) Kv => x⁻¹ * γ * x :=
  (continuous_id.inv.mul continuous_const).mul continuous_id

theorem measurable_Fγ (a b : Kvˣ) : Measurable (Fγ K v a b) := by
  unfold Fγ
  have : (fun x : GL (Fin 2) Kv => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 a b * x)) =
      ((fun x : GL (Fin 2) Kv => x⁻¹ * diagUnits2 a b * x) ⁻¹' localIntegralSet K v).indicator fun _ => (1 : ℂ) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_preimage]
  rw [this]
  exact measurable_const.indicator
    (((isOpen_localIntegralSet K v).preimage (continuous_conj K v _)).measurableSet)

theorem Fγ_centralizer_mul {a b : Kvˣ} (t : localCentralizer K v (diagUnits2 a b)) (x : GL (Fin 2) Kv) :
    Fγ K v a b ((t : GL (Fin 2) Kv) * x) = Fγ K v a b x := by
  have ht : (t : GL (Fin 2) Kv) * diagUnits2 a b = diagUnits2 a b * t :=
    Subgroup.mem_centralizer_singleton_iff.1 t.2
  have key : ((t : GL (Fin 2) Kv))⁻¹ * (diagUnits2 a b * ((t : GL (Fin 2) Kv) * x)) = diagUnits2 a b * x := by
    rw [← mul_assoc (diagUnits2 a b), ← ht, mul_assoc, inv_mul_cancel_left]
  unfold Fγ
  congr 1
  rw [mul_inv_rev, mul_assoc x⁻¹, mul_assoc x⁻¹, mul_assoc ((t : GL (Fin 2) Kv))⁻¹, key, ← mul_assoc]

private theorem _root_.P2mUnitWeightK.diagUnits2_mul_diagUnits2 (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 (s₁ * t₁) (s₂ * t₂) : GL (Fin 2) Kv) := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

p2m_export "P2mUnitWeightK" "diagUnits2_mul_diagUnits2"

theorem diagUnits2_comm (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 t₁ t₂ * diagUnits2 s₁ s₂ : GL (Fin 2) Kv) := by
  rw [diagUnits2_mul_diagUnits2, diagUnits2_mul_diagUnits2, mul_comm s₁, mul_comm s₂]

theorem conj_mem_iff (a b t₁ t₂ : Kvˣ) (y : Kv) {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 a b * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈
        localIntegralSet K v ↔
      ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1 ∧ ‖((a : Kv) - b) * y‖ ≤ 1 := by
  have hcomm : (diagUnits2 t₁ t₂)⁻¹ * (diagUnits2 a b * diagUnits2 t₁ t₂) = (diagUnits2 a b : GL (Fin 2) Kv) := by
    rw [inv_mul_eq_iff_eq_mul, diagUnits2_comm]
  have hrw : (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 a b * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) =
      k⁻¹ * ((unipotentGL2 y)⁻¹ * ((diagUnits2 t₁ t₂)⁻¹ * (diagUnits2 a b * diagUnits2 t₁ t₂)) * unipotentGL2 y) * k := by
    simp only [mul_inv_rev, mul_assoc]
  rw [hrw, hcomm, mul_mem_localIntegralSet_iff_left K v hk,
    mul_mem_localIntegralSet_iff_right K v (inv_mem_localIntegralSet K v hk), unipotent_conj_mem_iff]

def NK : Set (GL (Fin 2) Kv) := {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

private theorem _root_.P2mUnitWeightK.diagUnits2_mem_iff (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localIntegralSet K v ↔ ‖(t₁ : Kv)‖ = 1 ∧ ‖(t₂ : Kv)‖ = 1 := by
  have := unipotent_conj_mem_iff K v t₁ t₂ 0
  rw [unipotentGL2_zero, inv_one, one_mul, mul_one] at this
  rw [this]
  simp

p2m_export "P2mUnitWeightK" "diagUnits2_mem_iff"

theorem diag_mul_mem_NK_iff (t₁ t₂ : Kvˣ) (y : Kv) {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    diagUnits2 t₁ t₂ * unipotentGL2 y * k ∈ NK K v ↔ diagUnits2 t₁ t₂ ∈ localIntegralSet K v := by
  rw [diagUnits2_mul_unipotentGL2]
  constructor
  · rintro ⟨y', k', hk', h⟩

    have h2 : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      calc (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k
          = (unipotentGL2 y')⁻¹ * (unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k) := by
            simp only [mul_assoc]
        _ = k' := by rw [h, inv_mul_cancel_left]
    have hmem : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ ∈
        localIntegralSet K v := by
      rw [h2]; exact mul_mem_localIntegralSet K v hk' (inv_mem_localIntegralSet K v hk)
    rw [unipotentGL2_inv, ← unipotentGL2_add] at hmem
    set z : Kv := -y' + (t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)
    have hM : ((unipotentGL2 z * diagUnits2 t₁ t₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
        !![(t₁ : Kv), z * (t₂ : Kv); 0, (t₂ : Kv)] := by
      rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [mem_localIntegralSet_iff_norm, hM, Matrix.det_fin_two_of] at hmem
    obtain ⟨h1, hdet⟩ := hmem
    simp only [mul_zero, sub_zero, norm_mul] at hdet
    have ha : ‖(t₁ : Kv)‖ ≤ 1 := by simpa using h1 0 0
    have hb : ‖(t₂ : Kv)‖ ≤ 1 := by simpa using h1 1 1
    have ha1 : ‖(t₁ : Kv)‖ = 1 := by
      by_contra hne
      exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (lt_of_le_of_ne ha hne) hb).ne hdet
    rw [diagUnits2_mem_iff]
    exact ⟨ha1, by rwa [ha1, one_mul] at hdet⟩
  · intro hd
    exact ⟨_, diagUnits2 t₁ t₂ * k, mul_mem_localIntegralSet K v hd hk, by rw [mul_assoc]⟩

variable {K v}

theorem mem_U_iff_of_units {a b : Kvˣ} (ha : ‖(a : Kv)‖ = 1) (hb : ‖(b : Kv)‖ = 1) {m : ℕ}
    (hm : ‖(a : Kv) - b‖ = (qv K v ^ m)⁻¹) (x : GL (Fin 2) Kv) :
    x ∈ U K v m ↔ x ∈ NK K v ∧ x⁻¹ * diagUnits2 a b * x ∈ localIntegralSet K v := by
  have hq : 0 < qv K v ^ m := pow_pos (qv_pos K v) _
  have key : ∀ y : Kv, ‖((a : Kv) - b) * y‖ ≤ 1 ↔ ‖y‖ ≤ qv K v ^ m := fun y => by
    rw [norm_mul, hm, inv_mul_le_iff₀ hq, mul_one]
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩
    refine ⟨⟨y, k, hk, rfl⟩, ?_⟩
    have := (conj_mem_iff K v a b 1 1 y hk).2 ⟨ha, hb, (key y).2 hy⟩
    have h11 : (diagUnits2 1 1 : GL (Fin 2) Kv) = 1 := by
      apply Units.ext
      rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [h11] using this
  · rintro ⟨⟨y, k, hk, rfl⟩, hx⟩
    have h11 : (diagUnits2 1 1 : GL (Fin 2) Kv) = 1 := by
      apply Units.ext
      rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hx' : (diagUnits2 1 1 * unipotentGL2 y * k)⁻¹ * diagUnits2 a b * (diagUnits2 1 1 * unipotentGL2 y * k) ∈
        localIntegralSet K v := by simpa [h11] using hx
    obtain ⟨-, -, hy⟩ := (conj_mem_iff K v a b 1 1 y hk).1 hx'
    exact ⟨y, k, (key y).1 hy, hk, rfl⟩

theorem Fγ_eq_zero_of_not_units {a b : Kvˣ} (h : ¬ (‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1)) (x : GL (Fin 2) Kv) :
    Fγ K v a b x = 0 := by
  by_contra hne
  rw [← Ne, Fγ_ne_zero_iff] at hne
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa K v x
  obtain ⟨ha, hb, -⟩ := (conj_mem_iff K v a b t₁ t₂ y hk).1 hne
  exact h ⟨ha, hb⟩

variable (K v)

theorem isClosed_centralizer (γ : GL (Fin 2) Kv) : IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) Kv)) :
    Set (GL (Fin 2) Kv)) := by
  have : ((localCentralizer K v γ : Subgroup (GL (Fin 2) Kv)) : Set (GL (Fin 2) Kv)) =
      {x | x * γ = γ * x} := by
    ext x; exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem isInvInvariant_of_comm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → G)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

theorem integral_indicator_U_translate {a b : Kvˣ} (hab : a ≠ b) (ha : ‖(a : Kv)‖ = 1) (hb : ‖(b : Kv)‖ = 1)
    {m : ℕ} (hm : ‖(a : Kv) - b‖ = (qv K v ^ m)⁻¹)
    (τ : @Measure (localCentralizer K v (diagUnits2 a b)) (localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} = 1)
    (x : GL (Fin 2) Kv) (hx : x⁻¹ * diagUnits2 a b * x ∈ localIntegralSet K v) :
    (letI := localCentralizerBorel K v (diagUnits2 a b)
     ∫ t : localCentralizer K v (diagUnits2 a b),
        (U K v m).indicator (fun _ => (1 : ℝ)) ((t : GL (Fin 2) Kv) * x) ∂τ) = 1 := by
  letI := localCentralizerBorel K v (diagUnits2 a b)
  haveI : BorelSpace (localCentralizer K v (diagUnits2 a b)) := ⟨rfl⟩
  haveI := hτ
  haveI : τ.IsMulRightInvariant :=
    isMulRightInvariant_of_comm _ (centralizer_comm K v hab) τ
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa K v x
  set d : localCentralizer K v (diagUnits2 a b) := ⟨diagUnits2 t₁ t₂, diagUnits2_mem_centralizer K v hab t₁ t₂⟩
    with hd

  have hset : ∀ t : localCentralizer K v (diagUnits2 a b),
      (t : GL (Fin 2) Kv) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈ U K v m ↔
        ((t * d : localCentralizer K v (diagUnits2 a b)) : GL (Fin 2) Kv) ∈ localIntegralSet K v := by
    intro t
    have htd : ((t * d : localCentralizer K v (diagUnits2 a b)) : GL (Fin 2) Kv) = (t : GL (Fin 2) Kv) * diagUnits2 t₁ t₂ := rfl
    rw [mem_U_iff_of_units ha hb hm, htd, centralizer_eq_diagUnits2 K v hab t, diagUnits2_mul_diagUnits2]
    have hassoc : diagUnits2 (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).1)
          (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).2) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) =
        diagUnits2 (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).1 * t₁)
          (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).2 * t₂) * unipotentGL2 y * k := by
      rw [← mul_assoc, ← mul_assoc, diagUnits2_mul_diagUnits2]
    rw [hassoc, diag_mul_mem_NK_iff K v _ _ y hk, and_iff_left_iff_imp]
    intro _
    rw [conj_mem_iff K v a b _ _ y hk]
    have hx' := (conj_mem_iff K v a b t₁ t₂ y hk).1 hx
    exact hx'
  have hfun : (fun t : localCentralizer K v (diagUnits2 a b) =>
        (U K v m).indicator (fun _ => (1 : ℝ)) ((t : GL (Fin 2) Kv) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k))) =
      ((fun t => t * d) ⁻¹' {t : localCentralizer K v (diagUnits2 a b) | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v}).indicator
        fun _ => (1 : ℝ) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq, hset t]
  have hmeas : MeasurableSet {t : localCentralizer K v (diagUnits2 a b) | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} :=
    ((isOpen_localIntegralSet K v).preimage continuous_subtype_val).measurableSet
  rw [hfun, integral_indicator_const _ (measurableSet_preimage (measurable_mul_const d) hmeas), smul_eq_mul, mul_one,
    measureReal_def, measure_preimage_mul_right, hτ1, ENNReal.toReal_one]

end SectionFn

section Main

open scoped Classical

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

theorem m_nonneg_of_units {a b : Kvˣ} (ha : ‖(a : Kv)‖ = 1) (hb : ‖(b : Kv)‖ = 1) {m : ℤ}
    (hm : ‖(a : Kv) - b‖ = qv K v ^ (-m)) : 0 ≤ m := by
  have h1 : ‖(a : Kv) - b‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.le (by rw [norm_neg]; exact hb.le))
  rw [hm] at h1
  by_contra hlt
  have hlt' : m < 0 := lt_of_not_ge hlt
  have : (1 : ℝ) < qv K v ^ (-m) := one_lt_zpow₀ (one_lt_qv K v) (by omega)
  exact absurd h1 (not_le.2 this)

theorem main_units {a b : Kvˣ} (hab : a ≠ b) (ha : ‖(a : Kv)‖ = 1) (hb : ‖(b : Kv)‖ = 1) (m : ℤ)
    (hm : ‖(a : Kv) - b‖ = qv K v ^ (-m))
    (τ : @Measure (localCentralizer K v (diagUnits2 a b)) (localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) J) :
    J = ((2 * Real.log (qv K v) * shellSum K v m.toNat : ℝ) : ℂ) := by
  letI := localCentralizerBorel K v (diagUnits2 a b)
  haveI : BorelSpace (localCentralizer K v (diagUnits2 a b)) := ⟨rfl⟩
  haveI := hτ
  haveI : τ.IsInvInvariant :=
    isInvInvariant_of_comm _ (isClosed_centralizer K v _) (centralizer_comm K v hab) τ
  have hm0 := m_nonneg_of_units K v ha hb hm
  have hm' : ‖(a : Kv) - b‖ = (qv K v ^ m.toNat)⁻¹ := by
    rw [hm, ← zpow_natCast, Int.toNat_of_nonneg hm0, zpow_neg]
  obtain ⟨s, ⟨hs0, hsm, hsc, hs1⟩, hJs⟩ := hJ

  set s₀ : GL (Fin 2) Kv → ℝ := (U K v m.toNat).indicator fun _ => (1 : ℝ) with hs₀
  have hs₀' : (∀ x, 0 ≤ s₀ x) ∧ Measurable s₀ ∧ HasCompactSupport s₀ ∧
      ∀ x, Fγ K v a b x ≠ 0 →
        ∫ t : localCentralizer K v (diagUnits2 a b), s₀ ((t : GL (Fin 2) Kv) * x) ∂τ = 1 := by
    refine ⟨fun x => ?_, measurable_const.indicator (measurableSet_U K v _),
      HasCompactSupport.intro (isCompact_U K v m.toNat) fun x hx => Set.indicator_of_notMem hx _, fun x hx => ?_⟩
    · rw [hs₀, Set.indicator_apply]; split_ifs <;> simp
    · exact integral_indicator_U_translate K v hab ha hb hm' τ hτ hτ1 x ((Fγ_ne_zero_iff K v a b x).1 hx)
  have hs' : (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      ∀ x, Fγ K v a b x ≠ 0 →
        ∫ t : localCentralizer K v (diagUnits2 a b), s ((t : GL (Fin 2) Kv) * x) ∂τ = 1 :=
    ⟨hs0, hsm, hsc, fun x hx => hs1 x hx⟩
  have hind := (MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
    (localCentralizer K v (diagUnits2 a b)) (isClosed_centralizer K v _) (localHaar K v) τ
    (Fγ K v a b) (measurable_Fγ K v a b) ⟨1, norm_Fγ_le_one K v a b⟩ (fun t x => Fγ_centralizer_mul K v t x)
    LocalWeight.weight WeightKit.continuous_weight
    (fun t x => by rw [centralizer_eq_diagUnits2 K v hab t]; exact WeightKit.weight_diagUnits2_mul _ _ x)
    s s₀ hs' hs₀').2

  have hval : ∫ x, Fγ K v a b x * (LocalWeight.weight x : ℂ) * (s₀ x : ℂ) ∂(localHaar K v) =
      ((2 * Real.log (qv K v) * shellSum K v m.toNat : ℝ) : ℂ) := by
    have hfun : (fun x => Fγ K v a b x * (LocalWeight.weight x : ℂ) * (s₀ x : ℂ)) =
        (U K v m.toNat).indicator fun x => (LocalWeight.weight x : ℂ) := by
      funext x
      by_cases hx : x ∈ U K v m.toNat
      · rw [Set.indicator_of_mem hx, hs₀, Set.indicator_of_mem hx,
          Fγ_eq_one_of_mem K v ((mem_U_iff_of_units ha hb hm' x).1 hx).2]
        simp
      · rw [Set.indicator_of_notMem hx, hs₀, Set.indicator_of_notMem hx]
        simp
    rw [hfun, integral_indicator (measurableSet_U K v _), integral_complex_ofReal, integral_weight_U]
  change J = ∫ x, Fγ K v a b x * (LocalWeight.weight x : ℂ) * (s x : ℂ) ∂(localHaar K v) at hJs
  rw [hJs, hind, hval]

theorem main_not_units {a b : Kvˣ} (h : ¬ (‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1))
    (τ : @Measure (localCentralizer K v (diagUnits2 a b)) (localCentralizerBorel K v (diagUnits2 a b)))
    (J : ℂ)
    (hJ : IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) J) :
    J = 0 := by
  obtain ⟨s, -, hJs⟩ := hJ
  change J = ∫ x, Fγ K v a b x * (LocalWeight.weight x : ℂ) * (s x : ℂ) ∂(localHaar K v) at hJs
  rw [hJs]
  simp [Fγ_eq_zero_of_not_units h]

end Main

end P2mUnitWeightK
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter Set
open scoped NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mInertUnitE2

open AutomorphicForm

section Norms

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private abbrev _root_.P2mInertUnitE2.qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

p2m_export "P2mInertUnitE2" "qv"
private theorem _root_.P2mInertUnitE2.one_lt_qv : 1 < qv K v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

p2m_export "P2mInertUnitE2" "one_lt_qv"
private theorem _root_.P2mInertUnitE2.qv_pos : 0 < qv K v := lt_trans zero_lt_one (one_lt_qv K v)

p2m_export "P2mInertUnitE2" "qv_pos"
private theorem _root_.P2mInertUnitE2.qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

p2m_export "P2mInertUnitE2" "qv_ne_zero"
theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv K v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

private theorem _root_.P2mInertUnitE2.norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hx
    exact Or.inr ⟨k, hk⟩

p2m_export "P2mInertUnitE2" "norm_eq_zero_or_zpow"

theorem v_eq_exp_of_norm_eq_zpow {x : v.adicCompletion K} {k : ℤ} (h : ‖x‖ = qv K v ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (qv_pos K v) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (qv_pos K v) (one_lt_qv K v).ne' h
  rw [hv, hk]

theorem norm_eq_zpow_of_v_eq_exp {x : v.adicCompletion K} {k : ℤ}
    (h : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k) : ‖x‖ = qv K v ^ k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at h
    exact WithZero.coe_ne_zero h.symm
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hv] at h
  have : k' = k := WithZero.exp_injective h
  rw [hk', this]

theorem norm_eq_one_iff_v (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  constructor
  · intro h
    have := v_eq_exp_of_norm_eq_zpow K v (k := 0) (by rw [h, zpow_zero])
    rwa [WithZero.exp_zero] at this
  · intro h
    have := norm_eq_zpow_of_v_eq_exp K v (k := 0) (by rw [h, WithZero.exp_zero])
    rwa [zpow_zero] at this

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

private theorem _root_.P2mInertUnitE2.exists_norm_eq_inv : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  exact ⟨x, by rw [norm_eq_zpow_of_v_eq_exp K v hx, zpow_neg, zpow_one]⟩

p2m_export "P2mInertUnitE2" "exists_norm_eq_inv"
end Norms
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section IntegralPoints

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_mul_max (M : Matrix (Fin 2) (Fin 2) Kv) :
    ‖M.det‖ ≤ max ‖M 0 0‖ ‖M 0 1‖ * max ‖M 1 0‖ ‖M 1 1‖ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 :=
  (norm_det_le_mul_max K v M).trans
    (mul_le_one₀ (max_le (hM 0 0) (hM 0 1)) (le_max_of_le_left (norm_nonneg _)) (max_le (hM 1 0) (hM 1 1)))

theorem norm_det_mul_norm_det_inv (g : GL (Fin 2) Kv) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ * ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 := norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hn := norm_det_mul_norm_det_inv K v g
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ < 1 := lt_of_le_of_ne h1 hne
  exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2).ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) Kv}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) Kv} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem upper_mem_iff {g : GL (Fin 2) Kv} {A B D : Kv}
    (hg : (g : Matrix (Fin 2) (Fin 2) Kv) = !![A, B; 0, D]) :
    g ∈ localIntegralSet K v ↔ ‖A‖ = 1 ∧ ‖D‖ = 1 ∧ ‖B‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, hg, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero, norm_mul]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : ‖A‖ ≤ 1 := by simpa using h1 0 0
    have hb : ‖D‖ ≤ 1 := by simpa using h1 1 1
    have hy : ‖B‖ ≤ 1 := by simpa using h1 0 1
    have ha1 : ‖A‖ = 1 := by
      by_contra hne
      exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (lt_of_le_of_ne ha hne) hb).ne h2
    exact ⟨ha1, by rwa [ha1, one_mul] at h2, hy⟩
  · rintro ⟨ha, hb, hy⟩
    refine ⟨fun i j => ?_, by rw [ha, hb, one_mul]⟩
    fin_cases i <;> fin_cases j
    · simpa using ha.le
    · simpa using hy
    · simp
    · simpa using hb.le

theorem unipotentGL2_mem_iff (y : Kv) : unipotentGL2 y ∈ localIntegralSet K v ↔ ‖y‖ ≤ 1 := by
  rw [upper_mem_iff K v (A := 1) (B := y) (D := 1) (unipotentGL2_coe y)]
  simp

theorem diagUnits2_mem_iff (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localIntegralSet K v ↔ ‖(t₁ : Kv)‖ = 1 ∧ ‖(t₂ : Kv)‖ = 1 := by
  rw [upper_mem_iff K v (A := (t₁ : Kv)) (B := 0) (D := (t₂ : Kv))
    (by rw [LanglandsTunnell.CubicInduction.coe_diagUnits2])]
  simp

end IntegralPoints
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Algebra

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_centralizer_iff {a b : Kvˣ} (hab : a ≠ b) (t : GL (Fin 2) Kv) :
    t ∈ localCentralizer K v (diagUnits2 a b) ↔
      (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0 := by
  rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  have hab' : (a : Kv) ≠ b := fun h => hab (Units.ext h)
  have hba : (b : Kv) - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab')
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 2) Kv => (g : Matrix (Fin 2) (Fin 2) Kv)) h
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    refine ⟨?_, ?_⟩
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, e01, mul_comm]
      exact (mul_eq_zero.1 this).resolve_right hba
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, mul_comm, e10]
      exact (mul_eq_zero.1 this).resolve_right hba
  · rintro ⟨h01, h10⟩
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem diag_ne_zero_of_offdiag {t : GL (Fin 2) Kv} (h01 : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0) :
    (t : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 ∧ (t : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := by
  have hdet : (t : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 := (Matrix.isUnits_det_units t).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem eq_diagUnits2_of_offdiag {t : GL (Fin 2) Kv} (h01 : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0) :
    t = diagUnits2 (Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).1)
      (Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).2) := by
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

private theorem _root_.P2mInertUnitE2.diagUnits2_mem_centralizer {a b : Kvˣ} (hab : a ≠ b) (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localCentralizer K v (diagUnits2 a b) := by
  rw [mem_centralizer_iff K v hab, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  simp

p2m_export "P2mInertUnitE2" "diagUnits2_mem_centralizer"

theorem diagUnits2_mul_unipotentGL2 (t₁ t₂ : Kvˣ) (y : Kv) :
    diagUnits2 t₁ t₂ * unipotentGL2 y = unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotentGL2_inv (y : Kv) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem diagUnits2_mul_diagUnits2 (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 (s₁ * t₁) (s₂ * t₂) : GL (Fin 2) Kv) := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_inv (t₁ t₂ : Kvˣ) : (diagUnits2 t₁ t₂ : GL (Fin 2) Kv)⁻¹ = diagUnits2 t₁⁻¹ t₂⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, diagUnits2_mul_diagUnits2, inv_mul_cancel, inv_mul_cancel]
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coe_unipotent_twist_conj (A D : Kvˣ) (y y' : Kv) :
    (((unipotentGL2 y)⁻¹ * diagUnits2 A D * unipotentGL2 y' : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
      !![(A : Kv), (A : Kv) * y' - D * y; 0, (D : Kv)] := by
  rw [unipotentGL2_inv, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem map_diagUnits2 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (s t : Rˣ) :
    Matrix.GeneralLinearGroup.map f (diagUnits2 s t) =
      diagUnits2 (Units.map (f : R →* S) s) (Units.map (f : R →* S) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem map_unipotentGL2 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : R) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (unipotentGL2 y) = unipotentGL2 (f y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Algebra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Iwasawa

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_localIntegralSet_of_mem_integralSubgroup {g : GL (Fin 2) Kv}
    (hg : g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) Kv) : g ∈ localIntegralSet K v := by
  obtain ⟨k, rfl⟩ := hg
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2
  · rw [← map_inv]
    exact (((k⁻¹ : GL (Fin 2) (v.adicCompletionIntegers K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2

theorem iwasawa (x : GL (Fin 2) Kv) :
    ∃ (t₁ t₂ : Kvˣ) (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧
      x = diagUnits2 t₁ t₂ * unipotentGL2 y * k := by
  obtain ⟨b, k, hk, hb10, rfl⟩ :=
    LocalGL2.iwasawa_decomposition (v.adicCompletionIntegers K) Kv x
  have hdet : (b : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero] at hdet
  have h00 : (b : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (b : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11,
    (b : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0)⁻¹, k,
    mem_localIntegralSet_of_mem_integralSubgroup K v hk, ?_⟩
  congr 1
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb10]
  rw [mul_comm ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0), mul_assoc, inv_mul_cancel₀ h00, mul_one]

end Iwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

namespace WeightKit

open AutomorphicForm.LocalWeight

variable {F : Type*} [NormedField F]

theorem det_norm_pos (x : GL (Fin 2) F) : 0 < ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero

theorem row0_ne_zero (x : GL (Fin 2) F) :
    ¬ ((x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  exact (Matrix.isUnits_det_units x).ne_zero hdet

theorem topMax_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ := by
  rcases lt_or_ge 0 (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖) with h | h
  · exact h
  · exfalso
    have h0 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ 0 := (le_max_left _ _).trans h
    have h1 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ 0 := (le_max_right _ _).trans h
    exact row0_ne_zero x ⟨norm_le_zero_iff.mp h0, norm_le_zero_iff.mp h1⟩

theorem arg_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) / ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  div_pos (mul_pos (topMax_pos x) (AdelicHeight.rowMaxNorm_pos x)) (det_norm_pos x)

theorem continuous_weight : Continuous (weight : GL (Fin 2) F → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  unfold weight
  refine continuous_const.mul (Continuous.log ?_ fun x => (arg_pos x).ne')
  exact (((hc 0 0).max (hc 0 1)).mul ((hc 1 0).max (hc 1 1))).div hdet fun x => (det_norm_pos x).ne'

theorem weight_eq (x : GL (Fin 2) F) :
    weight x = 2 * Real.log
      (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        max ‖(x : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 1 1‖ /
        ‖(x : Matrix (Fin 2) (Fin 2) F).det‖) := rfl

theorem weight_diagUnits2_mul (t₁ t₂ : Fˣ) (x : GL (Fin 2) F) :
    weight (diagUnits2 t₁ t₂ * x) = weight x := by
  rw [weight_eq, weight_eq]
  congr 2
  have hM : ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0, (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1;
        (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0, (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hM, Matrix.det_fin_two_of]
  have h1 : 0 < ‖(t₁ : F)‖ := norm_pos_iff.2 t₁.ne_zero
  have h2 : 0 < ‖(t₂ : F)‖ := norm_pos_iff.2 t₂.ne_zero
  have hdet : (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1) -
      (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0) =
      (t₁ : F) * (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.det_fin_two]; ring
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul]
  rw [hdet, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ h1.le, ← mul_max_of_nonneg _ _ h2.le]
  field_simp

section Ultra

variable [IsUltrametricDist F]

theorem norm_mul_entry_le_rowMax (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) :
    ‖(M * N) i j‖ ≤ max ‖M i 0‖ ‖M i 1‖ := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 0 j)).trans (le_max_left _ _)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 1 j)).trans (le_max_right _ _)

theorem rowMax_mul_le (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i : Fin 2) :
    max ‖(M * N) i 0‖ ‖(M * N) i 1‖ ≤ max ‖M i 0‖ ‖M i 1‖ :=
  max_le (norm_mul_entry_le_rowMax M N hN i 0) (norm_mul_entry_le_rowMax M N hN i 1)

theorem rowMax_mul_eq (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1) (i : Fin 2) :
    max ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 1‖ =
      max ‖(x : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) i 1‖ := by
  refine le_antisymm ?_ ?_
  · rw [Units.val_mul]; exact rowMax_mul_le _ _ hk i
  · have hx : (x : Matrix (Fin 2) (Fin 2) F) = ((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    conv_lhs => rw [hx]
    exact rowMax_mul_le _ _ hk' i

theorem weight_mul_of_norm_le_one (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hdet : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ = 1) :
    weight (x * k) = weight x := by
  rw [weight_eq, weight_eq]
  have h0 := rowMax_mul_eq x k hk hk' 0
  have h1 := rowMax_mul_eq x k hk hk' 1
  rw [h0, h1, Units.val_mul, Matrix.det_mul, norm_mul, hdet, mul_one]

end Ultra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

theorem weight_unipotentGL2 (y : F) : weight (unipotentGL2 y) = 2 * Real.log (max 1 ‖y‖) := by
  rw [weight_eq, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

end WeightKit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Instances

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) Kv) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kv))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem continuous_unipotentGL2' : Continuous (fun y : Kv => (unipotentGL2 y : GL (Fin 2) Kv)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun y : Kv => ((unipotentGL2 y : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv))
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun y : Kv => (((unipotentGL2 y)⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv)) =
        fun y => !![1, -y; 0, 1] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem weight_unipotentGL2_mul {y : Kv} {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    LocalWeight.weight (unipotentGL2 y * k) = 2 * Real.log (max 1 ‖y‖) := by
  have hK := (mem_localIntegralSet_iff_norm K v k).1 hk
  have hK' := (mem_localIntegralSet_iff_norm K v k⁻¹).1 (inv_mem_localIntegralSet K v hk)
  rw [WeightKit.weight_mul_of_norm_le_one _ _ hK.1 hK'.1 hK.2, WeightKit.weight_unipotentGL2]

theorem norm_sub_le_one_of_eq {y y' : Kv} {k k' : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v)
    (hk' : k' ∈ localIntegralSet K v) (h : unipotentGL2 y * k = unipotentGL2 y' * k') : ‖y' - y‖ ≤ 1 := by
  have h2 : unipotentGL2 (y' - y) = k * k'⁻¹ := by
    rw [sub_eq_neg_add, unipotentGL2_add, ← unipotentGL2_inv K v, eq_mul_inv_iff_mul_eq, mul_assoc, ← h,
      ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← unipotentGL2_mem_iff K v, h2]
  exact mul_mem_localIntegralSet K v hk (inv_mem_localIntegralSet K v hk')

def NK : Set (GL (Fin 2) Kv) := {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem diag_mul_mem_NK_iff (t₁ t₂ : Kvˣ) (y : Kv) {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    diagUnits2 t₁ t₂ * unipotentGL2 y * k ∈ NK K v ↔ diagUnits2 t₁ t₂ ∈ localIntegralSet K v := by
  rw [diagUnits2_mul_unipotentGL2]
  constructor
  · rintro ⟨y', k', hk', h⟩
    have h2 : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      calc (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k
          = (unipotentGL2 y')⁻¹ * (unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k) := by
            simp only [mul_assoc]
        _ = k' := by rw [h, inv_mul_cancel_left]
    have hmem : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ ∈
        localIntegralSet K v := by
      rw [h2]; exact mul_mem_localIntegralSet K v hk' (inv_mem_localIntegralSet K v hk)
    rw [unipotentGL2_inv, ← unipotentGL2_add] at hmem
    set z : Kv := -y' + (t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)
    have hM : ((unipotentGL2 z * diagUnits2 t₁ t₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
        !![(t₁ : Kv), z * (t₂ : Kv); 0, (t₂ : Kv)] := by
      rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨ha, hb, -⟩ := (upper_mem_iff K v hM).1 hmem
    exact (diagUnits2_mem_iff K v t₁ t₂).2 ⟨ha, hb⟩
  · intro hd
    exact ⟨_, diagUnits2 t₁ t₂ * k, mul_mem_localIntegralSet K v hd hk, by rw [mul_assoc]⟩

end Instances
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem liesOver : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : Kv) :
    (Valued.v (algebraMap Kv Lw x) : WithZero (Multiplicative ℤ)) = Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem norm_algebraMap_eq_one_iff (x : Kv) : ‖algebraMap Kv Lw x‖ = 1 ↔ ‖x‖ = 1 := by
  rw [norm_eq_one_iff_v, norm_eq_one_iff_v, v_algebraMap K L v w hw]

theorem norm_algebraMap_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) :
    ‖algebraMap Kv Lw ϖ‖ = (qv L w.1)⁻¹ := by
  have h1 := v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg, zpow_one])
  rw [← v_algebraMap K L v w hw] at h1
  rw [norm_eq_zpow_of_v_eq_exp L w.1 h1, zpow_neg, zpow_one]

theorem exists_eq_algebraMap_mul_unit {y : Lw} (hy : y ≠ 0) :
    ∃ x : Kv, x ≠ 0 ∧ (Valued.v (y * (algebraMap Kv Lw x)⁻¹) : WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

theorem qv_w_eq_pow : qv L w.1 = qv K v ^ Module.finrank Kv Lw := by
  have hef := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    have h2 : HeightOneSpectrum.under (𝓞 K) w.1 = v := w.2
    have h3 := hw
    rw [h2] at h3
    exact h3
  rw [hw', one_mul] at hef
  haveI := liesOver K L v w
  unfold qv
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hef]
  push_cast
  rfl

omit hw in

theorem isIntegral_of_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

omit hw in

theorem mem_of_isIntegral {y : Lw} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

variable (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

omit hw in

theorem theta_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  exact (isIntegral_of_mem K L v w hy).map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

omit hw in

theorem v_theta_eq_one {y : Lw} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) :
    (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : θ y ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hy.le)
  have h2 : θ y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hy, inv_one]))
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h3 : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ θ.injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

theorem v_theta (y : Lw) : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hy
  have ha0 : algebraMap Kv Lw x ≠ 0 := (map_ne_zero _).2 hx0
  have hy' : y = (y * (algebraMap Kv Lw x)⁻¹) * algebraMap Kv Lw x := by
    rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  conv_lhs => rw [hy', map_mul, AlgEquiv.commutes, map_mul, v_theta_eq_one K L v w θ hu]
  conv_rhs => rw [hy', map_mul, hu]

theorem norm_theta (y : Lw) : ‖θ y‖ = ‖y‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, v_theta K L v w hw θ]

theorem norm_theta_pow (i : ℕ) (y : Lw) : ‖(θ ^ i) y‖ = ‖y‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, norm_theta K L v w hw, ih]

theorem norm_eq_one_iff_of_normString {ℓ : ℕ} (hℓ : 0 < ℓ) (α : Lw) (a : Kv)
    (h : ∏ i ∈ Finset.range ℓ, (θ ^ i) α = algebraMap Kv Lw a) : ‖α‖ = 1 ↔ ‖a‖ = 1 := by
  have key : ‖algebraMap Kv Lw a‖ = ‖α‖ ^ ℓ := by
    rw [← h, norm_prod, Finset.prod_congr rfl fun i _ => norm_theta_pow K L v w hw θ i α, Finset.prod_const,
      Finset.card_range]
  rw [← norm_algebraMap_eq_one_iff K L v w hw, key]
  constructor
  · intro h1; rw [h1, one_pow]
  · intro h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ.ne').1 h1

theorem map_theta_mem_iff (g : GL (Fin 2) Lw) :
    Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom g ∈ localIntegralSet L w.1 ↔ g ∈ localIntegralSet L w.1 := by
  have hval : ((Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom g : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) =
      (g : Matrix (Fin 2) (Fin 2) Lw).map θ.toAlgHom.toRingHom := by
    simp only [Matrix.GeneralLinearGroup.val_map_apply]
  have hdet : ((g : Matrix (Fin 2) (Fin 2) Lw).map θ.toAlgHom.toRingHom).det = θ (g : Matrix (Fin 2) (Fin 2) Lw).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [mem_localIntegralSet_iff_norm, mem_localIntegralSet_iff_norm, hval, hdet]
  change (∀ i j, ‖θ ((g : Matrix (Fin 2) (Fin 2) Lw) i j)‖ ≤ 1) ∧ ‖θ (g : Matrix (Fin 2) (Fin 2) Lw).det‖ = 1 ↔ _
  simp only [norm_theta K L v w hw θ]

omit hw in

theorem continuous_map_theta : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) θ.toAlgHom.toRingHom) := by
  have hθ : Continuous θ := IsModuleTopology.continuous_of_linearMap θ.toLinearMap
  apply Continuous.units_map
  exact continuous_id.matrix_map hθ

end Unramified
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Shells

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

abbrev OK : AddSubgroup Kv := (v.adicCompletionIntegers K).toAddSubgroup

variable (Λ : AddSubgroup (v.adicCompletion K)) (π : v.adicCompletion K)

def Lam (s : ℕ) : AddSubgroup Kv := Λ ⊓ (OK K v).comap (AddMonoidHom.mulLeft (π ^ s))

theorem mem_Lam (s : ℕ) (y : Kv) : y ∈ Lam K v Λ π s ↔ y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K := by
  rw [Lam, AddSubgroup.mem_inf, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
  exact Iff.rfl

def V (s : ℕ) : Set (GL (Fin 2) Kv) :=
  {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), (y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K) ∧
    k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem isOpen_V (s : ℕ) : IsOpen (V K v Λ π s) := by
  have hV : V K v Λ π s = ⋃ y ∈ {y : Kv | y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K},
      (fun k => unipotentGL2 y * k) '' localIntegralSet K v := by
    ext x
    simp only [V, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨y, k, hy, hk, rfl⟩; exact ⟨y, hy, k, hk, rfl⟩
    · rintro ⟨y, hy, k, hk, rfl⟩; exact ⟨y, k, hy, hk, rfl⟩
  rw [hV]
  exact isOpen_biUnion fun y _ => (isOpenMap_mul_left _) _ (isOpen_localIntegralSet K v)

def Uball (s : ℕ) : Set (GL (Fin 2) Kv) :=
  (fun p : Kv × GL (Fin 2) Kv => unipotentGL2 p.1 * p.2) '' ({y : Kv | ‖y‖ ≤ qv K v ^ s} ×ˢ localIntegralSet K v)

theorem isCompact_Uball (s : ℕ) : IsCompact (Uball K v s) := by
  refine IsCompact.image (IsCompact.prod ?_ (isCompact_localIntegralSet K v)) ?_
  · have : {y : Kv | ‖y‖ ≤ qv K v ^ s} = Metric.closedBall 0 (qv K v ^ s) := by
      ext y; simp
    rw [this]
    exact isCompact_closedBall _ _
  · exact ((continuous_unipotentGL2' K v).comp continuous_fst).mul continuous_snd

variable (hπ : ‖π‖ = (qv K v)⁻¹)
include hπ

theorem norm_pi_pow (n : ℕ) : ‖π ^ n‖ = (qv K v ^ n)⁻¹ := by
  rw [norm_pow, hπ, inv_pow]

theorem pow_mul_mem_iff (s : ℕ) (y : Kv) : π ^ s * y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ qv K v ^ s := by
  rw [mem_integers_iff_norm, norm_mul, norm_pi_pow K v π hπ, inv_mul_le_iff₀ (pow_pos (qv_pos K v) _), mul_one]

theorem pow_mul_mem_mono {s t : ℕ} (hst : s ≤ t) {y : Kv} (hy : π ^ s * y ∈ v.adicCompletionIntegers K) :
    π ^ t * y ∈ v.adicCompletionIntegers K := by
  rw [pow_mul_mem_iff K v π hπ] at hy ⊢
  exact hy.trans (pow_le_pow_right₀ (one_lt_qv K v).le hst)

theorem Lam_mono {s t : ℕ} (hst : s ≤ t) : Lam K v Λ π s ≤ Lam K v Λ π t := by
  intro y hy
  rw [mem_Lam] at hy ⊢
  exact ⟨hy.1, pow_mul_mem_mono K v π hπ hst hy.2⟩

theorem V_subset_Uball (s : ℕ) : V K v Λ π s ⊆ Uball K v s := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  exact ⟨(y, k), ⟨(pow_mul_mem_iff K v π hπ s y).1 hy.2, hk⟩, rfl⟩

attribute [local instance] AutomorphicForm.localGLBorel in

theorem shells (m : ℕ) (hfin : ∀ s ≤ m, (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    (∀ s ≤ m, localHaar K v (V K v Λ π s) = (OK K v).relIndex (Lam K v Λ π s)) ∧
    (∫ x in V K v Λ π m, LocalWeight.weight x ∂(localHaar K v)) =
      2 * Real.log (qv K v) * ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
        (((OK K v).relIndex (Lam K v Λ π (s + 1)) : ℝ) - ((OK K v).relIndex (Lam K v Λ π s) : ℝ)) :=
  AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
    K v Λ π hπ m hfin

end Shells
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Twisted

open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)
local notation "θG" => Matrix.GeneralLinearGroup.map (AlgHom.toRingHom (AlgEquiv.toAlgHom θ))
local notation "θU" => Units.map (MonoidHomClass.toMonoidHom (AlgHom.toRingHom (AlgEquiv.toAlgHom θ)))

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

theorem thG_unipotentGL2 (y : Lw) : θG (unipotentGL2 y) = unipotentGL2 (θ y) :=
  map_unipotentGL2 _ y

theorem thG_diagUnits2 (t₁ t₂ : Lwˣ) : θG (diagUnits2 t₁ t₂) = diagUnits2 (θU t₁) (θU t₂) :=
  map_diagUnits2 _ _ _

theorem coe_thU (t : Lwˣ) : ((θU t : Lwˣ) : Lw) = θ t := rfl

def TorusHyp (a b : Kvˣ) (α β : Lwˣ) : Prop :=
  sigmaCentralizer θG (diagUnits2 α β) =
    (localCentralizer K v (diagUnits2 a b)).map (Matrix.GeneralLinearGroup.map (algebraMap Kv Lw))

theorem mem_torus_iff {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : GL (Fin 2) Lw) :
    t ∈ sigmaCentralizer θG (diagUnits2 α β) ↔ ∃ t₁ t₂ : Kvˣ,
      t = diagUnits2 (Units.map (algebraMap Kv Lw : Kv →* Lw) t₁) (Units.map (algebraMap Kv Lw : Kv →* Lw) t₂) := by
  rw [show sigmaCentralizer θG (diagUnits2 α β) = _ from hT, Subgroup.mem_map]
  constructor
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨h01, h10⟩ := (mem_centralizer_iff K v hab t').1 ht'
    refine ⟨Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).1, Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).2, ?_⟩
    conv_lhs => rw [eq_diagUnits2_of_offdiag K v h01 h10]
    exact map_diagUnits2 _ _ _
  · rintro ⟨t₁, t₂, rfl⟩
    exact ⟨diagUnits2 t₁ t₂, diagUnits2_mem_centralizer K v hab t₁ t₂, map_diagUnits2 _ _ _⟩

theorem torus_offdiag {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) :
    ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) 0 1 = 0 ∧ ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) 1 0 = 0 := by
  obtain ⟨t₁, t₂, ht⟩ := (mem_torus_iff K L v w θ hab hT t).1 t.2
  rw [ht, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  simp

theorem torus_eq_diag {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) :
    (t : GL (Fin 2) Lw) = diagUnits2 (Units.mk0 _ (diag_ne_zero_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1).1)
      (Units.mk0 _ (diag_ne_zero_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1).2) :=
  eq_diagUnits2_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1 (torus_offdiag K L v w θ hab hT t).2

theorem torus_comm {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (s t : sigmaCentralizer θG (diagUnits2 α β)) : s * t = t * s := by
  obtain ⟨s01, s10⟩ := torus_offdiag K L v w θ hab hT s
  obtain ⟨t01, t10⟩ := torus_offdiag K L v w θ hab hT t
  apply Subtype.ext
  apply Units.ext
  change ((s : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) * ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) =
    ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) * ((s : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, t01, t10, mul_comm]

theorem weight_torus_mul {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) (x : GL (Fin 2) Lw) :
    LocalWeight.weight ((t : GL (Fin 2) Lw) * x) = LocalWeight.weight x := by
  rw [torus_eq_diag K L v w θ hab hT t]
  exact WeightKit.weight_diagUnits2_mul _ _ x

theorem isClosed_torus (α β : Lwˣ) :
    IsClosed ((sigmaCentralizer θG (diagUnits2 α β) : Subgroup (GL (Fin 2) Lw)) : Set (GL (Fin 2) Lw)) := by
  have : ((sigmaCentralizer θG (diagUnits2 α β) : Subgroup (GL (Fin 2) Lw)) : Set (GL (Fin 2) Lw)) =
      {t | t * diagUnits2 α β * (θG t)⁻¹ = diagUnits2 α β} := rfl
  rw [this]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul ((continuous_map_theta K L v w θ).comp continuous_id).inv)
    continuous_const

def Fδ (α β : Lwˣ) (x : GL (Fin 2) Lw) : ℂ :=
  (localIntegralSet L w.1).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * θG x)

theorem Fδ_apply (α β : Lwˣ) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β x = if x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1 then 1 else 0 := by
  rw [Fδ, Set.indicator_apply]

theorem Fδ_ne_zero_iff (α β : Lwˣ) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β x ≠ 0 ↔ x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1 := by
  rw [Fδ_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc; exact h (if_neg hc)
  · rw [if_pos h]; exact one_ne_zero

theorem Fδ_eq_one_of_mem {α β : Lwˣ} {x : GL (Fin 2) Lw} (h : x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β x = 1 := by
  rw [Fδ_apply, if_pos h]

theorem norm_Fδ_le_one (α β : Lwˣ) (x : GL (Fin 2) Lw) : ‖Fδ K L v w θ α β x‖ ≤ 1 := by
  rw [Fδ_apply]; split_ifs <;> simp

theorem continuous_twistedConj (α β : Lwˣ) : Continuous fun x : GL (Fin 2) Lw => x⁻¹ * diagUnits2 α β * θG x :=
  (continuous_id.inv.mul continuous_const).mul ((continuous_map_theta K L v w θ).comp continuous_id)

theorem measurable_Fδ (α β : Lwˣ) : Measurable (Fδ K L v w θ α β) := by
  have : Fδ K L v w θ α β =
      ((fun x : GL (Fin 2) Lw => x⁻¹ * diagUnits2 α β * θG x) ⁻¹' localIntegralSet L w.1).indicator fun _ => (1 : ℂ) := by
    funext x
    simp only [Fδ, Set.indicator_apply, Set.mem_preimage]
  rw [this]
  exact measurable_const.indicator
    (((isOpen_localIntegralSet L w.1).preimage (continuous_twistedConj K L v w θ α β)).measurableSet)

theorem Fδ_torus_mul {α β : Lwˣ} (t : sigmaCentralizer θG (diagUnits2 α β)) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β ((t : GL (Fin 2) Lw) * x) = Fδ K L v w θ α β x := by
  have ht : ((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * θG (t : GL (Fin 2) Lw) = diagUnits2 α β :=
    mem_sigmaCentralizer_iff_inv.1 t.2
  unfold Fδ
  congr 1
  rw [mul_inv_rev, map_mul]
  calc x⁻¹ * ((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * (θG (t : GL (Fin 2) Lw) * θG x)
      = x⁻¹ * (((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * θG (t : GL (Fin 2) Lw)) * θG x := by
        simp only [mul_assoc]
    _ = x⁻¹ * diagUnits2 α β * θG x := by rw [ht]

theorem twistedConj_eq (α β t₁ t₂ : Lwˣ) (y : Lw) (k : GL (Fin 2) Lw) :
    (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 α β * θG (diagUnits2 t₁ t₂ * unipotentGL2 y * k) =
      k⁻¹ * ((unipotentGL2 y)⁻¹ * diagUnits2 (t₁⁻¹ * α * θU t₁) (t₂⁻¹ * β * θU t₂) * unipotentGL2 (θ y)) * θG k := by
  rw [map_mul, map_mul, thG_diagUnits2, thG_unipotentGL2, ← diagUnits2_mul_diagUnits2, ← diagUnits2_mul_diagUnits2,
    ← diagUnits2_inv]
  simp only [mul_inv_rev, mul_assoc]

theorem norm_coe_twistUnit (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (t α : Lwˣ) : ‖((t⁻¹ * α * θU t : Lwˣ) : Lw)‖ = ‖(α : Lw)‖ := by
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, coe_thU, norm_mul, norm_mul, norm_inv,
    norm_theta K L v w hw θ]
  have h : ‖(t : Lw)‖ ≠ 0 := norm_ne_zero_iff.2 t.ne_zero
  field_simp

theorem twistedConj_mem_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (α β t₁ t₂ : Lwˣ) (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 α β * θG (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈
        localIntegralSet L w.1 ↔
      ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 ∧
        ‖((t₁⁻¹ * α * θU t₁ : Lwˣ) : Lw) * θ y - ((t₂⁻¹ * β * θU t₂ : Lwˣ) : Lw) * y‖ ≤ 1 := by
  rw [twistedConj_eq, mul_mem_localIntegralSet_iff_left L w.1 ((map_theta_mem_iff K L v w hw θ k).2 hk),
    mul_mem_localIntegralSet_iff_right L w.1 (inv_mem_localIntegralSet L w.1 hk),
    upper_mem_iff L w.1 (coe_unipotent_twist_conj L w.1 _ _ y (θ y)), norm_coe_twistUnit K L v w θ hw,
    norm_coe_twistUnit K L v w θ hw]

theorem units_of_Fδ_ne_zero (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {α β : Lwˣ} {x : GL (Fin 2) Lw} (hx : Fδ K L v w θ α β x ≠ 0) : ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 := by
  rw [Fδ_ne_zero_iff] at hx
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa L w.1 x
  obtain ⟨ha, hb, -⟩ := (twistedConj_mem_iff K L v w θ hw α β t₁ t₂ y hk).1 hx
  exact ⟨ha, hb⟩

theorem Fδ_unipotent_mul_ne_zero_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (α β : Lwˣ) (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β (unipotentGL2 y * k) ≠ 0 ↔
      ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 ∧ ‖(α : Lw) * θ y - β * y‖ ≤ 1 := by
  have h := twistedConj_mem_iff K L v w θ hw α β 1 1 y hk
  have h11 : (diagUnits2 1 1 : GL (Fin 2) Lw) = 1 := by
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h11, one_mul] at h
  rw [Fδ_ne_zero_iff, h]
  simp

def LamC (c : Lw) : AddSubgroup Lw :=
  (w.1.adicCompletionIntegers L).toAddSubgroup.comap
    ((AlgHom.toRingHom (AlgEquiv.toAlgHom θ)).toAddMonoidHom - AddMonoidHom.mulLeft c)

theorem mem_LamC (c y : Lw) : y ∈ LamC K L v w θ c ↔ θ y - c * y ∈ w.1.adicCompletionIntegers L := by
  rw [LamC, AddSubgroup.mem_comap, AddMonoidHom.sub_apply, AddMonoidHom.coe_mulLeft]
  exact Iff.rfl

theorem isInvInvariant_of_comm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → G)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

section UnitCase

variable {α β : (w.1.adicCompletion L)ˣ} (ha1 : ‖(α : w.1.adicCompletion L)‖ = 1)
  (hb1 : ‖(β : w.1.adicCompletion L)‖ = 1)
include ha1 hb1

theorem norm_c : ‖((β * α⁻¹ : Lwˣ) : Lw)‖ = 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, ha1, hb1, inv_one, mul_one]

omit hb1 in
theorem norm_key (y : Lw) : ‖(α : Lw) * θ y - β * y‖ = ‖θ y - ((β * α⁻¹ : Lwˣ) : Lw) * y‖ := by
  have h : (α : Lw) * θ y - β * y = α * (θ y - ((β * α⁻¹ : Lwˣ) : Lw) * y) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, mul_comm (β : Lw) ((α : Lw)⁻¹), ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ α.ne_zero, one_mul]
  rw [h, norm_mul, ha1, one_mul]

theorem Fδ_unipotent_mul_ne_zero_iff_mem
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β (unipotentGL2 y * k) ≠ 0 ↔ y ∈ LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw) := by
  rw [Fδ_unipotent_mul_ne_zero_iff K L v w θ hw α β y hk, mem_LamC, mem_integers_iff_norm, norm_key K L v w θ ha1]
  simp [ha1, hb1]

theorem OK_le_Lam (π : Lw) (hπ : ‖π‖ = (qv L w.1)⁻¹) (s : ℕ) :
    OK L w.1 ≤ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s := by
  intro y hy
  change y ∈ w.1.adicCompletionIntegers L at hy
  rw [mem_Lam, mem_LamC]
  refine ⟨sub_mem (theta_mem K L v w θ hy) ?_, ?_⟩
  · rw [mem_integers_iff_norm] at hy ⊢
    rw [norm_mul, norm_c K L v w ha1 hb1, one_mul]; exact hy
  · rw [pow_mul_mem_iff L w.1 π hπ]
    exact ((mem_integers_iff_norm L w.1 y).1 hy).trans (one_le_pow₀ (one_lt_qv L w.1).le)

variable (π : w.1.adicCompletion L) (hπ : ‖π‖ = (qv L w.1)⁻¹) (M : ℕ)
  (hidx : ∀ s : ℕ, (OK L w.1).relIndex
    (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L)) π s) =
      Ideal.absNorm v.asIdeal ^ min s M)
include hπ hidx

theorem Lam_eq_of_le {s : ℕ} (hs : M ≤ s) :
    Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s = Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M := by
  have hle := Lam_mono L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π hπ hs
  have h := AddSubgroup.relIndex_mul_relIndex (OK L w.1) _ _ (OK_le_Lam K L v w θ ha1 hb1 π hπ M) hle
  rw [hidx M, hidx s, min_self, min_eq_right hs] at h
  have hq : Ideal.absNorm v.asIdeal ^ M ≠ 0 :=
    pow_ne_zero _ (by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
  have h1 : (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).relIndex
      (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s) = 1 :=
    (mul_right_inj' hq).1 (by rw [h, mul_one])
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle

theorem mem_LamM_of_mem_LamC {y : Lw} (hy : y ∈ LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) :
    y ∈ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M := by
  rcases norm_eq_zero_or_zpow L w.1 y with h0 | ⟨n, hn⟩
  · rw [norm_eq_zero] at h0
    rw [h0]; exact zero_mem _
  · have hN : y ∈ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π (max n.toNat M) := by
      rw [mem_Lam, pow_mul_mem_iff L w.1 π hπ, hn]
      refine ⟨hy, ?_⟩
      have h1 : (n : ℤ) ≤ ((max n.toNat M : ℕ) : ℤ) := (Int.self_le_toNat n).trans (by exact_mod_cast le_max_left _ _)
      have := zpow_le_zpow_right₀ (one_lt_qv L w.1).le h1
      rwa [zpow_natCast] at this
    rwa [Lam_eq_of_le K L v w θ ha1 hb1 π hπ M hidx (le_max_right _ _)] at hN

theorem mem_V_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (x : GL (Fin 2) Lw) :
    x ∈ V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M ↔ x ∈ NK L w.1 ∧ Fδ K L v w θ α β x ≠ 0 := by
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩
    exact ⟨⟨y, k, hk, rfl⟩, (Fδ_unipotent_mul_ne_zero_iff_mem K L v w θ ha1 hb1 hw y hk).2 hy.1⟩
  · rintro ⟨⟨y, k, hk, rfl⟩, hx⟩
    have hy := (Fδ_unipotent_mul_ne_zero_iff_mem K L v w θ ha1 hb1 hw y hk).1 hx
    exact ⟨y, k, (mem_Lam L w.1 _ π M y).1 (mem_LamM_of_mem_LamC K L v w θ ha1 hb1 π hπ M hidx hy), hk, rfl⟩

theorem integral_indicator_V_translate
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {a b : Kvˣ} (hab : a ≠ b) (hT : TorusHyp K L v w θ a b α β)
    (τ' : @Measure (sigmaCentralizer θG (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1} = 1)
    (x : GL (Fin 2) Lw) (hx : Fδ K L v w θ α β x ≠ 0) :
    (letI : MeasurableSpace (sigmaCentralizer θG (diagUnits2 α β)) := borel _
     ∫ t : sigmaCentralizer θG (diagUnits2 α β),
        (V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).indicator (fun _ => (1 : ℝ)) ((t : GL (Fin 2) Lw) * x) ∂τ') = 1 := by
  letI : MeasurableSpace (sigmaCentralizer θG (diagUnits2 α β)) := borel _
  haveI : BorelSpace (sigmaCentralizer θG (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_of_comm _ (torus_comm K L v w θ hab hT) τ'
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa L w.1 x

  have hset : ∀ t : sigmaCentralizer θG (diagUnits2 α β),
      (t : GL (Fin 2) Lw) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈ V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M ↔
        (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 := by
    intro t
    rw [mem_V_iff K L v w θ ha1 hb1 π hπ M hidx hw, Fδ_torus_mul, and_iff_left hx, torus_eq_diag K L v w θ hab hT t,
      ← mul_assoc, ← mul_assoc, diagUnits2_mul_diagUnits2, diag_mul_mem_NK_iff L w.1 _ _ y hk]

  obtain ⟨x₁, hx₁, hu₁⟩ := exists_eq_algebraMap_mul_unit K L v w hw t₁.ne_zero
  obtain ⟨x₂, hx₂, hu₂⟩ := exists_eq_algebraMap_mul_unit K L v w hw t₂.ne_zero
  set t₀ : sigmaCentralizer θG (diagUnits2 α β) :=
    ⟨diagUnits2 (Units.map (algebraMap Kv Lw : Kv →* Lw) (Units.mk0 x₁ hx₁)⁻¹)
        (Units.map (algebraMap Kv Lw : Kv →* Lw) (Units.mk0 x₂ hx₂)⁻¹),
      (mem_torus_iff K L v w θ hab hT _).2 ⟨(Units.mk0 x₁ hx₁)⁻¹, (Units.mk0 x₂ hx₂)⁻¹, rfl⟩⟩ with ht₀
  have ht₀d : (t₀ : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 := by
    change diagUnits2 _ _ * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1
    rw [diagUnits2_mul_diagUnits2, diagUnits2_mem_iff, norm_eq_one_iff_v, norm_eq_one_iff_v]
    constructor
    · rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, Units.coe_map, mul_comm]; exact hu₁
    · rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, Units.coe_map, mul_comm]; exact hu₂
  have hset2 : ∀ t : sigmaCentralizer θG (diagUnits2 α β),
      (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 ↔
        ((t * t₀⁻¹ : sigmaCentralizer θG (diagUnits2 α β)) : GL (Fin 2) Lw) ∈ localIntegralSet L w.1 := by
    intro t
    have : (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ =
        ((t * t₀⁻¹ : sigmaCentralizer θG (diagUnits2 α β)) : GL (Fin 2) Lw) * ((t₀ : GL (Fin 2) Lw) * diagUnits2 t₁ t₂) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
    rw [this, mul_mem_localIntegralSet_iff_left L w.1 ht₀d]
  have hfun : (fun t : sigmaCentralizer θG (diagUnits2 α β) =>
        (V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).indicator (fun _ => (1 : ℝ))
          ((t : GL (Fin 2) Lw) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k))) =
      ((fun t => t * t₀⁻¹) ⁻¹' {t : sigmaCentralizer θG (diagUnits2 α β) | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1}).indicator
        fun _ => (1 : ℝ) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq, hset t, hset2 t]
  have hmeas : MeasurableSet {t : sigmaCentralizer θG (diagUnits2 α β) | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1} :=
    ((isOpen_localIntegralSet L w.1).preimage continuous_subtype_val).measurableSet
  rw [hfun, integral_indicator_const _ (measurableSet_preimage (measurable_mul_const _) hmeas), smul_eq_mul, mul_one,
    measureReal_def, measure_preimage_mul_right, hτ'1, ENNReal.toReal_one]

end UnitCase
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

end Twisted
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

section Main

open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

omit [NumberField K] in

theorem shellSum_eq (q : ℝ) (hq : q ≠ 0) (M : ℕ) :
    ∑ s ∈ Finset.range M, ((s + 1 : ℕ) : ℝ) * (q ^ min (s + 1) M - q ^ min s M) =
      ∑ s ∈ Finset.range (M + 1), (s : ℝ) * (q ^ s - q ^ s / q) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [min_eq_left (by omega : s + 1 ≤ M), min_eq_left (by omega : s ≤ M), pow_succ, mul_div_assoc, div_self hq,
    mul_one]

theorem main
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (α : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (β : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
            (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (θ.toAlgHom.toRingHom.toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L))) ⊓
              ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (AddMonoidHom.mulLeft
                  (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈
          AutomorphicForm.localIntegralSet L w.1 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) *
          ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℂ) *
          (((2 * Real.log (Ideal.absNorm v.asIdeal) *
              ∑ s ∈ Finset.range (m.toNat + 1),
                (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                  (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by
  have hℓ : 0 < Module.finrank Kv Lw := Module.finrank_pos
  change ∫ x, Fδ K L v w θ α β x * (LocalWeight.weight x : ℂ) * (s x : ℂ) ∂(localHaar L w.1) = _
  by_cases hu : ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1
  swap
  ·
    rw [if_neg hu]
    have h0 : ∀ x, Fδ K L v w θ α β x = 0 := fun x => by
      by_contra hne
      obtain ⟨ha, hb⟩ := units_of_Fδ_ne_zero K L v w θ hw hne
      exact hu ⟨(norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNα).1 ha,
        (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNβ).1 hb⟩
    simp [h0]

  rw [if_pos hu]
  have ha1 : ‖(α : Lw)‖ = 1 := (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNα).2 hu.1
  have hb1 : ‖(β : Lw)‖ = 1 := (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNβ).2 hu.2
  obtain ⟨ϖ, hϖ⟩ := exists_norm_eq_inv K v
  set π : Lw := algebraMap Kv Lw ϖ with hπdef
  have hπ : ‖π‖ = (qv L w.1)⁻¹ := norm_algebraMap_uniformizer K L v w hw hϖ
  set M : ℕ := m.toNat with hM
  set Λ : AddSubgroup Lw := LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw) with hΛ
  have hidx' : ∀ s : ℕ, (OK L w.1).relIndex (Lam L w.1 Λ π s) = Ideal.absNorm v.asIdeal ^ min s M := by
    intro s
    have h := hidx hu.1 hu.2 ϖ hϖ s
    rw [map_pow] at h
    exact h
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega
  have hfin : ∀ s ≤ M, (OK L w.1).relIndex (Lam L w.1 Λ π s) ≠ 0 := fun s _ => by
    rw [hidx' s]; exact pow_ne_zero _ hq0

  letI : MeasurableSpace (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) :=
    borel _
  haveI : BorelSpace (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'
  haveI : τ'.IsInvInvariant :=
    isInvInvariant_of_comm _ (isClosed_torus K L v w θ α β) (torus_comm K L v w θ hab hT) τ'

  set s₀ : GL (Fin 2) Lw → ℝ := (V L w.1 Λ π M).indicator fun _ => (1 : ℝ) with hs₀
  have hs₀' : (∀ x, 0 ≤ s₀ x) ∧ Measurable s₀ ∧ HasCompactSupport s₀ ∧
      ∀ x, Fδ K L v w θ α β x ≠ 0 →
        ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β),
          s₀ ((t : GL (Fin 2) Lw) * x) ∂τ' = 1 := by
    refine ⟨fun x => ?_, measurable_const.indicator (isOpen_V L w.1 Λ π M).measurableSet,
      HasCompactSupport.intro (isCompact_Uball L w.1 M) fun x hx =>
        Set.indicator_of_notMem (fun h => hx (V_subset_Uball L w.1 Λ π hπ M h)) _, fun x hx => ?_⟩
    · rw [hs₀, Set.indicator_apply]; split_ifs <;> simp
    · exact integral_indicator_V_translate K L v w θ ha1 hb1 π hπ M hidx' hw hab hT τ' hτ' hτ'1 x hx
  have hs' : (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      ∀ x, Fδ K L v w θ α β x ≠ 0 →
        ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β),
          s ((t : GL (Fin 2) Lw) * x) ∂τ' = 1 :=
    ⟨hs0, hsm, hsc, fun x hx => hs1 x ((Fδ_ne_zero_iff K L v w θ α β x).1 hx)⟩

  have hind := (MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
    (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β))
    (isClosed_torus K L v w θ α β) (localHaar L w.1) τ'
    (Fδ K L v w θ α β) (measurable_Fδ K L v w θ α β) ⟨1, norm_Fδ_le_one K L v w θ α β⟩
    (fun t x => Fδ_torus_mul K L v w θ t x)
    LocalWeight.weight WeightKit.continuous_weight (fun t x => weight_torus_mul K L v w θ hab hT t x)
    s s₀ hs' hs₀').2

  have hshell := (shells L w.1 Λ π hπ M hfin).2
  have hval : ∫ x, Fδ K L v w θ α β x * (LocalWeight.weight x : ℂ) * (s₀ x : ℂ) ∂(localHaar L w.1) =
      ((2 * Real.log (qv L w.1) * ∑ s ∈ Finset.range M, ((s + 1 : ℕ) : ℝ) *
        ((qv K v) ^ min (s + 1) M - (qv K v) ^ min s M) : ℝ) : ℂ) := by
    have hfun : (fun x => Fδ K L v w θ α β x * (LocalWeight.weight x : ℂ) * (s₀ x : ℂ)) =
        (V L w.1 Λ π M).indicator fun x => (LocalWeight.weight x : ℂ) := by
      funext x
      by_cases hx : x ∈ V L w.1 Λ π M
      · rw [Set.indicator_of_mem hx, hs₀, Set.indicator_of_mem hx,
          Fδ_eq_one_of_mem K L v w θ ((Fδ_ne_zero_iff K L v w θ α β x).1
            ((mem_V_iff K L v w θ ha1 hb1 π hπ M hidx' hw x).1 hx).2)]
        simp
      · rw [Set.indicator_of_notMem hx, hs₀, Set.indicator_of_notMem hx]
        simp
    rw [hfun, integral_indicator (isOpen_V L w.1 Λ π M).measurableSet, integral_complex_ofReal, hshell]
    have hsum : ∑ s ∈ Finset.range M, ((s + 1 : ℕ) : ℝ) *
        (((OK L w.1).relIndex (Lam L w.1 Λ π (s + 1)) : ℝ) - ((OK L w.1).relIndex (Lam L w.1 Λ π s) : ℝ)) =
        ∑ s ∈ Finset.range M, ((s + 1 : ℕ) : ℝ) * ((qv K v) ^ min (s + 1) M - (qv K v) ^ min s M) :=
      Finset.sum_congr rfl fun s _ => by rw [hidx' (s + 1), hidx' s, Nat.cast_pow, Nat.cast_pow]
    rw [hsum]
  rw [hind, hval, shellSum_eq (qv K v) (qv_ne_zero K v) M, qv_w_eq_pow K L v w hw, Real.log_pow]
  push_cast
  ring

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK"

end P2mInertUnitE2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace E8A
namespace A0

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "EE" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w₀)

def cw (x : EE) : Lw := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w₀

theorem cw_mul (x y : EE) : cw K L v w₀ (x * y) = cw K L v w₀ x * cw K L v w₀ y := by
  simp only [cw, map_mul, Pi.mul_apply]

theorem cw_one : cw K L v w₀ 1 = 1 := by
  simp only [cw, map_one, Pi.one_apply]

theorem cw_tmul_one (y : Kv) : cw K L v w₀ ((1 : L) ⊗ₜ[K] y) = algebraMap Kv Lw y := by
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] y) w₀ = _
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]

theorem continuous_cw : Continuous (cw K L v w₀) := by
  have h : cw K L v w₀ = fun x => HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v x w₀ := rfl
  rw [h]
  exact (continuous_apply w₀).comp (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).continuous

theorem cw_ne_zero_of_isUnit {x : EE} (hx : IsUnit x) : cw K L v w₀ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h0
  have h1 : cw K L v w₀ ((u : EE) * (u⁻¹ : (EE)ˣ)) = 1 := by rw [Units.mul_inv, cw_one]
  rw [cw_mul, h0, zero_mul] at h1
  exact zero_ne_one h1

theorem v_algebraMap (y : Kv) :
    (Valued.v (algebraMap Kv Lw y) : WithZero (Multiplicative ℤ)) =
      Valued.v y ^ (w₀.1.under (𝓞 K)).asIdeal.ramificationIdx' w₀.1.asIdeal :=
  HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w₀ y

theorem ramificationIdx_ne_zero : (w₀.1.under (𝓞 K)).asIdeal.ramificationIdx' w₀.1.asIdeal ≠ 0 := by
  have h2 : HeightOneSpectrum.under (𝓞 K) w₀.1 = v := w₀.2
  rw [h2]
  haveI : w₀.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w₀.2).symm⟩
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w₀.1.asIdeal v.ne_bot

theorem norm_algebraMap_eq_one_iff (y : Kv) : ‖algebraMap Kv Lw y‖ = 1 ↔ ‖y‖ = 1 := by
  rw [P2mInertUnitE2.norm_eq_one_iff_v, P2mInertUnitE2.norm_eq_one_iff_v, v_algebraMap]
  constructor
  · intro h1
    rcases pow_eq_one_iff.1 h1 with h | h
    · exact h
    · exact absurd h (ramificationIdx_ne_zero K L v w₀)
  · intro h1; rw [h1, one_pow]

theorem norm_algebraMap_lt_one_of_norm_lt_one {y : Kv} (hy : ‖y‖ < 1) : ‖algebraMap Kv Lw y‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff] at hy ⊢
  rw [v_algebraMap]
  exact pow_lt_one₀ zero_le' hy (ramificationIdx_ne_zero K L v w₀)

end E8A.A0
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

namespace E8A
namespace A0

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "EE" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w₀)

def piU : Kvˣ := Units.mk0 (Classical.choose (P2mUnitWeightK.exists_norm_eq_inv K v))
  (P2mUnitWeightK.uniformizer_ne_zero K v (Classical.choose_spec (P2mUnitWeightK.exists_norm_eq_inv K v)))

theorem norm_piU : ‖((piU K v : Kvˣ) : Kv)‖ = (P2mUnitWeightK.qv K v)⁻¹ :=
  Classical.choose_spec (P2mUnitWeightK.exists_norm_eq_inv K v)

def Q : ℝ := ‖algebraMap Kv Lw ((piU K v : Kvˣ) : Kv)‖⁻¹

theorem norm_algebraMap_piU : ‖algebraMap Kv Lw ((piU K v : Kvˣ) : Kv)‖ = (Q K L v w₀)⁻¹ := by
  rw [Q, inv_inv]

theorem norm_algebraMap_piU_pos : 0 < ‖algebraMap Kv Lw ((piU K v : Kvˣ) : Kv)‖ :=
  norm_pos_iff.2 ((map_ne_zero _).2 (piU K v).ne_zero)

theorem one_lt_Q : 1 < Q K L v w₀ := by
  rw [Q]
  have h1 : ‖algebraMap Kv Lw ((piU K v : Kvˣ) : Kv)‖ < 1 := by
    apply norm_algebraMap_lt_one_of_norm_lt_one
    rw [norm_piU]
    exact inv_lt_one_of_one_lt₀ (P2mUnitWeightK.one_lt_qv K v)
  exact one_lt_inv₀ (norm_algebraMap_piU_pos K L v w₀) |>.2 h1

theorem Q_pos : 0 < Q K L v w₀ := lt_trans one_pos (one_lt_Q K L v w₀)

theorem exists_eq_piU_zpow_mul (d : Kvˣ) : ∃ (n : ℤ) (u : Kvˣ), ‖(u : Kv)‖ = 1 ∧ d = piU K v ^ n * u := by
  rcases P2mUnitWeightK.norm_eq_zero_or_zpow K v (d : Kv) with h0 | ⟨m, hm⟩
  · exact absurd (norm_eq_zero.1 h0) d.ne_zero
  refine ⟨-m, piU K v ^ m * d, ?_, by group⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, norm_piU, hm, inv_zpow', zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero m (P2mUnitWeightK.qv_ne_zero K v))

theorem norm_algebraMap_piU_zpow_mul (n : ℤ) {u : Kvˣ} (hu : ‖(u : Kv)‖ = 1) :
    ‖algebraMap Kv Lw ((piU K v ^ n * u : Kvˣ) : Kv)‖ = Q K L v w₀ ^ (-n) := by
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, norm_mul, norm_zpow,
    norm_algebraMap_piU, (norm_algebraMap_eq_one_iff K L v w₀ _).2 hu, mul_one, inv_zpow']

def box : Set EE := {x | (Q K L v w₀)⁻¹ < ‖cw K L v w₀ x‖ ∧ ‖cw K L v w₀ x‖ ≤ 1}

theorem box_eq_preimage : box K L v w₀ = (fun x => ‖cw K L v w₀ x‖) ⁻¹' Set.Ioc (Q K L v w₀)⁻¹ 1 := rfl

theorem measurableSet_box [MeasurableSpace EE] [BorelSpace EE] : MeasurableSet (box K L v w₀) := by
  rw [box_eq_preimage]
  exact (continuous_cw K L v w₀).norm.measurable measurableSet_Ioc

def βs (p : EE × EE) : ℝ := (box K L v w₀ ×ˢ box K L v w₀).indicator (fun _ => (1 : ℝ)) p

theorem measurable_βs [MeasurableSpace EE] [BorelSpace EE] : Measurable (βs K L v w₀) :=
  measurable_const.indicator ((measurableSet_box K L v w₀).prod (measurableSet_box K L v w₀))

theorem βs_nonneg_le_one (p : EE × EE) : 0 ≤ βs K L v w₀ p ∧ βs K L v w₀ p ≤ 1 := by
  unfold βs
  rw [Set.indicator_apply]
  split_ifs <;> simp

theorem βs_ne_zero_iff (p : EE × EE) : βs K L v w₀ p ≠ 0 ↔ p.1 ∈ box K L v w₀ ∧ p.2 ∈ box K L v w₀ := by
  unfold βs
  rw [Set.indicator_apply]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_ne_zero⟩
  · exact ⟨fun h0 => absurd rfl h0, fun h' => absurd h' h⟩

theorem exists_zpow_mul_mem_box (r : ℝ) (hr : 0 < r) :
    ∃ n : ℤ, (Q K L v w₀)⁻¹ < Q K L v w₀ ^ (-n) * r ∧ Q K L v w₀ ^ (-n) * r ≤ 1 := by
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hr (one_lt_Q K L v w₀)
  have hQ := Q_pos K L v w₀
  refine ⟨m + 1, ?_, ?_⟩
  · have : (Q K L v w₀)⁻¹ = Q K L v w₀ ^ (-(m + 1)) * Q K L v w₀ ^ m := by
      rw [← zpow_add₀ hQ.ne', ← zpow_neg_one]; congr 1; ring
    rw [this]
    exact mul_lt_mul_of_pos_left hm1 (zpow_pos hQ _)
  · have : (1 : ℝ) = Q K L v w₀ ^ (-(m + 1)) * Q K L v w₀ ^ (m + 1) := by
      rw [← zpow_add₀ hQ.ne', neg_add_cancel, zpow_zero]
    rw [this]
    exact mul_le_mul_of_nonneg_left hm2 (zpow_nonneg hQ.le _)

theorem zpow_mul_mem_box_unique {r : ℝ} (hr : 0 < r) {n n' : ℤ}
    (hn : (Q K L v w₀)⁻¹ < Q K L v w₀ ^ (-n) * r ∧ Q K L v w₀ ^ (-n) * r ≤ 1)
    (hn' : (Q K L v w₀)⁻¹ < Q K L v w₀ ^ (-n') * r ∧ Q K L v w₀ ^ (-n') * r ≤ 1) : n = n' := by
  have hQ := Q_pos K L v w₀
  have hQ1 := one_lt_Q K L v w₀

  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have h1 : Q K L v w₀ ^ (-n') * r ≤ Q K L v w₀ ^ (-n - 1) * r :=
      mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hQ1.le (by omega)) hr.le
    have h2 : Q K L v w₀ ^ (-n - 1) * r = (Q K L v w₀)⁻¹ * (Q K L v w₀ ^ (-n) * r) := by
      rw [← mul_assoc, ← zpow_neg_one, ← zpow_add₀ hQ.ne']; congr 1; ring
    have h3 : (Q K L v w₀)⁻¹ * (Q K L v w₀ ^ (-n) * r) ≤ (Q K L v w₀)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hn.2 (inv_nonneg.2 hQ.le)
    linarith [hn'.1]
  · have h1 : Q K L v w₀ ^ (-n) * r ≤ Q K L v w₀ ^ (-n' - 1) * r :=
      mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hQ1.le (by omega)) hr.le
    have h2 : Q K L v w₀ ^ (-n' - 1) * r = (Q K L v w₀)⁻¹ * (Q K L v w₀ ^ (-n') * r) := by
      rw [← mul_assoc, ← zpow_neg_one, ← zpow_add₀ hQ.ne']; congr 1; ring
    have h3 : (Q K L v w₀)⁻¹ * (Q K L v w₀ ^ (-n') * r) ≤ (Q K L v w₀)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hn'.2 (inv_nonneg.2 hQ.le)
    linarith [hn.1]

theorem tmul_mul_mem_box_iff {p : EE} (hp : cw K L v w₀ p ≠ 0) (n : ℤ)
    (hn : (Q K L v w₀)⁻¹ < Q K L v w₀ ^ (-n) * ‖cw K L v w₀ p‖ ∧ Q K L v w₀ ^ (-n) * ‖cw K L v w₀ p‖ ≤ 1)
    (d : Kvˣ) :
    ((1 : L) ⊗ₜ[K] ((d : Kvˣ) : Kv)) * p ∈ box K L v w₀ ↔ ‖((piU K v ^ (-n) * d : Kvˣ) : Kv)‖ = 1 := by
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_piU_zpow_mul K v d
  have hnorm : ‖cw K L v w₀ (((1 : L) ⊗ₜ[K] ((piU K v ^ m * u : Kvˣ) : Kv)) * p)‖ = Q K L v w₀ ^ (-m) * ‖cw K L v w₀ p‖ := by
    rw [cw_mul, cw_tmul_one, norm_mul, norm_algebraMap_piU_zpow_mul K L v w₀ m hu]
  have hkey : ‖((piU K v ^ (-n) * (piU K v ^ m * u) : Kvˣ) : Kv)‖ = 1 ↔ m = n := by
    rw [← mul_assoc, ← zpow_add, Units.val_mul, norm_mul, hu, mul_one, Units.val_zpow_eq_zpow_val, norm_zpow, norm_piU]
    constructor
    · intro h
      have h' : ((P2mUnitWeightK.qv K v)⁻¹) ^ (-n + m) = ((P2mUnitWeightK.qv K v)⁻¹) ^ (0 : ℤ) := by rw [h, zpow_zero]
      have hinj := zpow_right_injective₀ (inv_pos.2 (P2mUnitWeightK.qv_pos K v))
        (inv_lt_one_of_one_lt₀ (P2mUnitWeightK.one_lt_qv K v)).ne h'
      omega
    · intro h; rw [h, neg_add_cancel, zpow_zero]
  rw [hkey]
  constructor
  · intro hmem
    exact zpow_mul_mem_box_unique K L v w₀ (norm_pos_iff.2 hp) (by rw [← hnorm]; exact hmem) hn
  · intro hmn
    subst hmn
    show _ ∈ box K L v w₀
    rw [box, Set.mem_setOf_eq, hnorm]
    exact hn

end E8A.A0
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

namespace E8A
namespace A0

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "EE" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w₀)

theorem toTensorGL_diag_apply (d₁ d₂ : Kvˣ) (i : Fin 2) :
    ((toTensorGL K L Kv (diagUnits2 d₁ d₂) : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) i i =
      (1 : L) ⊗ₜ[K] (((diagUnits2 d₁ d₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) i i) := rfl

theorem diag00 (d₁ d₂ : Kvˣ) : (((diagUnits2 d₁ d₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 0) = (d₁ : Kv) := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl

theorem diag11 (d₁ d₂ : Kvˣ) : (((diagUnits2 d₁ d₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 1 1) = (d₂ : Kv) := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl

theorem map_cw_toTensorGL (w : v.Extension (𝓞 L)) (g : GL (Fin 2) Kv) :
    Matrix.GeneralLinearGroup.map
        ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
          (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
            EE →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) (toTensorGL K L Kv g) =
      Matrix.GeneralLinearGroup.map (algebraMap Kv (w.1.adicCompletion L)) g := by
  apply Units.ext
  ext i j
  simp only [toTensorGL, Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply, RingHom.coe_comp,
    Function.comp_apply, Pi.evalRingHom_apply]
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v
      ((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE).toRingHom ((g : Matrix (Fin 2) (Fin 2) Kv) i j)) w = _
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] ((g : Matrix (Fin 2) (Fin 2) Kv) i j)) w = _
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]

include w₀ in

theorem toTensorGL_diag_mem_iff (e₁ e₂ : Kvˣ) :
    toTensorGL K L Kv (diagUnits2 e₁ e₂) ∈ semiLocalIntegralSet K L v ↔ ‖(e₁ : Kv)‖ = 1 ∧ ‖(e₂ : Kv)‖ = 1 := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  rw [(AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    K L v).1]
  constructor
  · intro h
    have h0 := h w₀
    rw [map_cw_toTensorGL, P2mInertUnitE2.map_diagUnits2, P2mInertUnitE2.diagUnits2_mem_iff] at h0
    simp only [Units.coe_map, MonoidHom.coe_coe] at h0
    exact ⟨(norm_algebraMap_eq_one_iff K L v w₀ _).1 h0.1, (norm_algebraMap_eq_one_iff K L v w₀ _).1 h0.2⟩
  · rintro ⟨h1, h2⟩ w
    rw [map_cw_toTensorGL, P2mInertUnitE2.map_diagUnits2, P2mInertUnitE2.diagUnits2_mem_iff]
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact ⟨(norm_algebraMap_eq_one_iff K L v w _).2 h1, (norm_algebraMap_eq_one_iff K L v w _).2 h2⟩

theorem section_property
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : (EE)ˣ) (a b : Kvˣ) (hab : a ≠ b)
    (hN : normString K L Kv σ (diagUnits2 α β) = toTensorGL K L Kv (diagUnits2 a b))
    (τ' : @Measure (twistedCentralizer K L Kv σ (diagUnits2 α β)) (twistedCentralizerBorel K L Kv σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L Kv σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {x | (x : GL (Fin 2) EE) ∈ semiLocalIntegralSet K L v} = 1)
    (p : EE × EE) (hp1 : IsUnit p.1) (hp2 : IsUnit p.2) :
    @integral _ ℝ _ _ (twistedCentralizerBorel K L Kv σ (diagUnits2 α β)) τ'
      (fun t => βs K L v w₀ ((((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 0 0) * p.1,
        (((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 1 1) * p.2)) = 1 := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  letI : MeasurableSpace (twistedCentralizer K L Kv σ (diagUnits2 α β)) := twistedCentralizerBorel K L Kv σ (diagUnits2 α β)
  haveI : BorelSpace (twistedCentralizer K L Kv σ (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'

  have hT : twistedCentralizer K L Kv σ (diagUnits2 α β) =
      (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) Kv))).map (toTensorGL K L Kv) :=
    AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
      K L σ hgen Kv a b (isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))) α β hN
  have hdiag : ∀ t : twistedCentralizer K L Kv σ (diagUnits2 α β), ∃ d₁ d₂ : Kvˣ,
      (t : GL (Fin 2) EE) = toTensorGL K L Kv (diagUnits2 d₁ d₂) := by
    intro t
    have ht : (t : GL (Fin 2) EE) ∈ (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) Kv))).map (toTensorGL K L Kv) := by
      rw [← hT]; exact t.2
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 ht
    have h := P2mUnitWeightK.centralizer_eq_diagUnits2 K v hab ⟨s, hs⟩
    exact ⟨_, _, by rw [← hst]; exact congrArg (toTensorGL K L Kv) h⟩
  have hmemT : ∀ d₁ d₂ : Kvˣ, toTensorGL K L Kv (diagUnits2 d₁ d₂) ∈ twistedCentralizer K L Kv σ (diagUnits2 α β) := by
    intro d₁ d₂
    rw [hT]
    exact Subgroup.mem_map_of_mem _ (P2mUnitWeightK.diagUnits2_mem_centralizer K v hab d₁ d₂)

  have hp1' : cw K L v w₀ p.1 ≠ 0 := cw_ne_zero_of_isUnit K L v w₀ hp1
  have hp2' : cw K L v w₀ p.2 ≠ 0 := cw_ne_zero_of_isUnit K L v w₀ hp2
  obtain ⟨n₁, hn₁⟩ := exists_zpow_mul_mem_box K L v w₀ _ (norm_pos_iff.2 hp1')
  obtain ⟨n₂, hn₂⟩ := exists_zpow_mul_mem_box K L v w₀ _ (norm_pos_iff.2 hp2')
  set t₀ : twistedCentralizer K L Kv σ (diagUnits2 α β) :=
    ⟨toTensorGL K L Kv (diagUnits2 (piU K v ^ n₁) (piU K v ^ n₂)), hmemT _ _⟩ with ht₀
  set B : Set (twistedCentralizer K L Kv σ (diagUnits2 α β)) := {x | (x : GL (Fin 2) EE) ∈ semiLocalIntegralSet K L v}
    with hB
  have hBm : MeasurableSet B := ((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).measurableSet

  have hfun : (fun t : twistedCentralizer K L Kv σ (diagUnits2 α β) =>
      βs K L v w₀ ((((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 0 0) * p.1,
        (((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 1 1) * p.2)) =
      ((fun t => t₀⁻¹ * t) ⁻¹' B).indicator fun _ => (1 : ℝ) := by
    funext t
    obtain ⟨d₁, d₂, hd⟩ := hdiag t
    have h00 : (((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 0 0) = (1 : L) ⊗ₜ[K] ((d₁ : Kvˣ) : Kv) := by
      rw [hd, toTensorGL_diag_apply, diag00]
    have h11 : (((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 1 1) = (1 : L) ⊗ₜ[K] ((d₂ : Kvˣ) : Kv) := by
      rw [hd, toTensorGL_diag_apply, diag11]
    have hmem : t ∈ (fun t => t₀⁻¹ * t) ⁻¹' B ↔
        ‖((piU K v ^ (-n₁) * d₁ : Kvˣ) : Kv)‖ = 1 ∧ ‖((piU K v ^ (-n₂) * d₂ : Kvˣ) : Kv)‖ = 1 := by
      rw [Set.mem_preimage, hB, Set.mem_setOf_eq]
      have : ((t₀⁻¹ * t : twistedCentralizer K L Kv σ (diagUnits2 α β)) : GL (Fin 2) EE) =
          toTensorGL K L Kv (diagUnits2 (piU K v ^ (-n₁) * d₁) (piU K v ^ (-n₂) * d₂)) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hd]
        change (toTensorGL K L Kv (diagUnits2 (piU K v ^ n₁) (piU K v ^ n₂)))⁻¹ * toTensorGL K L Kv (diagUnits2 d₁ d₂) = _
        rw [← map_inv, ← map_mul, P2mInertUnitE2.diagUnits2_inv, P2mInertUnitE2.diagUnits2_mul_diagUnits2, zpow_neg, zpow_neg]
      rw [this, toTensorGL_diag_mem_iff K L v w₀]
    unfold βs
    rw [Set.indicator_apply, Set.indicator_apply]
    have hiff : ((((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 0 0) * p.1,
        (((t : GL (Fin 2) EE) : Matrix (Fin 2) (Fin 2) EE) 1 1) * p.2) ∈ box K L v w₀ ×ˢ box K L v w₀ ↔
        t ∈ (fun t => t₀⁻¹ * t) ⁻¹' B := by
      rw [hmem, Set.mem_prod, h00, h11, tmul_mul_mem_box_iff K L v w₀ hp1' n₁ hn₁ d₁,
        tmul_mul_mem_box_iff K L v w₀ hp2' n₂ hn₂ d₂]
    by_cases h : t ∈ (fun t => t₀⁻¹ * t) ⁻¹' B
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  rw [hfun, integral_indicator_const _ (measurableSet_preimage (measurable_const_mul _) hBm), smul_eq_mul, mul_one,
    measureReal_def, measure_preimage_mul, hB, hτ'1, ENNReal.toReal_one]

end E8A.A0
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

namespace E8A
namespace A0

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm Topology
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "EE" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w₀)

theorem isCompact_annulus (r₁ r₂ : ℝ) :
    IsCompact {d : Kvˣ | (r₁ ≤ ‖(d : Kv)‖ ∧ ‖(d : Kv)‖ ≤ r₂) ∧
      (r₂⁻¹ ≤ ‖((d⁻¹ : Kvˣ) : Kv)‖ ∧ ‖((d⁻¹ : Kvˣ) : Kv)‖ ≤ r₁⁻¹)} := by
  have hc : ∀ (s₁ s₂ : ℝ), IsCompact {x : Kv | s₁ ≤ ‖x‖ ∧ ‖x‖ ≤ s₂} := by
    intro s₁ s₂
    refine (isCompact_closedBall (0 : Kv) s₂).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.2
  have hK : IsCompact ({x : Kv | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} ×ˢ (MulOpposite.op '' {x : Kv | r₂⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ r₁⁻¹})) :=
    (hc r₁ r₂).prod ((hc _ _).image MulOpposite.continuous_op)
  have hpre : {d : Kvˣ | (r₁ ≤ ‖(d : Kv)‖ ∧ ‖(d : Kv)‖ ≤ r₂) ∧
      (r₂⁻¹ ≤ ‖((d⁻¹ : Kvˣ) : Kv)‖ ∧ ‖((d⁻¹ : Kvˣ) : Kv)‖ ≤ r₁⁻¹)} =
      Units.embedProduct Kv ⁻¹' ({x : Kv | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} ×ˢ (MulOpposite.op '' {x : Kv | r₂⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ r₁⁻¹})) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, ⟨y, hy, hy'⟩⟩
      refine ⟨h1, ?_⟩
      have : y = ((d⁻¹ : Kvˣ) : Kv) := MulOpposite.op_injective hy'
      rw [← this]; exact hy
  rw [hpre]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage hK

theorem exists_isCompact_norm_algebraMap_mem (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) :
    ∃ P : Set Kvˣ, IsCompact P ∧ ∀ d : Kvˣ,
      r₁ ≤ ‖algebraMap Kv Lw (d : Kv)‖ → ‖algebraMap Kv Lw (d : Kv)‖ ≤ r₂ → d ∈ P := by
  have hQ := one_lt_Q K L v w₀
  have hQ0 := Q_pos K L v w₀
  have hq := P2mUnitWeightK.one_lt_qv K v
  have hq0 := P2mUnitWeightK.qv_pos K v
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one hr₁ (inv_lt_one_of_one_lt₀ hQ)
  obtain ⟨N₂, hN₂⟩ := pow_unbounded_of_one_lt r₂ hQ
  refine ⟨{d : Kvˣ | ((P2mUnitWeightK.qv K v) ^ (-(N₁ : ℤ)) ≤ ‖(d : Kv)‖ ∧ ‖(d : Kv)‖ ≤ (P2mUnitWeightK.qv K v) ^ (N₂ : ℤ)) ∧
      (((P2mUnitWeightK.qv K v) ^ (N₂ : ℤ))⁻¹ ≤ ‖((d⁻¹ : Kvˣ) : Kv)‖ ∧
        ‖((d⁻¹ : Kvˣ) : Kv)‖ ≤ ((P2mUnitWeightK.qv K v) ^ (-(N₁ : ℤ)))⁻¹)},
    isCompact_annulus K v _ _, fun d h1 h2 => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_eq_piU_zpow_mul K v d
  rw [norm_algebraMap_piU_zpow_mul K L v w₀ n hu] at h1 h2
  have hn1 : n < N₁ := by
    by_contra hle
    push_neg at hle
    have : Q K L v w₀ ^ (-n) ≤ (Q K L v w₀)⁻¹ ^ N₁ := by
      rw [← zpow_natCast, inv_zpow', zpow_le_zpow_iff_right₀ hQ]; omega
    linarith
  have hn2 : -(N₂ : ℤ) < n := by
    by_contra hle
    push_neg at hle
    have : Q K L v w₀ ^ (N₂ : ℤ) ≤ Q K L v w₀ ^ (-n) := by
      rw [zpow_le_zpow_iff_right₀ hQ]; omega
    rw [zpow_natCast] at this
    linarith
  have hnorm : ‖((piU K v ^ n * u : Kvˣ) : Kv)‖ = P2mUnitWeightK.qv K v ^ (-n) := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, norm_piU, hu, mul_one, inv_zpow']
  have hnorm' : ‖(((piU K v ^ n * u)⁻¹ : Kvˣ) : Kv)‖ = (P2mUnitWeightK.qv K v ^ (-n))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hnorm]
  simp only [Set.mem_setOf_eq, hnorm, hnorm']
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [zpow_le_zpow_iff_right₀ hq]; omega
  · rw [zpow_le_zpow_iff_right₀ hq]; omega
  · rw [inv_le_inv₀ (zpow_pos hq0 _) (zpow_pos hq0 _), zpow_le_zpow_iff_right₀ hq]; omega
  · rw [inv_le_inv₀ (zpow_pos hq0 _) (zpow_pos hq0 _), zpow_le_zpow_iff_right₀ hq]; omega

theorem exists_bounds_of_isCompact {C : Set (EE)ˣ} (hC : IsCompact C) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ c ∈ C, m ≤ ‖cw K L v w₀ (c : EE)‖ ∧ ‖cw K L v w₀ (c : EE)‖ ≤ M := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  have hcont : Continuous fun c : (EE)ˣ => ‖cw K L v w₀ (c : EE)‖ :=
    ((continuous_cw K L v w₀).comp Units.continuous_val).norm
  by_cases hne : C.Nonempty
  · obtain ⟨c₀, hc₀, hmin⟩ := hC.exists_isMinOn hne hcont.continuousOn
    obtain ⟨c₁, hc₁, hmax⟩ := hC.exists_isMaxOn hne hcont.continuousOn
    exact ⟨‖cw K L v w₀ (c₀ : EE)‖, ‖cw K L v w₀ (c₁ : EE)‖,
      norm_pos_iff.2 (cw_ne_zero_of_isUnit K L v w₀ (Units.isUnit c₀)), hmax hc₀,
      fun c hc => ⟨hmin hc, hmax hc⟩⟩
  · exact ⟨1, 1, one_pos, le_rfl, fun c hc => absurd ⟨c, hc⟩ hne⟩

def iotaU : Kvˣ →* (EE)ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE) : Kv →* EE)

theorem coe_iotaU (d : Kvˣ) : ((iotaU K L v d : (EE)ˣ) : EE) = (1 : L) ⊗ₜ[K] (d : Kv) := rfl

theorem continuous_iotaU [FiniteDimensional K L] : Continuous (iotaU K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  apply Continuous.units_map
  have h : Continuous (algebraMap Kv EE) := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap Kv EE)
  have heq : (((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE) : Kv →* EE) : Kv → EE) = algebraMap Kv EE := by
    funext r
    show Algebra.TensorProduct.includeRight (R := K) (A := L) r = algebraMap Kv EE r
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.RightActions.algebraMap_eval]
  rw [heq]; exact h

theorem properness
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (C : Set ((EE)ˣ × (EE)ˣ)) (hC : IsCompact C) :
    ∃ D : Set ((EE)ˣ × (EE)ˣ), IsCompact D ∧
      ∀ q : (EE)ˣ × (EE)ˣ, βs K L v w₀ ((q.1 : EE), (q.2 : EE)) ≠ 0 →
        ((Units.map (sigmaTensor K L Kv σ : EE →* EE)) q.1 * q.1⁻¹,
          (Units.map (sigmaTensor K L Kv σ : EE →* EE)) q.2 * q.2⁻¹) ∈ C → q ∈ D := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  obtain ⟨C₁, hC₁, h₁⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
      K L σ hgen v (Prod.fst '' C) (hC.image continuous_fst)
  obtain ⟨C₂, hC₂, h₂⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
      K L σ hgen v (Prod.snd '' C) (hC.image continuous_snd)
  obtain ⟨m₁, M₁, hm₁, hmM₁, hb₁⟩ := exists_bounds_of_isCompact K L v w₀ hC₁
  obtain ⟨m₂, M₂, hm₂, hmM₂, hb₂⟩ := exists_bounds_of_isCompact K L v w₀ hC₂
  have hQ0 := Q_pos K L v w₀
  obtain ⟨P₁, hP₁, hP₁mem⟩ := exists_isCompact_norm_algebraMap_mem K L v w₀ m₁ (M₁ * Q K L v w₀) hm₁
  obtain ⟨P₂, hP₂, hP₂mem⟩ := exists_isCompact_norm_algebraMap_mem K L v w₀ m₂ (M₂ * Q K L v w₀) hm₂
  set F : Kvˣ × (EE)ˣ → (EE)ˣ := fun pc => (iotaU K L v pc.1)⁻¹ * pc.2 with hF
  have hFc : Continuous F := ((continuous_iotaU K L v).comp continuous_fst).inv.mul continuous_snd
  refine ⟨(F '' (P₁ ×ˢ C₁)) ×ˢ (F '' (P₂ ×ˢ C₂)), ((hP₁.prod hC₁).image hFc).prod ((hP₂.prod hC₂).image hFc), ?_⟩
  intro q hq hqC
  rw [βs_ne_zero_iff] at hq

  have key : ∀ (qi : (EE)ˣ) (Ci : Set (EE)ˣ) (Pi : Set Kvˣ) (mi Mi : ℝ), 0 < mi →
      (∀ c ∈ Ci, mi ≤ ‖cw K L v w₀ (c : EE)‖ ∧ ‖cw K L v w₀ (c : EE)‖ ≤ Mi) →
      (∀ d : Kvˣ, mi ≤ ‖algebraMap Kv Lw (d : Kv)‖ → ‖algebraMap Kv Lw (d : Kv)‖ ≤ Mi * Q K L v w₀ → d ∈ Pi) →
      (qi : EE) ∈ box K L v w₀ →
      (∃ p : Kvˣ, Units.map ((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE) : Kv →* EE) p * qi ∈ Ci) →
      qi ∈ F '' (Pi ×ˢ Ci) := by
    intro qi Ci Pi mi Mi hmi hbi hPi hbox ⟨p, hp⟩
    refine ⟨(p, iotaU K L v p * qi), ⟨?_, hp⟩, by simp only [hF, inv_mul_cancel_left]⟩
    have hc := hbi _ hp
    have hval : ((Units.map ((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE) : Kv →* EE) p : (EE)ˣ) : EE) =
        (1 : L) ⊗ₜ[K] (p : Kv) := rfl
    have hcw : cw K L v w₀ ((Units.map ((Algebra.TensorProduct.includeRight : Kv →ₐ[K] EE) : Kv →* EE) p * qi : (EE)ˣ) : EE) =
        algebraMap Kv Lw (p : Kv) * cw K L v w₀ (qi : EE) := by
      rw [Units.val_mul, cw_mul, hval, cw_tmul_one]
    rw [hcw, norm_mul] at hc
    rw [box, Set.mem_setOf_eq] at hbox
    have hN0 : 0 ≤ ‖algebraMap Kv Lw (p : Kv)‖ := norm_nonneg _
    apply hPi
    ·
      exact hc.1.trans (mul_le_of_le_one_right hN0 hbox.2)
    ·
      have h3 : ‖algebraMap Kv Lw (p : Kv)‖ * (Q K L v w₀)⁻¹ ≤ Mi :=
        (mul_le_mul_of_nonneg_left hbox.1.le hN0).trans hc.2
      rwa [mul_inv_le_iff₀ hQ0] at h3
  refine ⟨key q.1 C₁ P₁ m₁ M₁ hm₁ hb₁ hP₁mem hq.1 (h₁ q.1 ⟨_, hqC, rfl⟩),
    key q.2 C₂ P₂ m₂ M₂ hm₂ hb₂ hP₂mem hq.2 (h₂ q.2 ⟨_, hqC, rfl⟩)⟩

end E8A.A0
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

namespace E8A
namespace A0

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨⟨Q, hQmax.isPrime, hQ⟩, ?_⟩⟩
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact hQover.over.symm

end E8A.A0
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mUnitWeightK P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq.P2mInertUnitE2"

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] :
    ∃ βs : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ, Measurable βs ∧ (∀ p, 0 ≤ βs p ∧ βs p ≤ 1) ∧
      (∀ C : Set ((L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)ˣ), IsCompact C →
        ∃ D : Set ((L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)ˣ), IsCompact D ∧
          ∀ q : (L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)ˣ, βs ((q.1 : (L ⊗[K] v.adicCompletion K)), (q.2 : (L ⊗[K] v.adicCompletion K))) ≠ 0 →
            ((Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) q.1 * q.1⁻¹, (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) q.2 * q.2⁻¹) ∈ C → q ∈ D) ∧
      ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ), a ≠ b →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
          @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
            (fun t => βs ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
              (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1 := by
  obtain ⟨w₀⟩ := E8A.A0.nonempty_extension K L v
  refine ⟨E8A.A0.βs K L v w₀, E8A.A0.measurable_βs K L v w₀, E8A.A0.βs_nonneg_le_one K L v w₀,
    fun C hC => E8A.A0.properness K L v w₀ σ hgen C hC, ?_⟩
  intro α β a b hab hN τ' hτ' hτ'1 p hp1 hp2
  exact E8A.A0.section_property K L v w₀ σ hgen α β a b hab hN τ' hτ' hτ'1 p hp1 hp2

end S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_torusSection_forall_normString_diagUnits2_eq (solution)
