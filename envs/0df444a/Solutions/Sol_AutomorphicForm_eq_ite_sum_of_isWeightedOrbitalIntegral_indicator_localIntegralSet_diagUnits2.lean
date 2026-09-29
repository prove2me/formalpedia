-- Prove2me | solution 1 for AutomorphicForm.eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1d3c309e-287c-53a3-ba2a-15b5cfdd9896

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2

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

theorem diagUnits2_mul_diagUnits2 (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 (s₁ * t₁) (s₂ * t₂) : GL (Fin 2) Kv) := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

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

theorem diagUnits2_mem_iff (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localIntegralSet K v ↔ ‖(t₁ : Kv)‖ = 1 ∧ ‖(t₂ : Kv)‖ = 1 := by
  have := unipotent_conj_mem_iff K v t₁ t₂ 0
  rw [unipotentGL2_zero, inv_one, one_mul, mul_one] at this
  rw [this]
  simp

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
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2.P2mUnitWeightK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2.P2mUnitWeightK"

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) J) :
    J = if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (((2 * Real.log (Ideal.absNorm v.asIdeal) *
            ∑ s ∈ Finset.range (m.toNat + 1),
              (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by
  split_ifs with h
  · exact P2mUnitWeightK.main_units K v hab h.1 h.2 m hm τ hτ hτ1 J hJ
  · exact P2mUnitWeightK.main_not_units K v h τ J hJ

end S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2 (solution)
