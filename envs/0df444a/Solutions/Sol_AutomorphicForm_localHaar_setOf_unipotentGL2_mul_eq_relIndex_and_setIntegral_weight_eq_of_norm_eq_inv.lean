-- Prove2me | solution 1 for AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f5f04143-6863-5d9e-a070-ec5047b0bcfd

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace P2mLatticeShells

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

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv K v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hx
    exact Or.inr ⟨k, hk⟩

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

end Norms

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

end IntegralPoints

section Algebra

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem unipotentGL2_inv (y : Kv) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

end Algebra

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

end Instances

section Shells

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

abbrev OK : AddSubgroup Kv := (v.adicCompletionIntegers K).toAddSubgroup

variable (Λ : AddSubgroup (v.adicCompletion K)) (π : v.adicCompletion K)

def Lam (s : ℕ) : AddSubgroup Kv := Λ ⊓ (OK K v).comap (AddMonoidHom.mulLeft (π ^ s))

theorem mem_Lam (s : ℕ) (y : Kv) : y ∈ Lam K v Λ π s ↔ y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K := by
  rw [Lam, AddSubgroup.mem_inf, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
  exact Iff.rfl

def V (s : ℕ) : Set (GL (Fin 2) Kv) :=
  {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), (y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K) ∧
    k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem mul_mem_V {s : ℕ} {y : Kv} {k : GL (Fin 2) Kv} (hy : y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K)
    (hk : k ∈ localIntegralSet K v) : unipotentGL2 y * k ∈ V K v Λ π s :=
  ⟨y, k, hy, hk, rfl⟩

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

theorem measurableSet_V (s : ℕ) : MeasurableSet (V K v Λ π s) := (isOpen_V K v Λ π s).measurableSet

def Uball (s : ℕ) : Set (GL (Fin 2) Kv) :=
  (fun p : Kv × GL (Fin 2) Kv => unipotentGL2 p.1 * p.2) '' ({y : Kv | ‖y‖ ≤ qv K v ^ s} ×ˢ localIntegralSet K v)

theorem isCompact_Uball (s : ℕ) : IsCompact (Uball K v s) := by
  refine IsCompact.image (IsCompact.prod ?_ (isCompact_localIntegralSet K v)) ?_
  · have : {y : Kv | ‖y‖ ≤ qv K v ^ s} = Metric.closedBall 0 (qv K v ^ s) := by
      ext y; simp
    rw [this]
    exact isCompact_closedBall _ _
  · exact ((continuous_unipotentGL2' K v).comp continuous_fst).mul continuous_snd

theorem weight_of_mem_V_zero {x : GL (Fin 2) Kv} (hx : x ∈ V K v Λ π 0) : LocalWeight.weight x = 0 := by
  obtain ⟨y, k, hy, hk, rfl⟩ := hx
  have hy2 : π ^ 0 * y ∈ v.adicCompletionIntegers K := hy.2
  rw [pow_zero, one_mul, mem_integers_iff_norm] at hy2
  rw [weight_unipotentGL2_mul K v hk, max_eq_left hy2, Real.log_one, mul_zero]

abbrev Qt (s : ℕ) : Type := Lam K v Λ π s ⧸ (OK K v).addSubgroupOf (Lam K v Λ π s)

def rep (s : ℕ) (c : Qt K v Λ π s) : Kv := ((Quotient.out c : Lam K v Λ π s) : Kv)

theorem rep_mem (s : ℕ) (c : Qt K v Λ π s) :
    rep K v Λ π s c ∈ Λ ∧ π ^ s * rep K v Λ π s c ∈ v.adicCompletionIntegers K :=
  (mem_Lam K v Λ π s _).1 (Quotient.out c : Lam K v Λ π s).2

def coset (s : ℕ) (c : Qt K v Λ π s) : Set (GL (Fin 2) Kv) :=
  (fun x => unipotentGL2 (rep K v Λ π s c) * x) '' localIntegralSet K v

theorem mk_eq_iff {s : ℕ} (y y' : Lam K v Λ π s) :
    (QuotientAddGroup.mk y : Qt K v Λ π s) = QuotientAddGroup.mk y' ↔
      (y' : Kv) - y ∈ v.adicCompletionIntegers K := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, sub_eq_neg_add]
  rfl

theorem sub_rep_mem {s : ℕ} (y : Lam K v Λ π s) :
    (y : Kv) - rep K v Λ π s (QuotientAddGroup.mk y) ∈ v.adicCompletionIntegers K := by
  have hout : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk y : Qt K v Λ π s)) : Qt K v Λ π s) =
      QuotientAddGroup.mk y := QuotientAddGroup.out_eq' _
  exact (mk_eq_iff K v Λ π (Quotient.out (QuotientAddGroup.mk y : Qt K v Λ π s)) y).1 hout

theorem V_eq_iUnion_coset (s : ℕ) : V K v Λ π s = ⋃ c : Qt K v Λ π s, coset K v Λ π s c := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩
    have hy' : y ∈ Lam K v Λ π s := (mem_Lam K v Λ π s y).2 hy
    have hdiff := sub_rep_mem K v Λ π ⟨y, hy'⟩
    refine ⟨QuotientAddGroup.mk ⟨y, hy'⟩, ⟨unipotentGL2 (y - rep K v Λ π s (QuotientAddGroup.mk ⟨y, hy'⟩)) * k,
      mul_mem_localIntegralSet K v ((unipotentGL2_mem_iff K v _).2 ((mem_integers_iff_norm K v _).1 hdiff)) hk, ?_⟩⟩
    change unipotentGL2 _ * (unipotentGL2 _ * k) = unipotentGL2 y * k
    rw [← mul_assoc, ← unipotentGL2_add, add_sub_cancel]
  · rintro ⟨c, ⟨k, hk, rfl⟩⟩
    exact ⟨rep K v Λ π s c, k, rep_mem K v Λ π s c, hk, rfl⟩

theorem pairwise_disjoint_coset (s : ℕ) :
    Pairwise (Function.onFun Disjoint fun c : Qt K v Λ π s => coset K v Λ π s c) := by
  intro c c' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨k, hk, rfl⟩ ⟨k', hk', h⟩
  apply hne
  have h1 : ‖rep K v Λ π s c - rep K v Λ π s c'‖ ≤ 1 := norm_sub_le_one_of_eq K v hk' hk h
  have h2 : (QuotientAddGroup.mk (Quotient.out c') : Qt K v Λ π s) = QuotientAddGroup.mk (Quotient.out c) :=
    (mk_eq_iff K v Λ π (Quotient.out c') (Quotient.out c)).2 ((mem_integers_iff_norm K v _).2 h1)
  rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq', eq_comm] at h2

theorem measurableSet_coset {s : ℕ} (c : Qt K v Λ π s) : MeasurableSet (coset K v Λ π s c) := by
  rw [coset, Set.image_mul_left]
  exact measurableSet_preimage (measurable_const_mul _) (isOpen_localIntegralSet K v).measurableSet

theorem measure_coset {s : ℕ} (c : Qt K v Λ π s) : localHaar K v (coset K v Λ π s c) = 1 := by
  rw [coset, Set.image_mul_left, measure_preimage_mul, localHaar_localIntegralSet]

theorem measure_V {s : ℕ} (hfin : (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    localHaar K v (V K v Λ π s) = ((OK K v).relIndex (Lam K v Λ π s) : ℝ≥0∞) := by
  haveI : Finite (Qt K v Λ π s) := AddSubgroup.index_ne_zero_iff_finite.1 hfin
  letI : Fintype (Qt K v Λ π s) := Fintype.ofFinite _
  rw [V_eq_iUnion_coset, measure_iUnion (pairwise_disjoint_coset K v Λ π s) (measurableSet_coset K v Λ π),
    tsum_fintype]
  simp only [measure_coset, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

theorem measureReal_V {s : ℕ} (hfin : (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    (localHaar K v).real (V K v Λ π s) = ((OK K v).relIndex (Lam K v Λ π s) : ℝ) := by
  rw [measureReal_def, measure_V K v Λ π hfin, ENNReal.toReal_natCast]

theorem measure_V_lt_top {s : ℕ} (hfin : (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    localHaar K v (V K v Λ π s) < ⊤ := by
  rw [measure_V K v Λ π hfin]; exact ENNReal.natCast_lt_top _

variable (hπ : ‖π‖ = (qv K v)⁻¹)
include hπ

theorem norm_pi_pow (n : ℕ) : ‖π ^ n‖ = (qv K v ^ n)⁻¹ := by
  rw [norm_pow, hπ, inv_pow]

theorem pow_mul_mem_iff (s : ℕ) (y : Kv) : π ^ s * y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ qv K v ^ s := by
  rw [mem_integers_iff_norm, norm_mul, norm_pi_pow K v π hπ, inv_mul_le_iff₀ (pow_pos (qv_pos K v) _), mul_one]

theorem pow_succ_mul_mem {s : ℕ} {y : Kv} (hy : π ^ s * y ∈ v.adicCompletionIntegers K) :
    π ^ (s + 1) * y ∈ v.adicCompletionIntegers K := by
  rw [pow_mul_mem_iff K v π hπ] at hy ⊢
  exact hy.trans (pow_le_pow_right₀ (one_lt_qv K v).le (Nat.le_succ s))

theorem Lam_mono (s : ℕ) : Lam K v Λ π s ≤ Lam K v Λ π (s + 1) := by
  intro y hy
  rw [mem_Lam] at hy ⊢
  exact ⟨hy.1, pow_succ_mul_mem K v π hπ hy.2⟩

theorem Lam_mono' {s t : ℕ} (hst : s ≤ t) : Lam K v Λ π s ≤ Lam K v Λ π t := by
  induction hst with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Lam_mono K v Λ π hπ _)

theorem V_mono (s : ℕ) : V K v Λ π s ⊆ V K v Λ π (s + 1) := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  exact ⟨y, k, ⟨hy.1, pow_succ_mul_mem K v π hπ hy.2⟩, hk, rfl⟩

theorem V_subset_Uball (s : ℕ) : V K v Λ π s ⊆ Uball K v s := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  exact ⟨(y, k), ⟨(pow_mul_mem_iff K v π hπ s y).1 hy.2, hk⟩, rfl⟩

theorem weight_of_mem_V_diff {s : ℕ} {x : GL (Fin 2) Kv} (hx : x ∈ V K v Λ π (s + 1) \ V K v Λ π s) :
    LocalWeight.weight x = 2 * ((s + 1 : ℕ) : ℝ) * Real.log (qv K v) := by
  obtain ⟨⟨y, k, hy, hk, rfl⟩, hx2⟩ := hx
  have hys : ¬ (y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K) := fun h => hx2 (mul_mem_V K v Λ π h hk)
  rw [not_and, pow_mul_mem_iff K v π hπ] at hys
  have hlt : qv K v ^ s < ‖y‖ := not_le.1 (hys hy.1)
  have hle : ‖y‖ ≤ qv K v ^ (s + 1) := (pow_mul_mem_iff K v π hπ (s + 1) y).1 hy.2
  have hge : qv K v ^ (s + 1) ≤ ‖y‖ := by
    have := zpow_add_one_le_norm_of_lt K v (n := (s : ℤ)) (by exact_mod_cast hlt)
    exact_mod_cast this
  have hn : ‖y‖ = qv K v ^ (s + 1) := le_antisymm hle hge
  rw [weight_unipotentGL2_mul K v hk, hn, max_eq_right (one_le_pow₀ (one_lt_qv K v).le), Real.log_pow]
  ring

theorem integrableOn_weight_V (s : ℕ) : IntegrableOn LocalWeight.weight (V K v Λ π s) (localHaar K v) :=
  (ContinuousOn.integrableOn_compact (isCompact_Uball K v s) WeightKit.continuous_weight.continuousOn).mono_set
    (V_subset_Uball K v Λ π hπ s)

theorem integral_weight_V (m : ℕ) (hfin : ∀ s ≤ m, (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    ∫ x in V K v Λ π m, LocalWeight.weight x ∂(localHaar K v) =
      2 * Real.log (qv K v) *
        ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
          (((OK K v).relIndex (Lam K v Λ π (s + 1)) : ℝ) - ((OK K v).relIndex (Lam K v Λ π s) : ℝ)) := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, mul_zero]
    rw [setIntegral_congr_fun (measurableSet_V K v Λ π 0) (fun x hx => weight_of_mem_V_zero K v Λ π hx)]
    simp
  | succ m ih =>
    have hsub : V K v Λ π m ⊆ V K v Λ π (m + 1) := V_mono K v Λ π hπ m
    have hfin' : ∀ s ≤ m, (OK K v).relIndex (Lam K v Λ π s) ≠ 0 := fun s hs => hfin s (hs.trans (Nat.le_succ m))
    have hsplit : ∫ x in V K v Λ π (m + 1), LocalWeight.weight x ∂(localHaar K v) =
        (∫ x in V K v Λ π m, LocalWeight.weight x ∂(localHaar K v)) +
          ∫ x in V K v Λ π (m + 1) \ V K v Λ π m, LocalWeight.weight x ∂(localHaar K v) := by
      rw [← setIntegral_union disjoint_sdiff_right ((measurableSet_V K v Λ π (m + 1)).diff (measurableSet_V K v Λ π m))
        (integrableOn_weight_V K v Λ π hπ m) ((integrableOn_weight_V K v Λ π hπ (m + 1)).mono_set Set.diff_subset),
        Set.union_diff_cancel hsub]
    have hshell : ∫ x in V K v Λ π (m + 1) \ V K v Λ π m, LocalWeight.weight x ∂(localHaar K v) =
        (((OK K v).relIndex (Lam K v Λ π (m + 1)) : ℝ) - ((OK K v).relIndex (Lam K v Λ π m) : ℝ)) *
          (2 * ((m + 1 : ℕ) : ℝ) * Real.log (qv K v)) := by
      rw [setIntegral_congr_fun ((measurableSet_V K v Λ π (m + 1)).diff (measurableSet_V K v Λ π m))
        (fun x hx => weight_of_mem_V_diff K v Λ π hπ hx), setIntegral_const, smul_eq_mul,
        measureReal_diff hsub (measurableSet_V K v Λ π m) (measure_V_lt_top K v Λ π (hfin _ le_rfl)).ne,
        measureReal_V K v Λ π (hfin _ le_rfl), measureReal_V K v Λ π (hfin _ (Nat.le_succ m))]
    rw [hsplit, ih hfin', hshell, Finset.sum_range_succ]
    ring

end Shells

end P2mLatticeShells

end

open MeasureTheory NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Λ : AddSubgroup (v.adicCompletion K)) (ϖ : v.adicCompletion K)
    (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (m : ℕ)
    (hfin : ∀ s ≤ m, (v.adicCompletionIntegers K).toAddSubgroup.relIndex
      (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) ≠ 0) :
    (∀ s ≤ m, AutomorphicForm.localHaar K v
        {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ s * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k} =
      (v.adicCompletionIntegers K).toAddSubgroup.relIndex
        (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s)))) ∧
    (∫ x in {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ m * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k},
        AutomorphicForm.LocalWeight.weight x ∂(AutomorphicForm.localHaar K v)) =
      2 * Real.log (Ideal.absNorm v.asIdeal) *
        ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
          (((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ (s + 1)))) : ℝ) -
            ((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) : ℝ)) :=
  ⟨fun s hs => P2mLatticeShells.measure_V K v Λ ϖ (hfin s hs), P2mLatticeShells.integral_weight_V K v Λ ϖ hϖ m hfin⟩

end S_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
end P2MW
export P2MW.S_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv (solution)
