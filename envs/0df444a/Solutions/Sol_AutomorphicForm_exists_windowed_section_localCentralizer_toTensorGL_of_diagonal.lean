-- Prove2me | solution 1 for AutomorphicForm.exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/20a888d2-8eed-5028-a0fa-34b61faf3419

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace BetaWin

open scoped TensorProduct TensorProduct.RightActions

section NormFacts

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_q : 1 < q K v := by
  unfold q; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem q_pos : 0 < q K v := lt_trans one_pos (one_lt_q K v)

theorem q_ne_zero : q K v ≠ 0 := (q_pos K v).ne'

theorem exists_norm_eq_zpow (y : v.adicCompletion K) (hy : y ≠ 0) : ∃ e : ℤ, ‖y‖ = q K v ^ e := by
  have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  unfold q
  push_cast
  rfl

theorem exists_norm_eq_inv : ∃ π : v.adicCompletion K, ‖π‖ = (q K v)⁻¹ := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  refine ⟨((WithVal.equiv (v.valuation K)).symm π : WithVal (v.valuation K)), ?_⟩
  rw [NumberField.FinitePlace.norm_def, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.unzero_coe _
  rw [this, toAdd_ofAdd]
  unfold q
  push_cast
  rw [zpow_neg, zpow_one]

theorem exists_norm_eq_zpow_of_int (e : ℤ) : ∃ π : v.adicCompletion K, ‖π‖ = q K v ^ e := by
  obtain ⟨π, hπ⟩ := exists_norm_eq_inv K v
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, norm_zero] at hπ; exact (inv_pos.mpr (q_pos K v)).ne' hπ.symm
  refine ⟨π ^ (-e), ?_⟩
  rw [norm_zpow, hπ, inv_zpow', neg_neg]

theorem mem_integers_iff_norm_le_one (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.FinitePlace.norm_def,
    ← NNReal.coe_one, NNReal.coe_le_coe,
    WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)]

theorem zpow_q_injective {e e' : ℤ} (h : q K v ^ e = q K v ^ e') : e = e' :=
  zpow_right_injective₀ (q_pos K v) (one_lt_q K v).ne' h

end NormFacts

section NormTensor

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem continuous_algebraNorm :
    Continuous (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI : ContinuousSMul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    IsModuleTopology.toContinuousSMul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  let b := Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  have h : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
      fun s => (Algebra.leftMulMatrix b s).det := funext (Algebra.norm_eq_matrix_det b)
  rw [h]
  haveI : IsModuleTopology (v.adicCompletion K)
      (Matrix (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)))
        (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K))) (v.adicCompletion K)) :=
    inferInstanceAs (IsModuleTopology (v.adicCompletion K)
      (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) →
        Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K))
  refine Continuous.matrix_det ?_
  exact IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap

theorem norm_algebraMap_mul (t : v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K) :
    Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) t * x) =
      t ^ Module.finrank K L * Algebra.norm (v.adicCompletion K) x := by
  rw [map_mul, Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra]

end NormTensor

end BetaWin

namespace BetaWin

open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

section Arith

theorem window_iff (qv : ℝ) (hq : 1 < qv) (n : ℕ) (hn : 0 < n) (c e : ℤ) :
    ((qv⁻¹) ^ n < (qv ^ e) ^ n * qv ^ c ∧ (qv ^ e) ^ n * qv ^ c ≤ 1) ↔ e = (-c) / (n : ℤ) := by
  have hq0 : qv ≠ 0 := (lt_trans one_pos hq).ne'
  have hpow : (qv ^ e) ^ n * qv ^ c = qv ^ ((n : ℤ) * e + c) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq0, mul_comm]
  have hinv : (qv⁻¹) ^ n = qv ^ (-(n : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow, hinv, ← zpow_zero qv, zpow_lt_zpow_iff_right₀ hq, zpow_le_zpow_iff_right₀ hq]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨h1, h2⟩
    have := (Int.ediv_emod_unique (a := -c) (b := n) (r := -c - n * e) (q := e) hn').2
      ⟨by ring, by omega, by omega⟩
    exact this.1.symm
  · intro he
    have h1 := Int.mul_ediv_add_emod (-c) (n : ℤ)
    have h2 := Int.emod_nonneg (-c) hn'.ne'
    have h3 := Int.emod_lt_of_pos (-c) hn'
    subst he
    omega

end Arith

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem mem_localIntegralSet_iff_of_diagonal (s : GL (Fin 2) (v.adicCompletion K))
    (h01 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) :
    s ∈ AutomorphicForm.localIntegralSet K v ↔
      ‖(s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ = 1 ∧
      ‖(s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖ = 1 := by

  have hinv00 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 *
      ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = 1 := by
    have h := congrFun (congrFun (s.mul_inv) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h01, zero_mul, add_zero] at h
    exact h
  have hinv11 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 *
      ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1 := by
    have h := congrFun (congrFun (s.mul_inv) 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h10, zero_mul, zero_add] at h
    exact h
  have hinv01 : ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
    have h := congrFun (congrFun (s.mul_inv) 0) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide), h01, zero_mul, add_zero] at h
    have h00 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hinv00; exact zero_ne_one hinv00
    exact (mul_eq_zero.1 h).resolve_left h00
  have hinv10 : ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    have h := congrFun (congrFun (s.mul_inv) 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide), h10, zero_mul, zero_add] at h
    have h11 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hinv11; exact zero_ne_one hinv11
    exact (mul_eq_zero.1 h).resolve_left h11
  have hi00 : ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
      ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0)⁻¹ :=
    (eq_inv_of_mul_eq_one_right hinv00)
  have hi11 : ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
      ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)⁻¹ :=
    (eq_inv_of_mul_eq_one_right hinv11)
  have h0mem : (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K := zero_mem _
  rw [AutomorphicForm.mem_localIntegralSet]
  simp only [Fin.forall_fin_two, h01, h10, hinv01, hinv10, hi00, hi11, SetLike.mem_coe]
  simp only [mem_integers_iff_norm_le_one, norm_inv, norm_zero, zero_le_one, true_and, and_true]
  have h00 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hinv00; exact zero_ne_one hinv00
  have h11 : (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hinv11; exact zero_ne_one hinv11
  have hp0 : 0 < ‖(s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ := norm_pos_iff.2 h00
  have hp1 : 0 < ‖(s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖ := norm_pos_iff.2 h11
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    exact ⟨le_antisymm ha (by rwa [inv_le_one₀ hp0] at hc), le_antisymm hb (by rwa [inv_le_one₀ hp1] at hd)⟩
  · rintro ⟨ha, hb⟩
    refine ⟨⟨ha.le, hb.le⟩, ?_, ?_⟩
    · rw [ha, inv_one]
    · rw [hb, inv_one]

end Main

end BetaWin

section SolAux

open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem BetaWin.toTensorGL_mul_apply_00 (s : GL (Fin 2) (v.adicCompletion K))
    (u : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0) :
    ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) s * u : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
          ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) *
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hu10, mul_zero, add_zero]
  rfl

theorem BetaWin.toTensorGL_mul_apply_11 (s : GL (Fin 2) (v.adicCompletion K))
    (u : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu01 : (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0) :
    ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) s * u : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
          ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1) *
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hu01, mul_zero, zero_add]
  rfl

theorem BetaWin.offdiag_of_mem_localCentralizer (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (s : GL (Fin 2) (v.adicCompletion K)) (hs : s ∈ AutomorphicForm.localCentralizer K v γ) :
    (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
    (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
  have h := Subgroup.mem_centralizer_singleton_iff.1 hs
  have hM := congrArg (fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) h
  simp only [Units.val_mul, hγ] at hM
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  refine ⟨?_, ?_⟩
  · have : ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1) * (a - b) = 0 := by
      linear_combination (-1 : v.adicCompletion K) * h01
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hab)
  · have : ((s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) * (b - a) = 0 := by
      linear_combination (-1 : v.adicCompletion K) * h10
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hab))

open LanglandsTunnell.CubicInduction (diagUnits2) in
theorem BetaWin.diagUnits2_mem_localCentralizer (a b : v.adicCompletion K)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (x y : (v.adicCompletion K)ˣ) : diagUnits2 x y ∈ AutomorphicForm.localCentralizer K v γ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, hγ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, LanglandsTunnell.CubicInduction.coe_diagUnits2, mul_comm]

end SolAux

open LanglandsTunnell.CubicInduction (diagUnits2) in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (hτ1 : τ {s : AutomorphicForm.localCentralizer K v γ |
      (s : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1) :
    ∃ β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β ∧
      (∀ x, 0 ≤ β x) ∧ (∀ x, β x ≤ 1) ∧
      (∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ s : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (s : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1) ∧
      (∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        β u ≠ 0 →
          (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L <
              ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖ ∧
            ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖ ≤ 1) ∧
          (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L <
              ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ∧
            ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ≤ 1)) := by
  classical

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  letI mC : MeasurableSpace (AutomorphicForm.localCentralizer K v γ) := AutomorphicForm.localCentralizerBorel K v γ
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v γ) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ := hτ
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hq1 := BetaWin.one_lt_q K v
  have hq0 : (0 : ℝ) < BetaWin.q K v := BetaWin.q_pos K v

  let N0 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ := fun g =>
    ‖Algebra.norm (v.adicCompletion K) ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖
  let N1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ := fun g =>
    ‖Algebra.norm (v.adicCompletion K) ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖
  have hN0c : Continuous N0 :=
    ((BetaWin.continuous_algebraNorm K L v).comp (Units.continuous_val.matrix_elem 0 0)).norm
  have hN1c : Continuous N1 :=
    ((BetaWin.continuous_algebraNorm K L v).comp (Units.continuous_val.matrix_elem 1 1)).norm
  let cst : ℝ := ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L
  let S : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    ({g | cst < N0 g} ∩ {g | N0 g ≤ 1}) ∩ ({g | cst < N1 g} ∩ {g | N1 g ≤ 1})
  have hSm : MeasurableSet S :=
    ((measurableSet_lt measurable_const hN0c.measurable).inter
      (measurableSet_le hN0c.measurable measurable_const)).inter
    ((measurableSet_lt measurable_const hN1c.measurable).inter
      (measurableSet_le hN1c.measurable measurable_const))
  refine ⟨S.indicator (fun _ => (1 : ℝ)), measurable_const.indicator hSm,
    fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x,
    fun x => ?_, ?_, ?_⟩
  · by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; exact zero_le_one
  rotate_left
  ·
    intro u _ _ hne
    have hu : u ∈ S := Set.mem_of_indicator_ne_zero hne
    exact ⟨⟨hu.1.1, hu.1.2⟩, ⟨hu.2.1, hu.2.2⟩⟩
  ·
    intro u hu01 hu10
    have hCdiag := BetaWin.offdiag_of_mem_localCentralizer K v a b hab γ hγ

    have hudet : IsUnit ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) := Matrix.isUnits_det_units u
    rw [Matrix.det_fin_two, hu10, mul_zero, sub_zero] at hudet
    have hy0 : Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠ 0 :=
      ((isUnit_of_mul_isUnit_left hudet).map (Algebra.norm (v.adicCompletion K))).ne_zero
    have hy1 : Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) ≠ 0 :=
      ((isUnit_of_mul_isUnit_right hudet).map (Algebra.norm (v.adicCompletion K))).ne_zero
    obtain ⟨c0, hc0⟩ := BetaWin.exists_norm_eq_zpow K v _ hy0
    obtain ⟨c1, hc1⟩ := BetaWin.exists_norm_eq_zpow K v _ hy1
    obtain ⟨π0, hπ0⟩ := BetaWin.exists_norm_eq_zpow_of_int K v ((-c0) / (Module.finrank K L : ℤ))
    obtain ⟨π1, hπ1⟩ := BetaWin.exists_norm_eq_zpow_of_int K v ((-c1) / (Module.finrank K L : ℤ))
    have hz0 : BetaWin.q K v ^ ((-c0) / (Module.finrank K L : ℤ)) ≠ 0 := (zpow_pos hq0 _).ne'
    have hz1 : BetaWin.q K v ^ ((-c1) / (Module.finrank K L : ℤ)) ≠ 0 := (zpow_pos hq0 _).ne'
    have hπ0ne : π0 ≠ 0 := by intro h; rw [h, norm_zero] at hπ0; exact hz0 hπ0.symm
    have hπ1ne : π1 ≠ 0 := by intro h; rw [h, norm_zero] at hπ1; exact hz1 hπ1.symm

    let sst : AutomorphicForm.localCentralizer K v γ :=
      ⟨diagUnits2 (Units.mk0 π0 hπ0ne) (Units.mk0 π1 hπ1ne),
        BetaWin.diagUnits2_mem_localCentralizer K v a b γ hγ _ _⟩

    let M0 : AutomorphicForm.localCentralizer K v γ → ℝ := fun s =>
      ‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖
    let M1 : AutomorphicForm.localCentralizer K v γ → ℝ := fun s =>
      ‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖
    have hM0c : Continuous M0 := ((Units.continuous_val.matrix_elem 0 0).comp continuous_subtype_val).norm
    have hM1c : Continuous M1 := ((Units.continuous_val.matrix_elem 1 1).comp continuous_subtype_val).norm
    let S' : Set (AutomorphicForm.localCentralizer K v γ) :=
      {s | M0 s = BetaWin.q K v ^ ((-c0) / (Module.finrank K L : ℤ))} ∩
      {s | M1 s = BetaWin.q K v ^ ((-c1) / (Module.finrank K L : ℤ))}
    have hS'm : MeasurableSet S' :=
      (measurableSet_eq_fun hM0c.measurable measurable_const).inter
        (measurableSet_eq_fun hM1c.measurable measurable_const)

    have hpt : ∀ s : AutomorphicForm.localCentralizer K v γ,
        S.indicator (fun _ => (1 : ℝ)) (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (s : GL (Fin 2) (v.adicCompletion K)) * u) = S'.indicator (fun _ => (1 : ℝ)) s := by
      intro s
      obtain ⟨hs01, hs10⟩ := hCdiag (s : GL (Fin 2) (v.adicCompletion K)) s.2
      have hsdet : IsUnit (((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) :=
        Matrix.isUnits_det_units _
      rw [Matrix.det_fin_two, hs10, mul_zero, sub_zero] at hsdet
      obtain ⟨f0, hf0⟩ := BetaWin.exists_norm_eq_zpow K v _ (isUnit_of_mul_isUnit_left hsdet).ne_zero
      obtain ⟨f1, hf1⟩ := BetaWin.exists_norm_eq_zpow K v _ (isUnit_of_mul_isUnit_right hsdet).ne_zero
      have hN0 : N0 (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K)) * u) =
          (BetaWin.q K v ^ f0) ^ Module.finrank K L * BetaWin.q K v ^ c0 := by
        show ‖Algebra.norm (v.adicCompletion K) ((_ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖ = _
        rw [BetaWin.toTensorGL_mul_apply_00 K L v _ u hu10, BetaWin.norm_algebraMap_mul, norm_mul, norm_pow,
          hf0, hc0]
      have hN1 : N1 (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K)) * u) =
          (BetaWin.q K v ^ f1) ^ Module.finrank K L * BetaWin.q K v ^ c1 := by
        show ‖Algebra.norm (v.adicCompletion K) ((_ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ = _
        rw [BetaWin.toTensorGL_mul_apply_11 K L v _ u hu01, BetaWin.norm_algebraMap_mul, norm_mul, norm_pow,
          hf1, hc1]
      have hw0 := BetaWin.window_iff (BetaWin.q K v) hq1 (Module.finrank K L) hn c0 f0
      have hw1 := BetaWin.window_iff (BetaWin.q K v) hq1 (Module.finrank K L) hn c1 f1
      have hmemS : (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K)) * u ∈ S) ↔
          s ∈ S' := by
        show ((cst < N0 _ ∧ N0 _ ≤ 1) ∧ (cst < N1 _ ∧ N1 _ ≤ 1)) ↔
          (M0 s = BetaWin.q K v ^ ((-c0) / (Module.finrank K L : ℤ)) ∧
            M1 s = BetaWin.q K v ^ ((-c1) / (Module.finrank K L : ℤ)))
        rw [hN0, hN1]
        show (((BetaWin.q K v)⁻¹ ^ Module.finrank K L < _ ∧ _) ∧ ((BetaWin.q K v)⁻¹ ^ Module.finrank K L < _ ∧ _)) ↔
          (‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ = _ ∧
            ‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖ = _)
        rw [hw0, hw1, hf0, hf1]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1], by rw [h2]⟩
        · rintro ⟨h1, h2⟩
          exact ⟨BetaWin.zpow_q_injective K v h1, BetaWin.zpow_q_injective K v h2⟩
      by_cases hmem : s ∈ S'
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hmemS.2 hmem)]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem (hmemS.1 h))]

    have hS'eq : S' = (fun h : AutomorphicForm.localCentralizer K v γ => sst⁻¹ * h) ⁻¹'
        {s : AutomorphicForm.localCentralizer K v γ |
          (s : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} := by
      ext s
      obtain ⟨hs01, hs10⟩ := hCdiag (s : GL (Fin 2) (v.adicCompletion K)) s.2
      have hd := hCdiag ((sst⁻¹ * s : AutomorphicForm.localCentralizer K v γ) : GL (Fin 2) (v.adicCompletion K))
        (sst⁻¹ * s).2
      rw [Set.mem_preimage, Set.mem_setOf_eq,
        BetaWin.mem_localIntegralSet_iff_of_diagonal K v _ hd.1 hd.2]
      have hm0 : (((sst⁻¹ * s : AutomorphicForm.localCentralizer K v γ) : GL (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
          π0⁻¹ * ((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hs10,
          mul_zero, add_zero]
        rfl
      have hm1 : (((sst⁻¹ * s : AutomorphicForm.localCentralizer K v γ) : GL (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
          π1⁻¹ * ((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hs01,
          mul_zero, zero_add]
        rfl
      rw [hm0, hm1, norm_mul, norm_mul, norm_inv, norm_inv, hπ0, hπ1]
      show (‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ = _ ∧
          ‖((s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖ = _) ↔ _
      constructor
      · rintro ⟨h1, h2⟩; rw [h1, h2]; exact ⟨inv_mul_cancel₀ hz0, inv_mul_cancel₀ hz1⟩
      · rintro ⟨h1, h2⟩
        rw [inv_mul_eq_one₀ hz0] at h1
        rw [inv_mul_eq_one₀ hz1] at h2
        exact ⟨h1.symm, h2.symm⟩
    have hτS' : τ S' = 1 := by rw [hS'eq, MeasureTheory.measure_preimage_mul]; exact hτ1
    show ∫ s : AutomorphicForm.localCentralizer K v γ,
        S.indicator (fun _ => (1 : ℝ)) (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (s : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ = 1
    simp_rw [hpt]
    rw [integral_indicator_const _ hS'm, Measure.real, hτS']
    simp

#print axioms solution

end S_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal (solution)
