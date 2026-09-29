-- Prove2me | solution 1 for AutomorphicForm.mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/526e46de-265e-554d-9560-ff20afe52fd4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
import Theorems.Thm_AutomorphicForm_measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal
import Theorems.Thm_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
import Theorems.Thm_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsLocalTestFn localIntegralSet one_mem_localIntegralSet localGLBorel borelSpace_localGLBorel localCentralizer localCentralizerBorel IsOrbitalIntegral IsRegularSemisimple isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal"
namespace EllGermValue
p2m_open "AutomorphicForm"

theorem elim (A b b' ν₀ ν₁ J₀ J₁ J₀' J₁' : ℂ)
    (e1 : J₀ = A * 1 + b * ν₀) (e2 : J₁ = A * 1 + b * ν₁) (e3 : J₀' = A * 1 + b' * ν₀) (e4 : J₁' = A * 1 + b' * ν₁) :
    A * (J₀ - J₁ - J₀' + J₁') = J₀ * J₁' - J₀' * J₁ := by
  linear_combination (A - J₁') * e1 + (J₀' - A) * e2 + (b * ν₁) * e3 + (-(b * ν₀)) * e4

theorem solve_core (A X u k : ℂ) (hX : X ≠ 0) (hu : u ≠ 0) (h : A * (-(X * u)) = k * X * u ^ 2) :
    A = -(k * u) := by
  have h2 : (A + k * u) * (X * u) = 0 := by linear_combination (-1 : ℂ) * h
  rcases mul_eq_zero.mp h2 with h1 | h1
  · linear_combination h1
  · exact absurd h1 (mul_ne_zero hX hu)

theorem solve_ram (A q θ : ℂ) (m : ℕ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hθ : θ ≠ 0)
    (h : A * ((q ^ (m + 1) - 1) / ((q - 1) * θ) - (q ^ m - 1) / ((q - 1) * θ)
        - (q ^ (m + 1 + 1) - 1) / ((q - 1) * θ) + (q ^ (m + 1) - 1) / ((q - 1) * θ))
      = (q ^ (m + 1) - 1) / ((q - 1) * θ) * ((q ^ (m + 1) - 1) / ((q - 1) * θ))
        - (q ^ (m + 1 + 1) - 1) / ((q - 1) * θ) * ((q ^ m - 1) / ((q - 1) * θ))) :
    A * θ = -(1 : ℂ) / (q - 1) := by
  set u : ℂ := ((q - 1) * θ)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero (mul_ne_zero hq1 hθ)
  have hL : (q ^ (m + 1) - 1) / ((q - 1) * θ) - (q ^ m - 1) / ((q - 1) * θ)
        - (q ^ (m + 1 + 1) - 1) / ((q - 1) * θ) + (q ^ (m + 1) - 1) / ((q - 1) * θ)
      = -((q ^ m * (q - 1) ^ 2) * u) := by
    simp only [div_eq_mul_inv, hu]; ring
  have hR : (q ^ (m + 1) - 1) / ((q - 1) * θ) * ((q ^ (m + 1) - 1) / ((q - 1) * θ))
        - (q ^ (m + 1 + 1) - 1) / ((q - 1) * θ) * ((q ^ m - 1) / ((q - 1) * θ))
      = 1 * (q ^ m * (q - 1) ^ 2) * u ^ 2 := by
    simp only [div_eq_mul_inv, hu]; ring
  rw [hL, hR] at h
  have hA := solve_core A _ u 1 (mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hq1)) hu0 h
  rw [hA, hu, one_mul]
  field_simp

theorem solve_unr (A q θ : ℂ) (m : ℕ) (hm : 1 ≤ m) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hq2 : q + 1 ≠ 0) (hθ : θ ≠ 0)
    (h : A * (((q + 1) * q ^ m - 2) / ((q - 1) * θ) - ((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * θ)
        - ((q + 1) * q ^ (m + 1) - 2) / ((q - 1) * θ) + ((q + 1) * q ^ (m + 1 - 1) - 2) / ((q - 1) * θ))
      = ((q + 1) * q ^ m - 2) / ((q - 1) * θ) * (((q + 1) * q ^ (m + 1 - 1) - 2) / ((q - 1) * θ))
        - ((q + 1) * q ^ (m + 1) - 2) / ((q - 1) * θ) * (((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * θ))) :
    A * θ = -(2 : ℂ) / (q - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  set u : ℂ := ((q - 1) * θ)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero (mul_ne_zero hq1 hθ)
  have hL : ((q + 1) * q ^ (n + 1) - 2) / ((q - 1) * θ) - ((q + 1) * q ^ n - 2) / ((q - 1) * θ)
        - ((q + 1) * q ^ (n + 1 + 1) - 2) / ((q - 1) * θ) + ((q + 1) * q ^ (n + 1) - 2) / ((q - 1) * θ)
      = -(((q + 1) * q ^ n * (q - 1) ^ 2) * u) := by
    simp only [div_eq_mul_inv, hu]; ring
  have hR : ((q + 1) * q ^ (n + 1) - 2) / ((q - 1) * θ) * (((q + 1) * q ^ (n + 1) - 2) / ((q - 1) * θ))
        - ((q + 1) * q ^ (n + 1 + 1) - 2) / ((q - 1) * θ) * (((q + 1) * q ^ n - 2) / ((q - 1) * θ))
      = 2 * ((q + 1) * q ^ n * (q - 1) ^ 2) * u ^ 2 := by
    simp only [div_eq_mul_inv, hu]; ring
  rw [hL, hR] at h
  have hA := solve_core A _ u 2
    (mul_ne_zero (mul_ne_zero hq2 (pow_ne_zero _ hq)) (pow_ne_zero _ hq1)) hu0 h
  rw [hA, hu]
  field_simp

section Transport

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem transport (γ₀ γ' : GL (Fin 2) (v.adicCompletion K))
    (heq : AutomorphicForm.localCentralizer K v γ' = AutomorphicForm.localCentralizer K v γ₀)
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτ₀ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀)
    (hν : @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ₀ = νT) :
    ∃ τ : @Measure (AutomorphicForm.localCentralizer K v γ') (AutomorphicForm.localCentralizerBorel K v γ'),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ') τ ∧
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ') (AutomorphicForm.localGLBorel K v)
        Subtype.val τ = νT := by
  letI := AutomorphicForm.localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
  letI : MeasurableSpace (AutomorphicForm.localCentralizer K v γ₀) := AutomorphicForm.localCentralizerBorel K v γ₀
  letI : MeasurableSpace (AutomorphicForm.localCentralizer K v γ') := AutomorphicForm.localCentralizerBorel K v γ'
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v γ₀) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v γ') := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ₀ := hτ₀
  let e : ↥(AutomorphicForm.localCentralizer K v γ₀) ≃* ↥(AutomorphicForm.localCentralizer K v γ') :=
    (MulEquiv.subgroupCongr heq).symm
  have hec : Continuous e := continuous_induced_rng.2 (continuous_subtype_val.congr fun x => rfl)
  have hec' : Continuous e.symm := continuous_induced_rng.2 (continuous_subtype_val.congr fun x => rfl)
  refine ⟨Measure.map e τ₀, e.isHaarMeasure_map τ₀ hec hec', ?_⟩
  rw [Measure.map_map continuous_subtype_val.measurable hec.measurable]
  exact hν

end Transport

theorem absNorm_two_le {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

set_option maxHeartbeats 3200000 in
theorem main
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (_hνT : ∃ τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀ ∧
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ₀ = νT)
    (ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ) (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (_hgerm : ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                  Subtype.val τ = νT →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) :
    letI := AutomorphicForm.localGLBorel K v
    ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
        = -(1 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) ∧
    ((¬ ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
        = -(2 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) := by
  letI := AutomorphicForm.localGLBorel K v

  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hϖ : Valued.v ((π : v.adicCompletion K)) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ

  obtain ⟨hθpos, hθtop⟩ :=
    AutomorphicForm.measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal K v γ₀ _hreg _hns νT _hνT
  have hθ : ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hθpos.ne' hθtop.ne).ne'

  have hq2 := absNorm_two_le v
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hq1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1 ≠ 0 := by
    have : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 1 := by exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 1 by omega)
    exact sub_ne_zero.mpr this
  have hq3 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (Ideal.absNorm v.asIdeal))

  set f₀ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) with hf₀
  set f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) with hf₁
  obtain ⟨hf₀t, hf₁t⟩ :=
    AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence K v c
  have hf₀z : f₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
    simp only [hf₀, inv_mul_cancel]
    exact Set.indicator_of_mem (AutomorphicForm.one_mem_localIntegralSet K v) _
  have hf₁z : f₁ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
    simp only [hf₁, inv_mul_cancel]
    refine Set.indicator_of_mem ?_ _
    refine ⟨AutomorphicForm.one_mem_localIntegralSet K v, fun i j => ?_⟩
    simp
  obtain ⟨W₀, hW₀, hG₀⟩ := _hgerm f₀ hf₀t
  obtain ⟨W₁, hW₁, hG₁⟩ := _hgerm f₁ hf₁t

  obtain ⟨Y, γ, hYint, hYgen, hγ, hlim⟩ :=
    AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal K v c _ hϖ γ₀ _hreg _hns
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp (hlim.eventually_mem (Filter.inter_mem hW₀ hW₁))
  obtain ⟨hγT, hγreg, hγdet, hγY, hγZ⟩ := hγ (max m₀ 1) (le_max_right _ _)
  obtain ⟨hγT', hγreg', hγdet', hγY', hγZ'⟩ := hγ (max m₀ 1 + 1) (by omega)
  have hmW := hm₀ (max m₀ 1) (le_max_left _ _)
  have hmW' := hm₀ (max m₀ 1 + 1) (by omega)

  obtain ⟨τ₀, hτ₀, hτ₀ν⟩ := _hνT
  obtain ⟨τ, hτ, hτν⟩ := transport K v γ₀ _ hγZ νT τ₀ hτ₀ hτ₀ν
  obtain ⟨τ', hτ', hτ'ν⟩ := transport K v γ₀ _ hγZ' νT τ₀ hτ₀ hτ₀ν

  have hnear : ∀ n : ℕ, 1 ≤ n → 1 ≤ n ∧ Valued.v ((1 : v.adicCompletion K) - 1) < 1 := fun n hn =>
    ⟨hn, by rw [sub_self, Valuation.map_zero]; exact zero_lt_one⟩
  have hB := AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
    K v c _ hϖ γ₀ _hreg _hns νT (γ (max m₀ 1)) hγT hγreg hγdet (max m₀ 1) 1 (by simp) Y hγY hYint hYgen τ hτ hτν
  have hB' := AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
    K v c _ hϖ γ₀ _hreg _hns νT (γ (max m₀ 1 + 1)) hγT' hγreg' hγdet' (max m₀ 1 + 1) 1 (by simp) Y hγY' hYint hYgen τ' hτ' hτ'ν
  refine ⟨fun hram => ?_, fun hunr => ?_⟩
  · obtain ⟨h0, h1⟩ := hB.1 hram
    obtain ⟨h0', h1'⟩ := hB'.1 hram
    have e1 := hG₀ _ hmW.1 hγT hγreg τ hτ hτν _ h0
    have e2 := hG₁ _ hmW.2 hγT hγreg τ hτ hτν _ (h1 (hnear _ (le_max_right _ _)))
    have e3 := hG₀ _ hmW'.1 hγT' hγreg' τ' hτ' hτ'ν _ h0'
    have e4 := hG₁ _ hmW'.2 hγT' hγreg' τ' hτ' hτ'ν _ (h1' (hnear _ (by omega)))
    rw [hf₀z] at e1 e3
    rw [hf₁z] at e2 e4
    exact solve_ram A _ _ (max m₀ 1) hq hq1 hθ (elim A _ _ _ _ _ _ _ _ e1 e2 e3 e4)
  · obtain ⟨h0, h1⟩ := hB.2 hunr
    obtain ⟨h0', h1'⟩ := hB'.2 hunr
    have e1 := hG₀ _ hmW.1 hγT hγreg τ hτ hτν _ h0
    have e2 := hG₁ _ hmW.2 hγT hγreg τ hτ hτν _ (h1 (hnear _ (le_max_right _ _)))
    have e3 := hG₀ _ hmW'.1 hγT' hγreg' τ' hτ' hτ'ν _ h0'
    have e4 := hG₁ _ hmW'.2 hγT' hγreg' τ' hτ' hτ'ν _ (h1' (hnear _ (by omega)))
    rw [hf₀z] at e1 e3
    rw [hf₁z] at e2 e4
    exact solve_unr A _ _ (max m₀ 1) (le_max_right _ _) hq hq1 hq3 hθ (elim A _ _ _ _ _ _ _ _ e1 e2 e3 e4)

end AutomorphicForm.EllGermValue

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (_hνT : ∃ τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀ ∧
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ₀ = νT)
    (ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ) (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (_hgerm : ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                  Subtype.val τ = νT →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) :
    letI := AutomorphicForm.localGLBorel K v
    ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
        = -(1 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) ∧
    ((¬ ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
        = -(2 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) :=
  AutomorphicForm.EllGermValue.main K v c γ₀ _hreg _hns νT _hνT ν A B _hgerm

end S_AutomorphicForm_mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal
end P2MW
export P2MW.S_AutomorphicForm_mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal (solution)
