-- Prove2me | solution 1 for AutomorphicForm.setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e20520ad-a326-5ac0-956b-81d1a896f80d

import Mathlib
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
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open MeasureTheory NumberField
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace R1UniVanish

section NormInvariance

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L where
  toAddEquiv := (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toAddEquiv
  continuous_toFun := D.continuous_act σ
  continuous_invFun := by
    have h : ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toAddEquiv.symm : AdeleRing (𝓞 L) L → _) =
        (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
      rw [map_inv]; rfl
    show Continuous ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toAddEquiv.symm)
    rw [h]
    exact D.continuous_act σ⁻¹

@[scoped simp] theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (x : AdeleRing (𝓞 L) L) : actEquiv D σ x = D.act σ x := rfl

theorem coe_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ((D.unitsAct σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = D.act σ z :=
  rfl

theorem ideleNorm_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    TateGlobal.ideleNorm L (D.unitsAct σ z) = TateGlobal.ideleNorm L z := by
  unfold TateGlobal.ideleNorm
  congr 1
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  let θ := actEquiv D σ
  let μ' : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ
  haveI : μ'.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ'.Regular := Measure.Regular.map θ.symm.toHomeomorph

  obtain ⟨s, hs, hs0⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs_ne : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs0).ne'
  have hs_top : μ s ≠ ∞ := hs.measure_lt_top.ne

  have hμ' : ∀ E : Set (AdeleRing (𝓞 L) L), μ (θ '' E) = μ' E := by
    intro E
    show μ (θ '' E) = Measure.map θ.symm.toHomeomorph.toMeasurableEquiv μ E
    rw [MeasurableEquiv.map_apply]
    congr 1
    exact θ.toEquiv.image_eq_preimage_symm E

  have hset : (D.unitsAct σ z) • s = θ '' (z • (θ.symm '' s)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm y, ⟨θ.symm y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
      show D.act σ ((z : AdeleRing (𝓞 L) L) * θ.symm y) = (D.unitsAct σ z : AdeleRing (𝓞 L) L) * y
      rw [map_mul, coe_unitsAct]
      congr 1
      exact θ.apply_symm_apply y
    · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      show (D.unitsAct σ z : AdeleRing (𝓞 L) L) * y = D.act σ ((z : AdeleRing (𝓞 L) L) * θ.symm y)
      rw [map_mul, coe_unitsAct]
      congr 1
      exact (θ.apply_symm_apply y).symm
  have key : μ ((D.unitsAct σ z) • s) = (distribHaarChar (AdeleRing (𝓞 L) L) z : ℝ≥0∞) * μ s := by
    rw [hset, hμ', ← distribHaarChar_mul μ' z (θ.symm '' s), ← hμ', Set.image_image]
    congr 2
    refine Set.ext fun x => ⟨?_, fun hx => ⟨x, hx, θ.apply_symm_apply x⟩⟩
    rintro ⟨y, hy, rfl⟩
    show θ (θ.symm y) ∈ s
    rwa [θ.apply_symm_apply]
  exact distribHaarChar_eq_of_measure_smul_eq_mul hs_ne hs_top key

end NormInvariance

section Witness

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

theorem ideleNorm_inv (z : (AdeleRing (𝓞 L) L)ˣ) :
    TateGlobal.ideleNorm L z⁻¹ = (TateGlobal.ideleNorm L z)⁻¹ := by
  unfold TateGlobal.ideleNorm; rw [map_inv, NNReal.coe_inv]

theorem ideleNorm_pow (z : (AdeleRing (𝓞 L) L)ˣ) (n : ℕ) :
    TateGlobal.ideleNorm L (z ^ n) = (TateGlobal.ideleNorm L z) ^ n := by
  unfold TateGlobal.ideleNorm; rw [map_pow, NNReal.coe_pow]

theorem exists_ideleNorm_eq_one_and_ne [FiniteDimensional K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (h : ∃ z₀ : (AdeleRing (𝓞 L) L)ˣ, ξ (D.unitsAct σ z₀) ≠ ξ z₀) :
    ∃ b : (AdeleRing (𝓞 L) L)ˣ, TateGlobal.ideleNorm L b = 1 ∧ ξ (D.unitsAct σ b) ≠ ξ b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀⟩ := h

  set ψ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := (ξ.comp (D.unitsAct σ).toMonoidHom) / ξ with hψ
  have hψ_apply : ∀ z, ψ z = ξ (D.unitsAct σ z) / ξ z := fun z => rfl
  have hψ1 : ∀ b, TateGlobal.ideleNorm L b = 1 → ψ b = 1 := fun b hb => by
    rw [hψ_apply, div_eq_one]; exact hcon b hb

  have hA : ∀ z w, TateGlobal.ideleNorm L z = TateGlobal.ideleNorm L w → ψ z = ψ w := by
    intro z w hzw
    have hb : TateGlobal.ideleNorm L (z * w⁻¹) = 1 := by
      rw [TateGlobal.ideleNorm_mul, ideleNorm_inv, hzw,
        mul_inv_cancel₀ (TateGlobal.ideleNorm_pos w).ne']
    have := hψ1 _ hb
    rwa [map_mul, map_inv, mul_inv_eq_one] at this

  set n := orderOf σ with hn
  have hn0 : n ≠ 0 := (orderOf_pos σ).ne'
  have hB : ∀ z, ψ z ^ n = 1 := by
    intro z
    let a : ℕ → ℂˣ := fun i => ξ (D.unitsAct (σ ^ i) z)
    have htel : ∏ i ∈ Finset.range n, a (i + 1) / a i = a n / a 0 := Finset.prod_range_div a n
    have han : a n = a 0 := by
      show ξ (D.unitsAct (σ ^ n) z) = ξ (D.unitsAct (σ ^ 0) z)
      rw [hn, pow_orderOf_eq_one, pow_zero]
    rw [han, div_self'] at htel
    have hterm : ∀ i ∈ Finset.range n, a (i + 1) / a i = ψ z := by
      intro i _
      have h1 : a (i + 1) = ξ (D.unitsAct σ (D.unitsAct (σ ^ i) z)) := by
        show ξ (D.unitsAct (σ ^ (i + 1)) z) = _
        rw [pow_succ', map_mul]; rfl
      rw [h1, ← hψ_apply]
      exact hA _ _ (ideleNorm_unitsAct D (σ ^ i) z)
    rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range] at htel
    exact htel

  obtain ⟨w, -, hw⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one L
    ((TateGlobal.ideleNorm L z₀) ^ ((n : ℝ)⁻¹)) (Real.rpow_pos_of_pos (TateGlobal.ideleNorm_pos z₀) _)
  have hwn : TateGlobal.ideleNorm L (w ^ n) = TateGlobal.ideleNorm L z₀ := by
    rw [ideleNorm_pow, hw, Real.rpow_inv_natCast_pow (TateGlobal.ideleNorm_pos z₀).le hn0]
  have : ψ z₀ = 1 := by
    rw [hA z₀ (w ^ n) hwn.symm, map_pow, hB]
  rw [hψ_apply, div_eq_one] at this
  exact hz₀ this

end Witness

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

namespace R1UniVanish

section Height

variable {K : Type*} [NormedField K]

theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, hbot 0, hbot 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  unfold finLocalHeight
  rw [hdet, rowMaxNorm_scalar_entries_mul h10 h11 g, mul_pow,
    mul_div_mul_left _ _ hz2.ne']

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hcoe : ∀ i j : Fin 2, ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
    intro i j
    show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v => ?_) ?_ ?_ ?_ ?_ _
    · exact (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [glArch_apply, hcoe]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_entries_mul (z := ((z : AdeleRing (𝓞 F) F).2) v) ?_ ?_ ?_ ?_ ?_ _
    · exact (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [finComponent_apply, glFin_apply, hcoe]; rfl

omit [NumberField F] in

theorem apply_one_zero_ne_zero_of_not_mem_borelSubgroup {γ : GL (Fin 2) F}
    (hγ : γ ∉ borelSubgroup F) : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := hγ

theorem adelicHeight_le_inv_of_not_mem_borelSubgroup {h₀ : ℝ} (hh₀ : 0 < h₀) {γ : GL (Fin 2) F}
    (hγ : γ ∉ borelSubgroup F) {x : AdelicGL2 (𝓞 F) F} (hx : h₀ ≤ adelicHeight F x)
    (hγx : h₀ ≤ adelicHeight F (globalPoints (𝓞 F) F γ * x)) :
    adelicHeight F x ≤ h₀⁻¹ ∧ adelicHeight F (globalPoints (𝓞 F) F γ * x) ≤ h₀⁻¹ := by
  have h1 := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one (F := F) γ hγ x
  have hpos := adelicHeight_pos (F := F) x
  have hpos' := adelicHeight_pos (F := F) (globalPoints (𝓞 F) F γ * x)
  constructor
  · rw [← one_div, le_div_iff₀ hh₀]
    calc adelicHeight F x * h₀ ≤ adelicHeight F x * adelicHeight F (globalPoints (𝓞 F) F γ * x) :=
          mul_le_mul_of_nonneg_left hγx hpos.le
      _ = adelicHeight F (globalPoints (𝓞 F) F γ * x) * adelicHeight F x := mul_comm _ _
      _ ≤ 1 := h1
  · rw [← one_div, le_div_iff₀ hh₀]
    calc adelicHeight F (globalPoints (𝓞 F) F γ * x) * h₀
        ≤ adelicHeight F (globalPoints (𝓞 F) F γ * x) * adelicHeight F x :=
          mul_le_mul_of_nonneg_left hx hpos'.le
      _ ≤ 1 := h1

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open Polynomial

namespace R1UniVanish

section Cells

open AutomorphicForm

variable {K : Type*} [Field K]

theorem X_sub_C_sq (a : K) : ((X - C a) ^ 2 : K[X]) = X ^ 2 - C (2 * a) * X + C (a ^ 2) := by
  rw [map_mul, map_pow, show (C (2 : K)) = 2 from map_ofNat C 2]; ring

theorem trace_det_of_charpoly_eq {M : Matrix (Fin 2) (Fin 2) K} {a : K} (h : M.charpoly = (X - C a) ^ 2) :
    M.trace = 2 * a ∧ M.det = a ^ 2 := by
  rw [Matrix.charpoly_fin_two, X_sub_C_sq] at h
  have h1 := congrArg (fun p : K[X] => p.coeff 1) h
  have h0 := congrArg (fun p : K[X] => p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, if_true,
    mul_one] at h1 h0
  norm_num at h1 h0
  exact ⟨h1, h0⟩

theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsCentralType (t • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨t⁻¹ * c, ?_⟩
    have := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => t⁻¹ • N) hc
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using this
  · rintro ⟨c, rfl⟩
    exact ⟨t * c, by rw [smul_smul]⟩

theorem isUnipotentType_smul {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) (h : IsUnipotentType M) :
    IsUnipotentType (t • M) := by
  obtain ⟨hnc, a, ha⟩ := h
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq ha
  refine ⟨(isCentralType_smul_iff ht).not.mpr hnc, t * a, ?_⟩
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, htr, hdet, X_sub_C_sq,
    smul_eq_mul]
  congr 2 <;> [(congr 2; ring); (congr 1; ring)]

theorem isUnipotentType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsUnipotentType (t • M) ↔ IsUnipotentType M := by
  refine ⟨fun h => ?_, isUnipotentType_smul ht⟩
  have := isUnipotentType_smul (inv_ne_zero ht) h
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

theorem coe_mul_scalar (γ : GL (Fin 2) K) (t : Kˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  show (γ : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (t : K) = _
  rw [← (Matrix.scalar_commute (t : K) (fun r' => mul_comm _ r') _).eq, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem mul_scalar_mem_unipotentCell_iff (γ : GL (Fin 2) K) (t : Kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t ∈ unipotentCell K ↔ γ ∈ unipotentCell K := by
  rw [mem_unipotentCell_iff, mem_unipotentCell_iff, coe_mul_scalar]
  exact isUnipotentType_smul_iff t.ne_zero

end Cells
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

section NormClasses

open LT.TwistedNorm AutomorphicForm

theorem sigmaPartialNorm_mul_of_mem_center {G : Type*} [Group G] (σ : G →* G) (x : G) {y : G}
    (hy : y ∈ Subgroup.center G) (r : ℕ) :
    sigmaPartialNorm σ (x * y) r = sigmaPartialNorm σ x r * sigmaPartialNorm σ y r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul]
      have hc := Subgroup.mem_center_iff.mp hy (σ (sigmaPartialNorm σ x r))
      calc x * y * (σ (sigmaPartialNorm σ x r) * σ (sigmaPartialNorm σ y r))
          = x * (y * σ (sigmaPartialNorm σ x r)) * σ (sigmaPartialNorm σ y r) := by group
        _ = x * (σ (sigmaPartialNorm σ x r) * y) * σ (sigmaPartialNorm σ y r) := by rw [hc]
        _ = x * σ (sigmaPartialNorm σ x r) * (y * σ (sigmaPartialNorm σ y r)) := by group

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem scalar_mem_center (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (n := Fin 2) (s : L) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) L)).eq i) j |>.symm

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : R →* S) s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show σ (Matrix.scalar (Fin 2) (s : R) i j) = Matrix.scalar (Fin 2) (σ (s : R)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_algebraMap_scalar (t : Kˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) t) :=
  map_scalar (algebraMap K L) t

variable [FiniteDimensional K L] [IsGalois K L]

theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (s : Lˣ) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap K L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s)) := by
  rw [sigmaNormPow_def, sigmaPartialNorm_mul_of_mem_center _ _ (scalar_mem_center s), ← sigmaNormPow_def,
    ← sigmaNormPow_def]
  congr 1
  have h := hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Matrix.GeneralLinearGroup.map (σ : L →+* L))
    (Matrix.GeneralLinearGroup.scalar (Fin 2)) (fun x => (map_scalar (σ : L →+* L) x).symm) (Module.finrank K L) s
  rw [← h, map_algebraMap_scalar]
  congr 1
  ext
  rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_of_isConj {σ : L ≃ₐ[K] L} {γ γ' : GL (Fin 2) K} {δ : GL (Fin 2) L}
    (h : IsNormRep σ γ δ) (hc : IsConj γ γ') : IsNormRep σ γ' δ := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap K L) c⁻¹, ?_⟩
  rw [map_mul, map_mul, ← hP, map_inv]
  group

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [FiniteDimensional K L] [IsGalois K L]
    {γ : GL (Fin 2) K} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (s : Lˣ) :
    IsNormRep σ (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP]
  have hc := Subgroup.mem_center_iff.mp
    (scalar_mem_center (Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) s))) P
  rw [← map_algebraMap_scalar] at hc
  simp only [mul_assoc, hc]

def SU (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : Set (GL (Fin 2) L) :=
  {δ | ∃ γ : GL (Fin 2) K, γ ∈ unipotentCell K ∧ normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}

theorem mul_scalar_mem_SU {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} (hδ : δ ∈ SU K hgen) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ SU K hgen := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hcls
  have hrep : IsNormRep σ γ δ := isNormRep_of_isConj (isNormRep_normRep hgen δ) hcls
  refine ⟨_, ?_, normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hrep s)⟩
  exact (mul_scalar_mem_unipotentCell_iff γ _).mpr hγ

theorem bijOn_mul_scalar_SU {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (s : Lˣ) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) (SU K hgen) (SU K hgen) := by
  refine ⟨fun δ hδ => mul_scalar_mem_SU hgen hδ s, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹, mul_scalar_mem_SU hgen hδ s⁻¹, ?_⟩
  simp only [map_inv, inv_mul_cancel_right]

omit [FiniteDimensional K L] [IsGalois K L] in

theorem mk_sigmaConj (σ : L ≃ₐ[K] L) (h δ : GL (Fin 2) L) :
    SigmaConjClasses.mk σ (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) = SigmaConjClasses.mk σ δ :=
  (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm

theorem bijOn_sigmaConj_SU {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (h : GL (Fin 2) L) :
    Set.BijOn (fun δ : GL (Fin 2) L => h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)
      (SU K hgen) (SU K hgen) := by
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ hh => ?_, fun δ hδ => ?_⟩
  · show ∃ γ, _ ∧ _
    rw [mk_sigmaConj]; exact hδ
  · have := congrArg (fun y => h * y * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹) hh
    simpa [mul_assoc] using this
  · refine ⟨h * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹, ?_, by group⟩
    show ∃ γ, _ ∧ _
    have e : SigmaConjClasses.mk σ (h * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹) =
        SigmaConjClasses.mk σ δ := by
      have := mk_sigmaConj σ h⁻¹ δ
      rwa [inv_inv, map_inv] at this
    rw [e]; exact hδ

end NormClasses
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

section BorelOne

open AutomorphicForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def dr (g : GL (Fin 2) L) : L := (g : Matrix (Fin 2) (Fin 2) L) 0 0 / (g : Matrix (Fin 2) (Fin 2) L) 1 1

theorem mul_apply_one_zero_of_upper {g h : GL (Fin 2) L}
    (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]; ring

theorem mul_apply_zero_zero_of_upper (g : GL (Fin 2) L) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]; ring

theorem mul_apply_one_one_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg]; ring

theorem dr_mul {g h : GL (Fin 2) L}
    (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    dr (g * h) = dr g * dr h := by
  unfold dr
  rw [mul_apply_zero_zero_of_upper g hh, mul_apply_one_one_of_upper hg h, mul_div_mul_comm]

theorem apply_one_one_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem apply_zero_zero_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem dr_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : dr g ≠ 0 :=
  div_ne_zero (apply_zero_zero_ne_zero_of_upper hg) (apply_one_one_ne_zero_of_upper hg)

theorem dr_one : dr (1 : GL (Fin 2) L) = 1 := by
  unfold dr; simp

theorem inv_apply_one_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
  (borelSubgroup L).inv_mem hg

theorem dr_inv {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : dr g⁻¹ = (dr g)⁻¹ := by
  have h := dr_mul (inv_apply_one_zero_of_upper hg) hg
  rw [inv_mul_cancel, dr_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem map_apply_one_zero (σ : L →+* L) (g : GL (Fin 2) L) :
    ((Matrix.GeneralLinearGroup.map σ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 =
      σ ((g : Matrix (Fin 2) (Fin 2) L) 1 0) := rfl

theorem dr_map (σ : L →+* L) (g : GL (Fin 2) L) : dr (Matrix.GeneralLinearGroup.map σ g) = σ (dr g) := by
  unfold dr; rw [map_div₀]; rfl

variable (K) in

def B1 : Set (GL (Fin 2) L) :=
  {γ | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}

theorem norm_inv' {x : L} (hx : x ≠ 0) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])

theorem mem_B1_iff {γ : GL (Fin 2) L} : γ ∈ B1 K ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Algebra.norm K (dr γ) = 1 :=
  Iff.rfl

theorem mul_mem_B1 {g h : GL (Fin 2) L} (hg : g ∈ B1 K) (hh : h ∈ B1 K) : g * h ∈ B1 K := by
  rw [mem_B1_iff] at hg hh ⊢
  refine ⟨mul_apply_one_zero_of_upper hg.1 hh.1, ?_⟩
  rw [dr_mul hg.1 hh.1, map_mul, hg.2, hh.2, mul_one]

theorem inv_mem_B1 {g : GL (Fin 2) L} (hg : g ∈ B1 K) : g⁻¹ ∈ B1 K := by
  rw [mem_B1_iff] at hg ⊢
  refine ⟨inv_apply_one_zero_of_upper hg.1, ?_⟩
  rw [dr_inv hg.1, norm_inv' (dr_ne_zero_of_upper hg.1), hg.2, inv_one]

theorem scalar_mem_B1 (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ B1 K := by
  refine ⟨?_, ?_⟩
  · show Matrix.scalar (Fin 2) (s : L) 1 0 = 0
    simp [Matrix.scalar_apply]
  · show Algebra.norm K (Matrix.scalar (Fin 2) (s : L) 0 0 / Matrix.scalar (Fin 2) (s : L) 1 1) = 1
    simp [Matrix.scalar_apply]

theorem unipotentGL2_mem_B1 (l : L) : unipotentGL2 l ∈ B1 K := by
  refine ⟨by simp, ?_⟩
  simp

theorem sigmaConj_mem_B1 [FiniteDimensional K L] (σ : L ≃ₐ[K] L) {h : GL (Fin 2) L} (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    {δ : GL (Fin 2) L} (hδ : δ ∈ B1 K) :
    h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h ∈ B1 K := by
  rw [mem_B1_iff] at hδ ⊢
  have hσh : ((Matrix.GeneralLinearGroup.map (σ : L →+* L) h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    rw [map_apply_one_zero, hh, map_zero]
  have hinv := inv_apply_one_zero_of_upper hh
  refine ⟨mul_apply_one_zero_of_upper (mul_apply_one_zero_of_upper hinv hδ.1) hσh, ?_⟩
  rw [dr_mul (mul_apply_one_zero_of_upper hinv hδ.1) hσh, dr_mul hinv hδ.1, dr_inv hh, dr_map, map_mul, map_mul,
    hδ.2, mul_one, norm_inv' (dr_ne_zero_of_upper hh), show ((σ : L →+* L) (dr h)) = σ (dr h) from rfl,
    Algebra.norm_eq_of_algEquiv, inv_mul_cancel₀]
  exact (Algebra.norm_ne_zero_iff.mpr (dr_ne_zero_of_upper hh))

theorem bijOn_sigmaConj_B1 [FiniteDimensional K L] (σ : L ≃ₐ[K] L) {h : GL (Fin 2) L} (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    Set.BijOn (fun δ : GL (Fin 2) L => h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) (B1 K) (B1 K) := by
  refine ⟨fun δ hδ => sigmaConj_mem_B1 σ hh hδ, fun δ _ δ' _ hh' => ?_, fun δ hδ => ?_⟩
  · have := congrArg (fun y => h * y * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹) hh'
    simpa [mul_assoc] using this
  · refine ⟨h * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹, ?_, by group⟩
    have := sigmaConj_mem_B1 (K := K) σ (inv_apply_one_zero_of_upper hh) hδ
    rwa [inv_inv, map_inv] at this

theorem bijOn_mul_B1 {b : GL (Fin 2) L} (hb : b ∈ B1 K) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * b) (B1 K) (B1 K) := by
  refine ⟨fun δ hδ => mul_mem_B1 hδ hb, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  exact ⟨δ * b⁻¹, mul_mem_B1 hδ (inv_mem_B1 hb), by simp⟩

theorem map_mem_B1 (σ : L ≃ₐ[K] L) {b : GL (Fin 2) L} (hb : b ∈ B1 K) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ B1 K := by
  rw [mem_B1_iff] at hb ⊢
  refine ⟨by rw [map_apply_one_zero, hb.1, map_zero], ?_⟩
  rw [dr_map, show ((σ : L →+* L) (dr b)) = σ (dr b) from rfl, Algebra.norm_eq_of_algEquiv, hb.2]

end BorelOne
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped NNReal ENNReal Pointwise

namespace R1UniVanish

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem conj_identity (h δ : GL (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L) :
    (globalPoints (𝓞 L) L h * x)⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y =
      x⁻¹ * globalPoints (𝓞 L) L (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) *
        sigmaAdelicAct K L D σ ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  rw [map_mul (sigmaAdelicAct K L D σ), map_inv (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints',
    map_mul (globalPoints (𝓞 L) L), map_mul (globalPoints (𝓞 L) L), map_inv (globalPoints (𝓞 L) L), mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unitsAct_principal (q : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) q) :=
  Units.ext (D.compat σ (q : L))

theorem globalPoints_unipotentGL2 (l : L) :
    globalPoints (𝓞 L) L (unipotentGL2 l) = unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show algebraMap L (AdeleRing (𝓞 L) L) ((unipotentGL2 l : Matrix (Fin 2) (Fin 2) L) i j) =
    (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_mul_globalPoints {h : GL (Fin 2) L} (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (q : AdeleRing (𝓞 L) L) :
    unipotentGL2 q * globalPoints (𝓞 L) L h =
      globalPoints (𝓞 L) L h *
        unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L)
          ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0) * q) := by
  have h00 : (h : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h0
    have hdet := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two, hh, h0] at hdet
    simp at hdet
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hg : ∀ i j, ((globalPoints (𝓞 L) L h : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
  have e : algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 0 0) *
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0) =
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [← map_mul, mul_div_cancel₀ _ h00]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh, unipotentGL2_coe]
  · rw [← mul_assoc, e]
    ring

theorem inv_cs_mul_conj (a : (AdeleRing (𝓞 L) L)ˣ) (x G Y : AdelicGL2 (𝓞 L) L) :
    (centralScalar (𝓞 L) L a * x)⁻¹ * G * sigmaAdelicAct K L D σ (Y * (centralScalar (𝓞 L) L a * x)) =
      x⁻¹ * G * sigmaAdelicAct K L D σ
        (Y * (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹) * x)) := by
  have ht : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹)) =
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L a) * (centralScalar (𝓞 L) L a)⁻¹ := by
    rw [sigmaAdelicAct_centralScalar, sigmaAdelicAct_centralScalar, map_mul, map_inv, map_mul, map_inv, map_inv]
    congr 3
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [map_mul, map_mul, map_mul, map_mul, ht, mul_inv_rev, ← map_inv]
  simp only [mul_assoc, mul_cs_left]

end AdelicAlgebra
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

section KernelSums

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) {σ : L ≃ₐ[K] L}
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Afun (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑ᶠ δ ∈ SU K hgen, φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))

variable (σ) in

def Bfun (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ B1 K, φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)

variable {K L D hgen}

theorem Afun_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (h : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    Afun K L D hgen φ (globalPoints (𝓞 L) L h * x) z = Afun K L D hgen φ x z := by
  unfold Afun
  refine finsum_mem_eq_of_bijOn _ (bijOn_sigmaConj_SU hgen h) fun δ _ => ?_
  rw [conj_identity, mul_cs_left, inv_mul_cancel_left]

theorem Afun_centralScalar_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    Afun K L D hgen φ (centralScalar (𝓞 L) L a * x) z = Afun K L D hgen φ x (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) := by
  unfold Afun
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [inv_cs_mul_conj]
  simp only [map_mul, map_inv, mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem sigmaAdelicAct_centralScalar_principal (q : Lˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : L →* L) q)) := by
  rw [sigmaAdelicAct_centralScalar, unitsAct_principal, centralScalar_principal]

theorem Afun_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Afun K L D hgen φ x (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) = Afun K L D hgen φ x z := by
  unfold Afun
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_SU hgen (Units.map (σ : L →* L) q)) fun δ _ => ?_
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

omit [IsGalois K L] in
theorem Bfun_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (x y : AdelicGL2 (𝓞 L) L) :
    Bfun K L D σ φ (globalPoints (𝓞 L) L h * x) y = Bfun K L D σ φ x ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  unfold Bfun
  exact finsum_mem_eq_of_bijOn _ (bijOn_sigmaConj_B1 σ hh) fun δ _ => congrArg φ (conj_identity K L D σ h δ x y)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem Bfun_mul_of_mem_B1 (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) {b : GL (Fin 2) L}
    (hb : b ∈ B1 K) :
    Bfun K L D σ φ x (globalPoints (𝓞 L) L b * y) = Bfun K L D σ φ x y := by
  unfold Bfun
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_B1 (map_mem_B1 σ hb)) fun δ _ => ?_
  rw [map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints', map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem Bfun_centralScalar_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (x y : AdelicGL2 (𝓞 L) L) :
    Bfun K L D σ φ x (centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) * y) =
      Bfun K L D σ φ x y := by
  rw [centralScalar_principal]
  exact Bfun_mul_of_mem_B1 φ x y (scalar_mem_B1 q)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem Bfun_centralScalar_mul_arg (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (x Y : AdelicGL2 (𝓞 L) L) :
    Bfun K L D σ φ (centralScalar (𝓞 L) L a * x) (Y * (centralScalar (𝓞 L) L a * x)) =
      Bfun K L D σ φ x (Y * (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹) * x)) := by
  unfold Bfun
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [inv_cs_mul_conj]

end KernelSums
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

section Box

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem borelSpace_adele : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L

attribute [local instance] borelSpace_adele

scoped instance isAddHaarMeasure_adelicAddHaar' : (adelicAddHaar (𝓞 L) L).IsAddHaarMeasure :=
  isAddHaarMeasure_adelicAddHaar (𝓞 L) L

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := countable_numberField L
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  unfold adelicAddHaar; infer_instance

theorem measurePreserving_smul_principal (q : Lˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 L) L =>
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) • x) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  set u := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)
  refine ⟨measurable_const_smul u, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_smul u) hs, Set.preimage_smul,
    ← distribHaarChar_mul (adelicAddHaar (𝓞 L) L) u⁻¹ s, map_inv]
  have : distribHaarChar (AdeleRing (𝓞 L) L) u = 1 := NumberField.AdeleRing.distribHaarChar_algebraMap L q
  rw [this, inv_one, ENNReal.coe_one, one_mul]

theorem integral_cond_adelicBox_comp_smul (h : AdeleRing (𝓞 L) L → ℂ)
    (hper : ∀ (l : L) (x : AdeleRing (𝓞 L) L), h (algebraMap L (AdeleRing (𝓞 L) L) l + x) = h x) (q : Lˣ) :
    ∫ x, h ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) • x)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) =
      ∫ x, h x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) := by
  set u := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)
  set μ := adelicAddHaar (𝓞 L) L with hμ
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  congr 1
  have hmp := measurePreserving_smul_principal L q
  let e : AdeleRing (𝓞 L) L ≃ᵐ AdeleRing (𝓞 L) L := (Homeomorph.smul u).toMeasurableEquiv
  have he : (e : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = fun x => u • x := rfl
  have hmpe : MeasurePreserving e μ μ := hmp
  have h1 : ∫ x in adelicBox L, h (u • x) ∂μ = ∫ y in e '' adelicBox L, h y ∂μ :=
    (hmpe.setIntegral_image_emb e.measurableEmbedding h (adelicBox L)).symm
  rw [h1]

  set G := AdeleRing.principalSubgroup (𝓞 L) L with hG
  have hB : IsAddFundamentalDomain G (adelicBox L) μ := isAddFundamentalDomain_adelicBox L μ
  let eG : G ≃ G :=
    { toFun := fun g => ⟨u⁻¹ • (g : AdeleRing (𝓞 L) L), by
        obtain ⟨_, l, rfl⟩ := g
        exact ⟨(q⁻¹ : Lˣ) * l, by rw [map_mul]; rfl⟩⟩
      invFun := fun g => ⟨u • (g : AdeleRing (𝓞 L) L), by
        obtain ⟨_, l, rfl⟩ := g
        exact ⟨(q : L) * l, by rw [map_mul]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (smul_inv_smul u (g : AdeleRing (𝓞 L) L))
      right_inv := fun g => Subtype.ext (inv_smul_smul u (g : AdeleRing (𝓞 L) L)) }
  have hB' : IsAddFundamentalDomain G (e '' adelicBox L) μ := by
    refine hB.image_of_equiv e.toEquiv ((hmpe.symm e).quasiMeasurePreserving) eG fun g x => ?_
    show u • ((u⁻¹ • (g : AdeleRing (𝓞 L) L)) + x) = (g : AdeleRing (𝓞 L) L) + u • x
    rw [smul_add, smul_inv_smul]
  haveI : Countable L := countable_numberField L
  haveI : Countable G := by
    have hc : (G : Set (AdeleRing (𝓞 L) L)).Countable := by
      rw [hG]; exact Set.countable_range (algebraMap L (AdeleRing (𝓞 L) L))
    exact hc.to_subtype
  refine hB'.setIntegral_eq hB fun g x => ?_
  obtain ⟨_, l, rfl⟩ := g
  exact hper l x

end Box
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicHeight
open IsDedekindDomain AutomorphicForm
open scoped NNReal ENNReal Pointwise

namespace R1UniVanish

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) {σ : L ≃ₐ[K] L}
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adele

variable (σ) in

def CTB (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) : ℂ :=
  constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) (fun t => unipotentGL2 t)
    (Bfun K L D σ φ x) y

def Efun (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  Afun K L D hgen φ x z -
    (highSet (adelicHeight L) (Real.exp R)).indicator (CTB K L D σ φ x) (centralScalar (𝓞 L) L z * x)

def Ifun {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z in ΩL, ξ' z * Efun K L D hgen R φ x z ∂νZL

variable {K L D hgen}

omit [IsGalois K L] in
theorem CTB_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    CTB K L D σ φ (globalPoints (𝓞 L) L h * x) (centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L h * x)) =
      CTB K L D σ φ x (centralScalar (𝓞 L) L z * x) := by
  have h00 : (h : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := apply_zero_zero_ne_zero_of_upper hh
  have h11 : (h : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := apply_one_one_ne_zero_of_upper hh
  set lam : Lˣ := Units.mk0 ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0)
    (div_ne_zero h11 h00) with hlam
  unfold CTB constantTerm constantTermIntegrand
  have hpt : ∀ q : AdeleRing (𝓞 L) L,
      Bfun K L D σ φ (globalPoints (𝓞 L) L h * x)
          (unipotentGL2 q * (centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L h * x))) =
        Bfun K L D σ φ x (unipotentGL2 ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) lam) • q) *
          (centralScalar (𝓞 L) L z * x)) := by
    intro q
    rw [Bfun_globalPoints_mul φ hh, ← mul_cs_left, ← mul_assoc (unipotentGL2 q), unipotentGL2_mul_globalPoints L hh,
      mul_assoc, inv_mul_cancel_left]
    rfl
  simp_rw [hpt]
  refine integral_cond_adelicBox_comp_smul L
    (fun t => Bfun K L D σ φ x (unipotentGL2 t * (centralScalar (𝓞 L) L z * x))) (fun l t => ?_) lam
  show Bfun K L D σ φ x (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l + t) * (centralScalar (𝓞 L) L z * x)) = _
  rw [unipotentGL2_add, ← globalPoints_unipotentGL2, mul_assoc, Bfun_mul_of_mem_B1 φ x _ (unipotentGL2_mem_B1 l)]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem CTB_centralScalar_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    CTB K L D σ φ (centralScalar (𝓞 L) L a * x) (centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * x)) =
      CTB K L D σ φ x (centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * x) := by
  unfold CTB constantTerm constantTermIntegrand
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show Bfun K L D σ φ (centralScalar (𝓞 L) L a * x) (unipotentGL2 q * (centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * x))) =
    Bfun K L D σ φ x (unipotentGL2 q * (centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * x))
  rw [← mul_assoc (unipotentGL2 q), Bfun_centralScalar_mul_arg]
  simp only [map_mul, map_inv, mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem CTB_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    CTB K L D σ φ x (centralScalar (𝓞 L) L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) * x) =
      CTB K L D σ φ x (centralScalar (𝓞 L) L z * x) := by
  unfold CTB constantTerm constantTermIntegrand
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show Bfun K L D σ φ x (unipotentGL2 n * (centralScalar (𝓞 L) L (Units.map _ q * z) * x)) =
    Bfun K L D σ φ x (unipotentGL2 n * (centralScalar (𝓞 L) L z * x))
  rw [map_mul, mul_assoc, mul_cs_left, Bfun_centralScalar_principal_mul]

theorem Efun_globalPoints_mul_of_mem (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Efun K L D hgen R φ (globalPoints (𝓞 L) L h * x) z = Efun K L D hgen R φ x z := by
  unfold Efun
  rw [Afun_globalPoints_mul]
  congr 1
  have hmem : centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L h * x) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L z * x ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, ← mul_cs_left,
      NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (γ := h) hh]
  by_cases hx : centralScalar (𝓞 L) L z * x ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), CTB_globalPoints_mul φ hh]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

theorem Efun_globalPoints_mul_of_not_mem (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0) {h₀ : ℝ} (hh₀ : 0 < h₀) (hR : h₀⁻¹ ≤ Real.exp R)
    {x : AdelicGL2 (𝓞 L) L} (hx : h₀ ≤ adelicHeight L x) (hγx : h₀ ≤ adelicHeight L (globalPoints (𝓞 L) L h * x))
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    Efun K L D hgen R φ (globalPoints (𝓞 L) L h * x) z = Efun K L D hgen R φ x z := by
  unfold Efun
  rw [Afun_globalPoints_mul]
  congr 1
  obtain ⟨h1, h2⟩ := adelicHeight_le_inv_of_not_mem_borelSubgroup L hh₀ hh hx hγx
  rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
  · rw [mem_highSet_iff, adelicHeight_centralScalar_mul, not_lt]
    exact h1.trans hR
  · rw [mem_highSet_iff, adelicHeight_centralScalar_mul, not_lt]
    exact h2.trans hR

theorem Efun_centralScalar_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ)
    (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Efun K L D hgen R φ (centralScalar (𝓞 L) L a * x) z = Efun K L D hgen R φ x (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) := by
  unfold Efun
  rw [Afun_centralScalar_mul]
  congr 1
  have hmem : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * x) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * x ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, adelicHeight_centralScalar_mul, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * x) ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx), CTB_centralScalar_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mpr h'))]

theorem Efun_principal_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (x : AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    Efun K L D hgen R φ x (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) =
      Efun K L D hgen R φ x z := by
  unfold Efun
  rw [Afun_principal_mul]
  congr 1
  have hmem : centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) * x ∈
        highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L z * x ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, adelicHeight_centralScalar_mul, adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * x ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), CTB_principal_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem countable_units : Countable Lˣ := by
  haveI : Countable L := countable_numberField L
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

theorem Ifun_centralScalar_mul {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsMulLeftInvariant] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    Ifun K L D hgen νZL ΩL (fun z => ((ξ' z : ℂˣ) : ℂ)) R φ (centralScalar (𝓞 L) L a * x) =
      ((ξ' (a * (D.unitsAct σ⁻¹ a)⁻¹) : ℂˣ) : ℂ)⁻¹ * Ifun K L D hgen νZL ΩL (fun z => ((ξ' z : ℂˣ) : ℂ)) R φ x := by
  unfold Ifun
  simp_rw [Efun_centralScalar_mul]
  generalize a * (D.unitsAct σ⁻¹ a)⁻¹ = t
  have hpt : ∀ z, ((ξ' z : ℂˣ) : ℂ) * Efun K L D hgen R φ x (z * t) =
      ((ξ' t : ℂˣ) : ℂ)⁻¹ * (((ξ' (t * z) : ℂˣ) : ℂ) * Efun K L D hgen R φ x (t * z)) := by
    intro z
    rw [mul_comm z t, map_mul, Units.val_mul]
    simp only [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1

  have h1 : ∫ z in ΩL, ((ξ' (t * z) : ℂˣ) : ℂ) * Efun K L D hgen R φ x (t * z) ∂νZL =
      ∫ w in t • ΩL, ((ξ' w : ℂˣ) : ℂ) * Efun K L D hgen R φ x w ∂νZL := by
    rw [← Set.image_smul]
    exact ((measurePreserving_mul_left νZL t).setIntegral_image_emb (MeasurableEquiv.mulLeft t).measurableEmbedding
      (fun w => ((ξ' w : ℂˣ) : ℂ) * Efun K L D hgen R φ x w) ΩL).symm
  rw [h1]
  haveI : Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
    haveI := countable_units (L := L)
    exact (MonoidHom.rangeRestrict_surjective _).countable
  refine (hΩL.smul_of_comm t).setIntegral_eq hΩL fun g w => ?_
  obtain ⟨_, q, rfl⟩ := g
  show ((ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) : ℂˣ) : ℂ) *
      Efun K L D hgen R φ x (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) =
    ((ξ' w : ℂˣ) : ℂ) * Efun K L D hgen R φ x w
  rw [map_mul, hξt, one_mul, Efun_principal_mul]

end Fold
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicHeight NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm
open scoped NNReal ENNReal Pointwise

namespace R1UniVanish

section Slab

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adele

theorem borelSpace_GL2 : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_GL2

scoped instance isHaarMeasure_adelicGLHaar' : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc

theorem det_globalPoints (γ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem ideleNorm_principal (q : Lˣ) :
    ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom q) = 1 := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_algebraMap L q]
  simp

theorem ideleNorm_det_globalPoints_mul (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ * g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_globalPoints, ideleNorm_principal, one_mul]

theorem det_centralScalar (w : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w) = w * w := by
  refine Units.ext ?_
  show Matrix.det (Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L)) = (w : AdeleRing (𝓞 L) L) * w
  rw [Matrix.det_fin_two]
  simp [Matrix.scalar_apply]

theorem ideleNorm_det_centralScalar_mul {w : (AdeleRing (𝓞 L) L)ˣ} (hw : ideleNorm L w = 1) (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w * g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_centralScalar, ideleNorm_mul, hw, one_mul, one_mul]

theorem smulInvariantMeasure_restrict (H : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Set (AdelicGL2 (𝓞 L) L))
    (hinv : ∀ h ∈ H, ∀ x, h * x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure H (AdelicGL2 (𝓞 L) L) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S) := by
  refine ⟨fun h A hA => ?_⟩
  obtain ⟨h, hh⟩ := h
  show (adelicGLHaar (Fin 2) (𝓞 L) L).restrict S ((fun x => h * x) ⁻¹' A) =
    (adelicGLHaar (Fin 2) (𝓞 L) L).restrict S A
  rw [Measure.restrict_apply (measurableSet_preimage (measurable_const_mul h) hA), Measure.restrict_apply hA]
  have hset : (fun x => h * x) ⁻¹' A ∩ S = (fun x => h * x) ⁻¹' (A ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hinv h hh]
  rw [hset, measure_preimage_mul]

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine smulInvariantMeasure_restrict L _ _ fun h hh x => ?_
  obtain ⟨γ, rfl⟩ := hh
  show ideleNorm L (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ * x)) ∈ Set.Icc α β ↔
    ideleNorm L (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
  rw [ideleNorm_det_globalPoints_mul]

def normOneCentre : Subgroup (AdelicGL2 (𝓞 L) L) := (normOneIdeles L).map (centralScalar (𝓞 L) L)

theorem smulInvariantMeasure_restrict_slab_centre (α β : ℝ) :
    SMulInvariantMeasure (normOneCentre L) (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine smulInvariantMeasure_restrict L _ _ fun h hh x => ?_
  obtain ⟨w, hw, rfl⟩ := hh
  show ideleNorm L (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w * x)) ∈ Set.Icc α β ↔
    ideleNorm L (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
  rw [ideleNorm_det_centralScalar_mul L ((mem_normOneIdeles_iff w).mp hw)]

scoped instance smulCommClass_centre :
    SMulCommClass (normOneCentre L) (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L) := by
  refine ⟨fun a b x => ?_⟩
  obtain ⟨_, ⟨w, -, rfl⟩⟩ := a
  obtain ⟨b, hb⟩ := b
  show centralScalar (𝓞 L) L w * (b * x) = b * (centralScalar (𝓞 L) L w * x)
  rw [mul_cs_left]

theorem countable_range_globalPoints : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_GL2 L
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L)).countable

end Slab
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

section LocalInvariance

variable {G α E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem setIntegral_eq_of_localInvariant {s t : Set α} {μ : Measure α} [MeasurableConstSMul G α]
    [SMulInvariantMeasure G α μ] [Countable G] (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (Y : Set α) (hsY : s ⊆ Y) (htY : t ⊆ Y) {f : α → E}
    (hf : ∀ (g : G) (x : α), x ∈ Y → g • x ∈ Y → f (g • x) = f x) :
    ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  classical
  let Fo : Set α → E := fun S => if h : ∃ y ∈ S, y ∈ Y then f h.choose else 0
  let F : α → E := fun x => Fo (MulAction.orbit G x)
  have hFinv : ∀ (g : G) (x : α), F (g • x) = F x := fun g x => congrArg Fo (MulAction.orbit_smul g x)
  have hFY : ∀ x ∈ Y, F x = f x := by
    intro x hx
    have h : ∃ y ∈ MulAction.orbit G x, y ∈ Y := ⟨x, MulAction.mem_orbit_self x, hx⟩
    show Fo (MulAction.orbit G x) = f x
    simp only [Fo, dif_pos h]
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h.choose_spec.1
    rw [← hg]
    exact hf g x hx (hg ▸ h.choose_spec.2)
  calc ∫ x in s, f x ∂μ = ∫ x in s, F x ∂μ :=
        setIntegral_congr_fun₀ hs.nullMeasurableSet fun x hx => (hFY x (hsY hx)).symm
    _ = ∫ x in t, F x ∂μ := hs.setIntegral_eq ht hFinv
    _ = ∫ x in t, f x ∂μ := setIntegral_congr_fun₀ ht.nullMeasurableSet fun x hx => hFY x (htY hx)

end LocalInvariance
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

end R1UniVanish
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.R1UniVanish"

open R1UniVanish
open NumberField.AdelicLevel
open scoped TensorProduct ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
            ¬ (∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
        ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 := by
  intro T hT ws w' hw' ϖs hirr hϖs0 ns rTs hcos zs hzs hnot ks js φ φf hfac
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_GL2 L

  obtain ⟨h₀, hh₀, hfloor⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact L c u d₁ d₂ hc Tc hTc
  have hY : ∀ x ∈ Φ₀, h₀ ≤ adelicHeight L x := by
    intro x hx
    have hx' := hΦ₀S hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx'
    obtain ⟨y, hy, g, hg, rfl⟩ := hx'
    exact hfloor g hg y hy
  refine ⟨Real.log h₀⁻¹, fun R hR => ?_⟩
  have hR' : h₀⁻¹ ≤ Real.exp R := by
    rw [← Real.exp_log (inv_pos.mpr hh₀)]
    exact Real.exp_le_exp.mpr hR

  let ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (Subgroup.topEquiv (G := (AdeleRing (𝓞 L) L)ˣ)).symm.toMonoidHom
  have hξ' : ∀ z, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hξt' : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1 :=
    fun q => hξt _ ⟨q, rfl⟩
  obtain ⟨b, hb1, hbne⟩ := exists_ideleNorm_eq_one_and_ne D σ ξ' (by
    push Not at hnot
    exact hnot)
  set a : (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ b with ha
  have hσa : D.unitsAct σ⁻¹ a = b := by
    rw [ha, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have ha1 : ideleNorm L a = 1 := by rw [ha, ideleNorm_unitsAct]; exact hb1
  set χ : ℂ := ((ξ' (a * (D.unitsAct σ⁻¹ a)⁻¹) : ℂˣ) : ℂ)⁻¹ with hχ
  have hχ1 : χ ≠ 1 := by
    intro h1
    rw [hχ, hσa, inv_eq_one, Units.val_eq_one, map_mul, map_inv, mul_inv_eq_one] at h1
    exact hbne h1

  set I : AdelicGL2 (𝓞 L) L → ℂ := Ifun K L D hgen νZL ΩL (fun z => ((ξ' z : ℂˣ) : ℂ)) R φ with hI
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  show ∫ x in Φ₀, I x ∂μ = 0

  have hIcs : ∀ x, I (centralScalar (𝓞 L) L a * x) = χ * I x := fun x =>
    Ifun_centralScalar_mul νZL ΩL hΩL ξ' hξt' R φ a x

  have hJ1 : ∫ x in Φ₀, I x ∂μ = χ * ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, I x ∂μ := by
    have h := (measurePreserving_mul_left μ (centralScalar (𝓞 L) L a)).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft (centralScalar (𝓞 L) L a)).measurableEmbedding I Φ₀
    have hpre : (fun x => centralScalar (𝓞 L) L a * x) ⁻¹' Φ₀ = (centralScalar (𝓞 L) L a)⁻¹ • Φ₀ :=
      Set.preimage_smul (centralScalar (𝓞 L) L a) Φ₀
    rw [← h, hpre]
    simp_rw [hIcs]
    exact integral_const_mul _ _

  have hsub : (centralScalar (𝓞 L) L a)⁻¹ • Φ₀ ⊆ slab L α β := by
    rintro _ ⟨y, hy, rfl⟩
    show ideleNorm L (Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 L) L a)⁻¹ * y)) ∈ Set.Icc α β
    rw [← map_inv, ideleNorm_det_centralScalar_mul L (by rw [ideleNorm_inv, ha1, inv_one])]
    exact hΦ₀s hy
  have hJ2 : ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, I x ∂μ = ∫ x in Φ₀, I x ∂μ := by
    rw [← Measure.restrict_restrict_of_subset hsub, ← Measure.restrict_restrict_of_subset (μ := μ) hΦ₀s]
    change ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, I x ∂(μ.restrict (slab L α β)) =
      ∫ x in Φ₀, I x ∂(μ.restrict (slab L α β))
    haveI := smulInvariantMeasure_restrict_slab L α β
    haveI := smulInvariantMeasure_restrict_slab_centre L α β
    haveI := countable_range_globalPoints L
    have hs : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ (μ.restrict (slab L α β)) := hΦ₀
    have hmem : (centralScalar (𝓞 L) L a)⁻¹ ∈ normOneCentre L :=
      ⟨a⁻¹, (mem_normOneIdeles_iff _).mpr (by rw [ideleNorm_inv, ha1, inv_one]), map_inv _ _⟩
    have ht : IsFundamentalDomain (globalPoints (𝓞 L) L).range ((centralScalar (𝓞 L) L a)⁻¹ • Φ₀)
        (μ.restrict (slab L α β)) :=
      hs.smul_of_comm (G' := normOneCentre L) ⟨(centralScalar (𝓞 L) L a)⁻¹, hmem⟩
    symm
    refine setIntegral_eq_of_localInvariant hs ht {x | h₀ ≤ adelicHeight L x} (fun x hx => hY x hx) ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      show h₀ ≤ adelicHeight L ((centralScalar (𝓞 L) L a)⁻¹ * y)
      rw [← map_inv, adelicHeight_centralScalar_mul]
      exact hY y hy
    · rintro ⟨_, h, rfl⟩ x hx hhx
      change h₀ ≤ adelicHeight L (globalPoints (𝓞 L) L h * x) at hhx
      show I (globalPoints (𝓞 L) L h * x) = I x
      by_cases hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
      · simp only [hI, Ifun, Efun_globalPoints_mul_of_mem R φ hh]
      · simp only [hI, Ifun, Efun_globalPoints_mul_of_not_mem R φ hh hh₀ hR' hx hhx]

  rw [hJ2] at hJ1
  have hzero : (1 - χ) * ∫ x in Φ₀, I x ∂μ = 0 := by rw [sub_mul, one_mul, ← hJ1, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ1
  · exact h

end
end S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram (solution)
