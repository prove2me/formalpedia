-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7fdbedae-b505-5fff-805e-2baecacabb82

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Theorems.Thm_NumberField_InfiniteAdeleRing_isEmbedding_units_val
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

noncomputable section

namespace MLPR

open scoped Classical

variable (K : Type) [Field K] [NumberField K]

local notation "MS" => NumberField.mixedEmbedding.mixedSpace K
local notation "Kinf" => InfiniteAdeleRing K
local notation "ι" => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
theorem norm_apply_eq_norm_coord (y : Kinf) (w : InfinitePlace K) (hw : w.IsReal) :
    ‖NumberField.AdelicLevel.archEval K w y‖ = ‖(ι y).1 ⟨w, hw⟩‖ := by
  rw [NumberField.AdelicLevel.archEval_apply]
  simp only [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm

theorem isUnit_iff_forall_ne_zero (y : Kinf) : IsUnit y ↔ ∀ w : InfinitePlace K, y w ≠ 0 := by
  have h := @Pi.isUnit_iff (InfinitePlace K) (fun w => w.Completion) _ y
  exact h.trans (forall_congr' fun w => isUnit_iff_ne_zero)

theorem isOpen_setOf_isUnit : IsOpen {y : Kinf | IsUnit y} := by
  have h : {y : Kinf | IsUnit y} = ⋂ w : InfinitePlace K, {y | y w ≠ 0} := by
    ext y; simp [isUnit_iff_forall_ne_zero]
  rw [h]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const

section Bump
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
omit K in
theorem exists_smooth_bump {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ S, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  set U' : Set E := U ∩ Metric.ball 0 R with hU'
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hd : Disjoint U'ᶜ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx ⟨hSU hxS, hR hxS⟩
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hU'o.isClosed_compl hS.isClosed hd
  obtain ⟨V, hVo, hsV, hV⟩ := eventually_nhdsSet_iff_exists.mp hf0
  have hts : tsupport (⇑f) ⊆ U' := by
    refine (closure_minimal (fun x hx => ?_) hVo.isClosed_compl).trans (Set.compl_subset_comm.mp hsV)
    exact fun hxV => hx (hV x hxV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, fun x hx => hf1.self_of_nhdsSet x hx,
    hts.trans Set.inter_subset_left⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport _)
    (hts.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
end Bump

theorem contDiff_boxIntegral
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (A₀ : (P × Y) × ℝ → ℂ) (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀) (ρf : P → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρf)
    (wY : Y → ℝ) (hwY : ContDiff ℝ (⊤ : ℕ∞) wY) (hwYc : HasCompactSupport wY) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ y, (wY y : ℝ) • A₀ ((p, y), ρf p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  let χ' : ContDiffBump p₀ := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨w', hw', hw'c, hw'1, -⟩ := exists_smooth_bump (E := Y) hwYc isOpen_univ (Set.subset_univ _)
  let Φ : Y × P → ℂ := fun q => ((w' q.1 * (χ' : P → ℝ) q.2 : ℝ)) • A₀ ((q.2, q.1), ρf q.2)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    refine ContDiff.smul ((hw'.comp contDiff_fst).mul (χ'.contDiff.comp contDiff_snd)) ?_
    exact hA₀.comp ((contDiff_snd.prodMk contDiff_fst).prodMk (hρ.comp contDiff_snd))
  have hΦc : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (hw'c.prod χ'.hasCompactSupport) fun q hq => ?_
    simp only [Set.mem_prod, not_and_or] at hq
    show ((w' q.1 * (χ' : P → ℝ) q.2 : ℝ)) • A₀ ((q.2, q.1), ρf q.2) = 0
    rcases hq with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport h, mul_zero, zero_smul]
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ y, (wY y) • Φ (id y, p) ∂volume) :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport (volume : Measure Y) id continuous_id
      wY hwY.continuous hwYc Φ hΦ hΦc
  have hGI : ∀ p : P, (∫ y, (wY y) • Φ (id y, p) ∂volume) =
      (((χ' : P → ℝ) p : ℝ) : ℂ) * ∫ y, (wY y : ℝ) • A₀ ((p, y), ρf p) := by
    intro p
    rw [← Complex.real_smul, ← integral_smul]
    congr 1
    funext y
    show (wY y) • (((w' y * (χ' : P → ℝ) p : ℝ)) • A₀ ((p, y), ρf p)) = ((χ' : P → ℝ) p) • ((wY y : ℝ) • A₀ ((p, y), ρf p))
    by_cases hy : wY y = 0
    · rw [hy, zero_smul, zero_smul, smul_zero]
    · rw [hw'1 y (subset_tsupport _ hy), one_mul, smul_comm]
  have hev : (fun p : P => ∫ y, (wY y : ℝ) • A₀ ((p, y), ρf p)) =ᶠ[nhds p₀]
      fun p : P => ∫ y, (wY y) • Φ (id y, p) ∂volume := by
    filter_upwards [Metric.closedBall_mem_nhds p₀ one_pos] with p hp
    rw [hGI p, χ'.one_of_mem_closedBall hp, Complex.ofReal_one, one_mul]
  exact hG.contDiffAt.congr_of_eventuallyEq hev

theorem abs_log_sq_add_sq_le (s ρ : ℝ) :
    |Real.log (s ^ 2 + ρ ^ 2)| ≤ |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)| := by
  have h1 : 0 ≤ Real.log (1 + s ^ 2) := Real.log_nonneg (by nlinarith)
  have h2 : 0 ≤ Real.log (1 + ρ ^ 2) := Real.log_nonneg (by nlinarith)
  by_cases hs : s = 0
  · subst hs
    have e1 : ((0 : ℝ) ^ 2 + ρ ^ 2) = ρ ^ 2 := by ring
    have e2 : Real.log ((0 : ℝ) ^ 2) = 0 := by simp
    have e3 : Real.log (1 + (0 : ℝ) ^ 2) = 0 := by simp
    rw [e1, e2, e3, abs_zero, zero_add, zero_add]
    linarith [abs_nonneg (Real.log (ρ ^ 2))]
  have hs2 : 0 < s ^ 2 := by positivity
  by_cases hle : s ^ 2 + ρ ^ 2 < 1
  · have hlt0 : Real.log (s ^ 2 + ρ ^ 2) ≤ 0 := Real.log_nonpos (by positivity) hle.le
    have hge : Real.log (s ^ 2) ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_le_log hs2 (by nlinarith)
    rw [abs_of_nonpos hlt0]
    have : |Real.log (s ^ 2)| = -Real.log (s ^ 2) := abs_of_nonpos (hge.trans hlt0)
    linarith [abs_nonneg (Real.log (ρ ^ 2))]
  · push Not at hle
    have hpos : 0 ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_nonneg hle
    rw [abs_of_nonneg hpos]
    have hprod : s ^ 2 + ρ ^ 2 ≤ (1 + s ^ 2) * (1 + ρ ^ 2) := by nlinarith
    calc Real.log (s ^ 2 + ρ ^ 2) ≤ Real.log ((1 + s ^ 2) * (1 + ρ ^ 2)) :=
          Real.log_le_log (by linarith) hprod
      _ = Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) := Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith [abs_nonneg (Real.log (s ^ 2)), abs_nonneg (Real.log (ρ ^ 2))]

theorem integrableOn_logBound' (R ρ : ℝ) :
    IntegrableOn (fun s : ℝ => |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)|)
      (Set.Icc (-R) R) := by
  have h1 : IntervalIntegrable (fun s : ℝ => |Real.log (s ^ 2)|) volume (-R) R := by
    have : (fun s : ℝ => |Real.log (s ^ 2)|) = fun s => |(2 : ℝ) * Real.log s| := by
      funext s; rw [Real.log_pow]; norm_num
    rw [this]
    exact (intervalIntegral.intervalIntegrable_log'.const_mul 2).abs
  have hc : Continuous fun s : ℝ => Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)| := by
    refine (Continuous.add ?_ continuous_const).add continuous_const
    refine continuous_iff_continuousAt.mpr fun s => ?_
    exact (Real.continuousAt_log (by positivity)).comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).continuousAt
  have h2 := hc.intervalIntegrable (μ := volume) (-R) R
  by_cases hR : 0 ≤ R
  · have := (h1.add h2)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at this
    refine this.congr_fun (fun s _ => by ring) measurableSet_Icc
  · rw [Set.Icc_eq_empty (by linarith)]
    exact integrableOn_empty

theorem haar_map [MeasurableSpace Kinf] [BorelSpace Kinf] (lam : Measure Kinf) [lam.IsAddHaarMeasure] :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map (ι : Kinf → MS) lam = c • (volume : Measure MS) := by
  have hH := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  set eH : Kinf ≃ₜ MS := hH.homeomorph (ι) with heH
  set eA : Kinf ≃ₜ+ MS :=
    { (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv with
      continuous_toFun := eH.continuous
      continuous_invFun := by
        have : ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm : MS → Kinf) = eH.symm := by
          funext y
          apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
          rw [show ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm y) =
            (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y from rfl, RingEquiv.apply_symm_apply]
          exact (eH.apply_symm_apply y).symm
        rw [AddEquiv.toEquiv_eq_coe]
        show Continuous ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm : MS → Kinf)
        rw [this]; exact eH.symm.continuous } with heA
  have heAc : (eA : Kinf → MS) = ι := rfl
  haveI : (Measure.map (ι : Kinf → MS) lam).IsAddHaarMeasure := by
    rw [← heAc]; exact eA.isAddHaarMeasure_map lam
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map (ι : Kinf → MS) lam = c • (volume : Measure MS) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : Measure.map (ι : Kinf → MS) lam = 0 := by rw [hc, h0, zero_smul]
    have h2 : Measure.map (ι : Kinf → MS) lam Set.univ = 0 := by rw [h1]; rfl
    rw [Measure.map_apply hH.continuous.measurable MeasurableSet.univ, Set.preimage_univ] at h2
    exact (IsOpen.measure_ne_zero lam isOpen_univ Set.univ_nonempty) h2
  exact ⟨c, hc0, hc⟩

theorem haar_transport [MeasurableSpace Kinf] [BorelSpace Kinf] (lam : Measure Kinf) [lam.IsAddHaarMeasure] :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ F : MS → ℂ, ∫ x, F (ι x) ∂lam = ((c : ℝ) : ℂ) * ∫ X, F X ∂volume := by
  have hH := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  set eH : Kinf ≃ₜ MS := hH.homeomorph (ι) with heH
  have heHc : (eH : Kinf → MS) = ι := rfl
  set eA : Kinf ≃ₜ+ MS :=
    { (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv with
      continuous_toFun := eH.continuous
      continuous_invFun := by
        have : ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm : MS → Kinf) = eH.symm := by
          funext y
          apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
          rw [show ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm y) =
            (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y from rfl, RingEquiv.apply_symm_apply]
          exact (eH.apply_symm_apply y).symm
        rw [AddEquiv.toEquiv_eq_coe]
        show Continuous ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.symm : MS → Kinf)
        rw [this]; exact eH.symm.continuous } with heA
  have heAc : (eA : Kinf → MS) = ι := rfl
  haveI : (Measure.map (ι : Kinf → MS) lam).IsAddHaarMeasure := by
    rw [← heAc]; exact eA.isAddHaarMeasure_map lam
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map (ι : Kinf → MS) lam = c • (volume : Measure MS) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : Measure.map (ι : Kinf → MS) lam = 0 := by rw [hc, h0, zero_smul]
    have h2 : Measure.map (ι : Kinf → MS) lam Set.univ = 0 := by rw [h1]; rfl
    rw [Measure.map_apply hH.continuous.measurable MeasurableSet.univ, Set.preimage_univ] at h2
    exact (IsOpen.measure_ne_zero lam isOpen_univ Set.univ_nonempty) h2
  refine ⟨c, hc0, fun F => ?_⟩
  have h3 : ∫ x, F (ι x) ∂lam = ∫ X, F X ∂(Measure.map (eH.toMeasurableEquiv : Kinf → MS) lam) :=
    (integral_map_equiv eH.toMeasurableEquiv F).symm
  rw [h3, Homeomorph.toMeasurableEquiv_coe, heHc, hc]
  rw [show ((c • (volume : Measure MS)) : Measure MS) = ((c : ENNReal) • (volume : Measure MS)) from rfl,
    integral_smul_measure, ENNReal.coe_toReal, RCLike.real_smul_eq_coe_mul]
  rfl

end MLPR

end

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨc : HasCompactSupport Ψ)
    (hΨu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ),
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) lam ∧
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ)) lam ∧
        ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ) ∂lam =
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  classical

  have hιH := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  obtain ⟨c', hc', hHT⟩ := MLPR.haar_transport K lam
  obtain ⟨e, he, he1⟩ := NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal K ⟨w, hw⟩
  have hιc : Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
    have h : ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
        NumberField.mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) =
        (hιH.homeomorph (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K)).symm := by
      funext y
      apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
      rw [RingEquiv.apply_symm_apply]
      exact ((hιH.homeomorph (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K)).apply_symm_apply y).symm
    rw [h]
    exact (hιH.homeomorph _).symm.continuous

  obtain ⟨g, hg_def⟩ : ∃ g : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) ×
      (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})} → ℝ) ×
        ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ))) × ℝ → ℂ,
      g = fun q => Ψ ![q.1.1 0, q.1.1 1, e.symm (q.2, q.1.2)] := ⟨_, rfl⟩
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [hg_def]
    refine hΨ.comp ?_
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · show ContDiff ℝ (⊤ : ℕ∞) fun x : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => x.1.1 0
      exact (contDiff_apply ℝ _ 0).comp (contDiff_fst.comp contDiff_fst)
    · show ContDiff ℝ (⊤ : ℕ∞) fun x : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => x.1.1 1
      exact (contDiff_apply ℝ _ 1).comp (contDiff_fst.comp contDiff_fst)
    · show ContDiff ℝ (⊤ : ℕ∞) fun x : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => e.symm (x.2, x.1.2)
      exact e.symm.contDiff.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have hgc : HasCompactSupport g := by

    let asm : (((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) ×
        (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})} → ℝ) ×
          ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ))) × ℝ) ≃ₜ (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) :=
      { toFun := fun q => ![q.1.1 0, q.1.1 1, e.symm (q.2, q.1.2)]
        invFun := fun p => ((![p 0, p 1], (e (p 2)).2), (e (p 2)).1)
        left_inv := by
          rintro ⟨⟨a, r⟩, s⟩
          have h2 : (![a 0, a 1, e.symm (s, r)] : Fin 3 → NumberField.mixedEmbedding.mixedSpace K) 2 = e.symm (s, r) := rfl
          simp only [h2, ContinuousLinearEquiv.apply_symm_apply]
          refine Prod.ext (Prod.ext ?_ rfl) rfl
          funext i
          fin_cases i <;> rfl
        right_inv := fun p => by
          funext i
          fin_cases i
          · rfl
          · rfl
          · show e.symm ((e (p 2)).1, (e (p 2)).2) = p 2
            rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
        continuous_toFun := by
          refine continuous_pi fun i => ?_
          fin_cases i
          · show Continuous fun q : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => q.1.1 0
            exact (continuous_apply 0).comp (continuous_fst.comp continuous_fst)
          · show Continuous fun q : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => q.1.1 1
            exact (continuous_apply 1).comp (continuous_fst.comp continuous_fst)
          · show Continuous fun q : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × _) × ℝ => e.symm (q.2, q.1.2)
            exact e.symm.continuous.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
        continuous_invFun := by
          refine ((continuous_pi fun i => ?_).prodMk
            (continuous_snd.comp (e.continuous.comp (continuous_apply 2)))).prodMk
            (continuous_fst.comp (e.continuous.comp (continuous_apply 2)))
          fin_cases i
          · show Continuous fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => p 0
            exact continuous_apply 0
          · show Continuous fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => p 1
            exact continuous_apply 1 }
    have hg_eq : g = Ψ ∘ asm := by rw [hg_def]; rfl
    rw [hg_eq]
    exact hΨc.comp_homeomorph asm
  obtain ⟨A₀, B₀, hA₀, hB₀, hD0⟩ :=
    MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport g hg hgc

  obtain ⟨ρf, hρf⟩ : ∃ ρf : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ,
      ρf = fun p => 1 - (p 0).1 ⟨w, hw⟩ := ⟨_, rfl⟩
  have hρs : ContDiff ℝ (⊤ : ℕ∞) ρf := by
    rw [hρf]
    exact contDiff_const.sub ((contDiff_apply ℝ ℝ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})).comp
      (contDiff_fst.comp (contDiff_apply ℝ _ 0)))
  have hρt : ∀ t : (InfiniteAdeleRing K)ˣ,
      ρf ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
           NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K)] =
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))).1 ⟨w, hw⟩ := by
    intro t
    rw [hρf]
    simp only [Matrix.cons_val_zero, map_sub, map_one, Prod.fst_sub, Prod.fst_one, Pi.sub_apply, Pi.one_apply]

  obtain ⟨Ca, hCa, hCar⟩ := hΨu

  obtain ⟨U2, hU2⟩ : ∃ U2 : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K), U2 = {p | IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
      IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))} := ⟨_, rfl⟩
  have hU2o : IsOpen U2 := by
    rw [hU2]
    exact ((MLPR.isOpen_setOf_isUnit K).preimage (hιc.comp (continuous_apply 0))).inter
      ((MLPR.isOpen_setOf_isUnit K).preimage (hιc.comp (continuous_apply 1)))
  obtain ⟨S2, hS2⟩ : ∃ S2 : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K), S2 = (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => (![p 0, p 1] : Fin 2 → NumberField.mixedEmbedding.mixedSpace K)) '' tsupport Ψ := ⟨_, rfl⟩
  have hS2c : IsCompact S2 := by
    rw [hS2]
    refine hΨc.image (continuous_pi fun i => ?_)
    fin_cases i
    · exact (show Continuous (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => p 0) from continuous_apply 0)
    · exact (show Continuous (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => p 1) from continuous_apply 1)
  have hS2U : S2 ⊆ U2 := by
    rw [hS2, hU2]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, -, h0, h1⟩ := hCar p hp
    simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h0, h1,
      RingEquiv.symm_apply_apply]
    exact ⟨Units.isUnit _, Units.isUnit _⟩
  obtain ⟨χ, hχ, hχc, hχ1, hχU⟩ := MLPR.exists_smooth_bump (E := Fin 2 → NumberField.mixedEmbedding.mixedSpace K) hS2c hU2o hS2U

  obtain ⟨SY, hSY⟩ : ∃ SY : Set (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})} → ℝ) ×
        ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ)),
      SY = (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace K => (e (p 2)).2) '' tsupport Ψ := ⟨_, rfl⟩
  have hSYc : IsCompact SY := by
    rw [hSY]; exact hΨc.image ((continuous_snd.comp e.continuous).comp (continuous_apply 2))
  obtain ⟨wY, hwY, hwYc, hwY1, -⟩ := MLPR.exists_smooth_bump hSYc isOpen_univ (Set.subset_univ _)

  obtain ⟨At, hAt⟩ : ∃ At : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      At = fun p => ((c' : ℝ) : ℂ) * ∫ y, (wY y : ℝ) • A₀ ((p, y), ρf p) := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      Bt = fun p => ((c' : ℝ) : ℂ) * ∫ y, (wY y : ℝ) • B₀ ((p, y), ρf p) := ⟨_, rfl⟩
  have hAts : ContDiff ℝ (⊤ : ℕ∞) At := by
    rw [hAt]
    exact contDiff_const.mul (MLPR.contDiff_boxIntegral A₀ hA₀ ρf hρs wY hwY hwYc)
  have hBts : ContDiff ℝ (⊤ : ℕ∞) Bt := by
    rw [hBt]
    exact contDiff_const.mul (MLPR.contDiff_boxIntegral B₀ hB₀ ρf hρs wY hwY hwYc)
  refine ⟨fun p => ((χ p : ℝ) : ℂ) * At p, fun p => ((χ p : ℝ) : ℂ) * Bt p, ?_, ?_, ?_, ?_, ?_, fun a t => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hχ).mul hAts
  · exact (Complex.ofRealCLM.contDiff.comp hχ).mul hBts
  · exact (hχc.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)).mul_right
  · exact (hχc.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)).mul_right
  ·
    have hUE := NumberField.InfiniteAdeleRing.isEmbedding_units_val K
    have hco : tsupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => ((χ p : ℝ) : ℂ)) ⊆ tsupport χ := by
      intro p hp
      by_contra h
      have h0 := notMem_tsupport_iff_eventuallyEq.mp h
      refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hp
      filter_upwards [h0] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, Complex.ofReal_zero]
    have hsubχ : tsupport (fun p => ((χ p : ℝ) : ℂ) * At p) ∪ tsupport (fun p => ((χ p : ℝ) : ℂ) * Bt p) ⊆ tsupport χ :=
      Set.union_subset ((tsupport_mul_subset_left (f := fun p => ((χ p : ℝ) : ℂ)) (g := At)).trans hco)
        ((tsupport_mul_subset_left (f := fun p => ((χ p : ℝ) : ℂ)) (g := Bt)).trans hco)
    obtain ⟨C, hC⟩ : ∃ C : Fin 2 → Set ((InfiniteAdeleRing K)ˣ), C = fun i =>
        Units.val ⁻¹' ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p i)) '' tsupport χ) :=
      ⟨_, rfl⟩
    have hCc : ∀ i : Fin 2, IsCompact (C i) := by
      intro i
      rw [hC]
      refine hUE.isInducing.isCompact_iff.mpr ?_
      have hsub : (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p i)) '' tsupport χ ⊆
          Set.range (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) := by
        rintro _ ⟨p, hp, rfl⟩
        have hpU := hχU hp
        rw [hU2] at hpU
        fin_cases i
        · obtain ⟨u, hu⟩ := hpU.1; exact ⟨u, hu⟩
        · obtain ⟨u, hu⟩ := hpU.2; exact ⟨u, hu⟩
      rw [Set.image_preimage_eq_of_subset hsub]
      exact hχc.image (hιc.comp (continuous_apply i))
    refine ⟨C 0 ×ˢ C 1, (hCc 0).prod (hCc 1), fun p hp => ?_⟩
    have hp' := hsubχ hp
    have hpU := hχU hp'
    rw [hU2] at hpU
    obtain ⟨u₀, hu₀⟩ := hpU.1
    obtain ⟨u₁, hu₁⟩ := hpU.2
    refine ⟨(u₀, u₁), ⟨?_, ?_⟩, ?_⟩
    · show u₀ ∈ C 0
      rw [hC]; exact ⟨p, hp', hu₀.symm⟩
    · show u₁ ∈ C 1
      rw [hC]; exact ⟨p, hp', hu₁.symm⟩
    · funext i
      fin_cases i
      · show p 0 = _
        rw [hu₀, RingEquiv.apply_symm_apply]; rfl
      · show p 1 = _
        rw [hu₁, RingEquiv.apply_symm_apply]; rfl
  ·
    set P : Fin 2 → NumberField.mixedEmbedding.mixedSpace K :=
      ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] with hP
    set ρ : ℝ := ρf P with hρdef
    have hP0 : P 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K) := rfl
    have hP1 : P 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K) := rfl
    have hx1 : ∀ x : InfiniteAdeleRing K, ‖NumberField.AdelicLevel.archEval K w x‖ =
        |(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x).1 ⟨w, hw⟩| := fun x => by
      rw [MLPR.norm_apply_eq_norm_coord K _ w hw, Real.norm_eq_abs]
    have hρ1 : ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ = |ρ| := by
      rw [hx1]
      congr 1
      rw [hρdef, hρf, map_sub, map_one]
      simp only [hP0, Prod.fst_sub, Prod.fst_one, Pi.sub_apply, Pi.one_apply]

    set F : NumberField.mixedEmbedding.mixedSpace K → ℂ := fun X =>
      Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), X] *
        ((Real.log ((X.1 ⟨w, hw⟩) ^ 2 + ρ ^ 2) : ℝ) : ℂ) with hF
    set G : ℝ × (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})} → ℝ) ×
        ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ)) → ℂ :=
      fun q => g ((P, q.2), q.1) * ((Real.log (q.1 ^ 2 + ρ ^ 2) : ℝ) : ℂ) with hG
    have hFG : ∀ X, G (e X) = F X := by
      intro X
      have h3 : e.symm (X.1 ⟨w, hw⟩, (e X).2) = X := by
        rw [← he1 X]; exact e.symm_apply_apply X
      simp only [hG, hF, hg_def, he1 X, hP0, hP1, h3]

    have hA : (∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
        ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
          ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ) ∂lam) = ((c' : ℝ) : ℂ) * ∫ X, F X := by
      rw [← hHT F]
      congr 1; funext x
      simp only [hF, hρ1, hx1, sq_abs]
      ring_nf

    have hB : ∫ X, F X = ∫ q, G q := by
      rw [← he.integral_comp e.toHomeomorph.measurableEmbedding G]
      congr 1; funext X; exact (hFG X).symm

    obtain ⟨Cg, hCg⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
    obtain ⟨R, hR⟩ := ((hgc.image continuous_snd).isBounded).subset_closedBall (0 : ℝ)
    set SYg := (fun q : ((Fin 2 → NumberField.mixedEmbedding.mixedSpace K) ×
        (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsReal})} → ℝ) ×
          ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ))) × ℝ => q.1.2) '' tsupport g with hSYg
    have hSYgc : IsCompact SYg := hgc.image (continuous_snd.comp continuous_fst)
    have hgz : ∀ (y) (s : ℝ), ((P, y), s) ∉ tsupport g → g ((P, y), s) = 0 := fun y s h => image_eq_zero_of_notMem_tsupport h
    have hsupp : ∀ (y) (s : ℝ), g ((P, y), s) ≠ 0 → s ∈ Set.Icc (-R) R ∧ y ∈ SYg := by
      intro y s hne
      have hmem : ((P, y), s) ∈ tsupport g := by
        by_contra h; exact hne (hgz y s h)
      refine ⟨?_, ⟨_, hmem, rfl⟩⟩
      have : s ∈ Metric.closedBall (0 : ℝ) R := hR ⟨_, hmem, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at this
      exact ⟨this.1, this.2⟩
    set Bnd : ℝ → ℝ := fun s => |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)| with hBnd
    have hBnd0 : ∀ s, 0 ≤ Bnd s := fun s => (abs_nonneg _).trans (MLPR.abs_log_sq_add_sq_le s ρ)
    have hInt : Integrable G ((volume : Measure ℝ).prod volume) := by
      have hb1' : IntegrableOn (fun s => Cg * Bnd s) (Set.Icc (-R) R) (volume : Measure ℝ) :=
        (MLPR.integrableOn_logBound' R ρ).const_mul Cg
      have hb1 : Integrable ((Set.Icc (-R) R).indicator fun s => Cg * Bnd s) (volume : Measure ℝ) :=
        hb1'.integrable_indicator measurableSet_Icc
      have hb2 : Integrable (SYg.indicator fun _ => (1 : ℝ)) (volume : Measure _) :=
        (integrableOn_const (hs := hSYgc.measure_lt_top.ne)).integrable_indicator hSYgc.isClosed.measurableSet
      refine (hb1.mul_prod hb2).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
      · refine ((hg.continuous.comp ?_).aestronglyMeasurable).mul ?_
        · exact ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
        · exact (Complex.continuous_ofReal.measurable.comp
            (Real.measurable_log.comp (by fun_prop))).aestronglyMeasurable
      · show ‖g ((P, q.2), q.1) * ((Real.log (q.1 ^ 2 + ρ ^ 2) : ℝ) : ℂ)‖ ≤
          (Set.Icc (-R) R).indicator (fun s => Cg * Bnd s) q.1 * SYg.indicator (fun _ => (1 : ℝ)) q.2
        by_cases hne : g ((P, q.2), q.1) = 0
        · rw [hne, zero_mul, norm_zero]
          exact mul_nonneg (Set.indicator_nonneg (fun s _ => mul_nonneg hCg0 (hBnd0 s)) _)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        · obtain ⟨hs, hy⟩ := hsupp q.2 q.1 hne
          rw [Set.indicator_of_mem hs, Set.indicator_of_mem hy, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hCg _) (MLPR.abs_log_sq_add_sq_le q.1 ρ) (abs_nonneg _) hCg0

    have hS4a : Integrable (fun x : InfiniteAdeleRing K =>
        Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
             NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
             NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) lam := by
      have hcont : Continuous (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) := by
        refine hΨ.continuous.comp (continuous_pi fun i => ?_)
        fin_cases i
        · exact continuous_const
        · exact continuous_const
        · exact hιH.continuous
      have hsupp : HasCompactSupport (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) := by
        refine HasCompactSupport.intro
          ((hΨc.image (continuous_apply 2)).image hιc) fun x hx => ?_
        by_contra h0
        apply hx
        refine ⟨NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x, ⟨_, subset_tsupport _ h0, rfl⟩, ?_⟩
        exact RingEquiv.symm_apply_apply _ x
      exact hcont.integrable_of_hasCompactSupport hsupp

    have hS4b : Integrable (fun x : InfiniteAdeleRing K =>
        Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
             NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
             NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
          ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ)) lam := by
      have hFint : Integrable F (volume : Measure (NumberField.mixedEmbedding.mixedSpace K)) := by
        have h1 : Integrable (G ∘ e) (volume : Measure (NumberField.mixedEmbedding.mixedSpace K)) := by
          rw [he.integrable_comp_emb e.toHomeomorph.measurableEmbedding, MeasureTheory.Measure.volume_eq_prod]
          exact hInt
        exact h1.congr (Filter.Eventually.of_forall fun X => hFG X)
      obtain ⟨c₀, hc₀, hmap⟩ := MLPR.haar_map K lam
      have h2 : Integrable F (Measure.map (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K) lam) := by
        rw [hmap]
        exact hFint.smul_measure (by simp)
      have h3 := (integrable_map_equiv (hιH.homeomorph (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K)).toMeasurableEquiv F).mp h2
      refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
      show F (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x) = _
      simp only [hF, hρ1, hx1, sq_abs]
      ring_nf
    refine ⟨hS4a, hS4b, ?_⟩

    have hD : ∫ q, G q = ∫ y, ∫ s, g ((P, y), s) * ((Real.log (s ^ 2 + ρ ^ 2) : ℝ) : ℂ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, integral_prod_symm G hInt]

    have hE : ∀ y, ∫ s, g ((P, y), s) * ((Real.log (s ^ 2 + ρ ^ 2) : ℝ) : ℂ) =
        A₀ ((P, y), ρ) + ((|ρ| : ℝ) : ℂ) * B₀ ((P, y), ρ) := fun y => hD0 (P, y) ρ
    have hF0 : ∀ y, y ∉ SY → ∫ s, g ((P, y), s) * ((Real.log (s ^ 2 + ρ ^ 2) : ℝ) : ℂ) = 0 := by
      intro y hy
      have hz : ∀ s : ℝ, g ((P, y), s) = 0 := by
        intro s
        rw [hg_def]
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        rw [hSY]
        refine ⟨_, hmem, ?_⟩
        show (e ((![((P, y), s).1.1 0, ((P, y), s).1.1 1, e.symm (((P, y), s).2, ((P, y), s).1.2)] :
          Fin 3 → NumberField.mixedEmbedding.mixedSpace K) 2)).2 = y
        simp
      simp [hz]
    have hG1 : ∫ y, (A₀ ((P, y), ρ) + ((|ρ| : ℝ) : ℂ) * B₀ ((P, y), ρ)) =
        ∫ y, (wY y : ℝ) • (A₀ ((P, y), ρ) + ((|ρ| : ℝ) : ℂ) * B₀ ((P, y), ρ)) := by
      congr 1; funext y
      by_cases hy : y ∈ SY
      · rw [hwY1 y hy, one_smul]
      · rw [← hE y, hF0 y hy, smul_zero]

    have hiA : Integrable (fun y => (wY y : ℝ) • A₀ ((P, y), ρ)) :=
      ((hwY.continuous.smul (hA₀.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)))).integrable_of_hasCompactSupport
        hwYc.smul_right
    have hiB : Integrable (fun y => (wY y : ℝ) • B₀ ((P, y), ρ)) :=
      ((hwY.continuous.smul (hB₀.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)))).integrable_of_hasCompactSupport
        hwYc.smul_right
    have hG2 : ∫ y, (wY y : ℝ) • (A₀ ((P, y), ρ) + ((|ρ| : ℝ) : ℂ) * B₀ ((P, y), ρ)) =
        (∫ y, (wY y : ℝ) • A₀ ((P, y), ρ)) + ((|ρ| : ℝ) : ℂ) * ∫ y, (wY y : ℝ) • B₀ ((P, y), ρ) := by
      rw [← integral_const_mul, ← integral_add hiA (hiB.const_mul _)]
      congr 1; funext y
      rw [smul_add, mul_smul_comm]

    have hL : (∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
        ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
          ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ) ∂lam) = At P + ((|ρ| : ℝ) : ℂ) * Bt P := by
      rw [hA, hB, hD]
      simp_rw [hE]
      rw [hG1, hG2, hAt, hBt]
      ring

    show _ = ((χ P : ℝ) : ℂ) * At P +
      ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
        (((χ P : ℝ) : ℂ) * Bt P)
    by_cases hPS : P ∈ S2
    · rw [hχ1 P hPS, hL, hρ1]; push_cast; ring
    · have hz : ∀ x : InfiniteAdeleRing K,
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] = 0 := by
        intro x
        refine image_eq_zero_of_notMem_tsupport fun hmem => hPS ?_
        rw [hS2]
        exact ⟨_, hmem, by simp [hP]⟩
      have hL0 : At P + ((|ρ| : ℝ) : ℂ) * Bt P = 0 := by
        rw [← hL]
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
        show Ψ _ * _ = (0 : ℂ)
        rw [hz x, zero_mul]
      have : ((χ P : ℝ) : ℂ) * At P + ((|ρ| : ℝ) : ℂ) * (((χ P : ℝ) : ℂ) * Bt P) =
          ((χ P : ℝ) : ℂ) * (At P + ((|ρ| : ℝ) : ℂ) * Bt P) := by ring
      rw [hρ1, this, hL0, mul_zero]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      show Ψ _ * _ = (0 : ℂ)
      rw [hz x, zero_mul]

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal (solution)
