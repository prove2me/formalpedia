-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:06.625318+00:00
-- url     : https://prove2.me/theorems/4b88016b-4e0b-4f55-afea-d598d4a4b239
-- title:
--   Example
-- statement:
--   Definitions and structural lemmas for Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/Example.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_birational_yLine_21d746fbd4e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isArithVar_yLine_74eda57965c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mCoordIdeal_yLine_1445442fc678
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smoothGenericFibreM_yLine_0ebdec44e278
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_yLine_ne_zero_0b6fa5d5751c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitAt_one_e6e6f4cfcb1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_841979791225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_zero_4d4e53901f14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
theorem mem_mcPts_line {z : (Σ _ : Unit, Fin 2) → ℂ} :
    z ∈ mcPts (mCoordIdeal yLine) ↔ ∃ i, z ⟨(), i⟩ ≠ 0 := by
  rw [mCoordIdeal_yLine]
  constructor
  · rintro ⟨h, -⟩
    exact h ()
  · rintro ⟨i, hi⟩
    refine ⟨fun _ => ⟨i, hi⟩, fun f hf => ?_⟩
    rw [Ideal.mem_bot] at hf
    subst hf
    simp
def chartBase (a : Fin 2) : (Σ _ : Unit, Fin 2) → ℂ := fun p => if p.2 = a then 1 else 0
def chartLin (a : Fin 2) : (Fin 1 → ℂ) →L[ℂ] ((Σ _ : Unit, Fin 2) → ℂ) :=
  ContinuousLinearMap.pi fun p => if p.2 = a then 0 else (2 : ℂ) • ContinuousLinearMap.proj 0
theorem chartLin_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartLin a t p = if p.2 = a then 0 else 2 * t 0 := by
  unfold chartLin
  split_ifs <;> simp [*]
def chartMap (a : Fin 2) (t : Fin 1 → ℂ) : (Σ _ : Unit, Fin 2) → ℂ := chartBase a + chartLin a t
theorem chartMap_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartMap a t p = if p.2 = a then 1 else 2 * t 0 := by
  simp only [chartMap, Pi.add_apply, chartBase, chartLin_apply]
  split_ifs <;> simp
theorem other_index (a : Fin 2) : ∃ b : Fin 2, b ≠ a := by
  fin_cases a
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
theorem hasFDerivAt_chartMap (a : Fin 2) (t : Fin 1 → ℂ) :
    HasFDerivAt (chartMap a) (chartLin a) t :=
  (chartLin a).hasFDerivAt.const_add (chartBase a)
def lineChart (a : Fin 2) :
    SncChart (mCoordIdeal yLine) 1 (∅ : Set ((Σ _ : Unit, Fin 2) → ℂ)) where
  γ := chartMap a
  a := 0
  a_le := Nat.zero_le _
  analytic t _ := analyticAt_const.add ((chartLin a).analyticAt t)
  mem t _ := mem_mcPts_line.2 ⟨a, by rw [chartMap_apply, if_pos rfl]; exact one_ne_zero⟩
  immersion t _ v := by
    rintro ⟨c, hc⟩
    rw [(hasFDerivAt_chartMap a t).fderiv] at hc
    obtain ⟨b, hb⟩ := other_index a
    have h1 := congrFun hc ⟨(), a⟩
    have h2 := congrFun hc ⟨(), b⟩
    simp only [torusSmul] at h1 h2
    rw [chartLin_apply, chartMap_apply, if_pos rfl, if_pos rfl, mul_one] at h1
    rw [chartLin_apply, chartMap_apply, if_neg hb, if_neg hb, ← h1, zero_mul] at h2
    funext i
    rw [Subsingleton.elim i 0]
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  injective t _ t' _ c _ h := by
    obtain ⟨b, hb⟩ := other_index a
    have h1 := congrFun h ⟨(), a⟩
    have h2 := congrFun h ⟨(), b⟩
    simp only [torusSmul] at h1 h2
    rw [chartMap_apply, chartMap_apply, if_pos rfl, if_pos rfl, mul_one] at h1
    rw [chartMap_apply, chartMap_apply, if_neg hb, if_neg hb, ← h1, one_mul] at h2
    funext i
    rw [Subsingleton.elim i 0]
    exact mul_left_cancel₀ two_ne_zero h2
  boundary t _ := by simp
theorem lineChart_γ (a : Fin 2) : (lineChart a).γ = chartMap a := rfl
theorem logR_lineChart (a : Fin 2) (t : Fin 1 → ℂ) : (lineChart a).logR t = Real.exp 1 := by
  simp [SncChart.logR, lineChart]
theorem norm_fin_one_le {t : Fin 1 → ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ‖t 0‖ ≤ r) : ‖t‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun i => by rw [Subsingleton.elim i 0]; exact h
theorem lineChart_cover : ∀ z ∈ mcPts (mCoordIdeal yLine), ∃ a, ∃ t : Fin 1 → ℂ,
    ‖t‖ ≤ 1 / 2 ∧ ∃ c : Unit → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((lineChart a).γ t) := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz
  have hcases : ∀ p : Σ _ : Unit, Fin 2, p = ⟨(), 0⟩ ∨ p = ⟨(), 1⟩ := by
    rintro ⟨⟨⟩, j⟩
    fin_cases j <;> simp
  by_cases h : ‖z ⟨(), 1⟩‖ ≤ ‖z ⟨(), 0⟩‖
  · have h0 : z ⟨(), 0⟩ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      have h1 : z ⟨(), 1⟩ = 0 := norm_le_zero_iff.mp h
      rcases hcases ⟨(), i⟩ with hp | hp <;> rw [hp] at hi
      · exact hi h0
      · exact hi h1
    refine ⟨0, fun _ => z ⟨(), 1⟩ / (2 * z ⟨(), 0⟩), norm_fin_one_le (by norm_num) ?_,
      fun _ => z ⟨(), 0⟩, fun _ => h0, ?_⟩
    · rw [norm_div, norm_mul, Complex.norm_two, div_le_iff₀ (by positivity)]
      linarith
    · funext p
      rcases hcases p with rfl | rfl
      · simp [torusSmul, lineChart, chartMap_apply]
      · simp only [torusSmul, lineChart, chartMap_apply]
        simp
        try field_simp
  · push Not at h
    have h1 : z ⟨(), 1⟩ ≠ 0 := fun h1 => by
      rw [h1, norm_zero] at h
      exact absurd h (not_lt.mpr (norm_nonneg _))
    refine ⟨1, fun _ => z ⟨(), 0⟩ / (2 * z ⟨(), 1⟩), norm_fin_one_le (by norm_num) ?_,
      fun _ => z ⟨(), 1⟩, fun _ => h1, ?_⟩
    · rw [norm_div, norm_mul, Complex.norm_two, div_le_iff₀ (by positivity)]
      linarith
    · funext p
      rcases hcases p with rfl | rfl
      · simp only [torusSmul, lineChart, chartMap_apply]
        simp
        try field_simp
      · simp [torusSmul, lineChart, chartMap_apply]
theorem segreCoord_line_ne_zero (l : Fin 2) : segreCoord yLine (fun _ : Unit => l) ≠ 0 := by
  simp only [segreCoord, Fintype.prod_unique]
  exact yLine_ne_zero _
theorem inFrameDomain_line {l : Fin 2} {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l⟩ ≠ 0) :
    InFrameDomain yLine (fun _ : Unit => l) 1 z :=
  ⟨fun _ => hz, isUnitAt_one _ _⟩
def lineMetric : HermMetric yLine (trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart where
  m := 2
  chart l := fun _ => l
  fr _ := 1
  b _ := Pi.basisFun Ω (Fin 2)
  isFrame l := ⟨segreCoord_line_ne_zero l, one_mem _, one_ne_zero,
    (Pi.basisFun Ω (Fin 2)).linearIndependent, trivial_frame_iff _ 2 _⟩
  gram _ _ := 1
  cover z hz := by
    obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz.1
    exact ⟨i, inFrameDomain_line hi⟩
  posDef _ _ _ _ := Matrix.PosDef.one
  compat l l' z hz _ _ S hS Sz hSz := by
    have hS1 : S = 1 := by
      funext r q
      have h := congrFun (hS q) r
      simp only [Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      rw [Matrix.one_apply]
      exact h.symm
    have hSz1 : Sz = 1 := by
      ext p q
      have h := hSz p q
      rw [hS1] at h
      by_cases hpq : p = q
      · subst hpq
        rw [Matrix.one_apply_eq] at h ⊢
        exact isValueAt_one hz.1 h
      · rw [Matrix.one_apply_ne hpq] at h ⊢
        exact isValueAt_zero hz.1 h
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) = Szᴴ * 1 * Sz
    rw [hSz1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_mul]
  torus _ _ _ _ _ _ := rfl
  conj _ _ _ _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  smooth _ _ _ _ _ _ _ _ := contDiffAt_const
  logBound a t₀ _ := by
    refine ⟨a, inFrameDomain_line (by rw [lineChart_γ, chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, 1, one_pos, 1, one_pos, fun t _ _ _ _ => ⟨?_, ?_, ?_⟩⟩
    · rw [inv_one, Complex.ofReal_one, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
    · rw [logR_lineChart, inv_one, one_mul]
      have : ((Real.exp 1 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1 =
          ((Real.exp 1 - 1 : ℝ) : ℂ) • 1 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [this]
      refine Matrix.PosSemidef.one.smul ?_
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (Real.one_le_exp (by norm_num)))
    · intro p q
      show ‖fderiv ℝ (fun _ : Fin 1 → ℂ => (1 : Matrix (Fin 2) (Fin 2) ℂ) p q) t‖ ≤ _
      rw [fderiv_const_apply, norm_zero]
      positivity
theorem isPositiveRel_fsLine : IsPositiveRel (mCoordIdeal yLine) (fsLine 2) := by
  refine ⟨Inter.isSmoothHerm_fsLine 2, fun z hz w _ hw => ?_⟩
  have hf : (fun z => Real.log ((fsLine 2).h z)) = FubiniLevi.phi := funext FubiniLevi.log_fsLine
  rw [hf]
  exact FubiniLevi.levi_phi_pos (mem_mcPts_line.1 hz) fun c h => hw (fun _ => c) h
theorem isConjInvariantH_fsLine : IsConjInvariantH (fsLine 2) := by
  intro z
  simp [fsLine, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]
def lineData (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    ComponentData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) where
  N := 2
  j := 1
  two_le_N := le_rfl
  one_le_j := le_rfl
  j_le := by norm_num
  F' := ⊥
  finiteDimensional := inferInstance
  const := (algebraMap ℚ Ω).comp (IntermediateField.botEquiv ℚ ℂ).toRingEquiv.toRingHom
  y := yLine
  const_mem _ _ _ := Subalgebra.algebraMap_mem _ _
  arith := isArithVar_yLine
  birational := birational_yLine
  smoothGeneric := smoothGenericFibreM_yLine
  Bd := ∅
  bd_subset := Set.empty_subset _
  bd_closed := by rw [Set.preimage_empty]; exact isClosed_empty
  bd_torus _ h := absurd h (Set.notMem_empty _)
  bd_conj _ h := absurd h (Set.notMem_empty _)
  nCharts := 2
  chart := lineChart
  chart_cover := lineChart_cover
  W _ := trivialBundle (segreCoord yLine) 2
  h _ := lineMetric
  S := ∅
  S_prime _ h := absurd h (Finset.notMem_empty _)
  vdeg _ := 0
  vnum _ := 0
  vden _ := 0
  vertical _ h := absurd h (Finset.notMem_empty _)
  a' := 1
  a'_pos _ := one_pos
  A' := fsLine 2
  A'_deg := rfl
  A'_pos := isPositiveRel_fsLine
  A'_conj := isConjInvariantH_fsLine
  KA := 0
  heights W hW _ := by simpa using hII W hW
def zeroSystem : IntersectionSystem := fun _ _ _ _ _ _ _ => 0
def lineDataZero : ComponentData zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  lineData zeroSystem fun _ _ => le_rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line


