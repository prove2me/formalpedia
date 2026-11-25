-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:14:51.560084+00:00
-- url     : https://prove2.me/theorems/1f1c1ff8-2740-4450-8236-b4af9b0a0fc8
-- title:
--   Continuous On Sec
-- statement:
--   Definitions and structural lemmas for Continuous On Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContinuousOnSec.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_log_sum_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_eq_leviV
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
def eFl {n : ℕ} (De : MvPolynomial (Fin n) ℂ) (v : V n) : ℝ :=
  ((De.totalDegree : ℝ) + 1) * Real.log (1 + ‖v‖ ^ 2) -
    Real.log (‖MvPolynomial.eval (fun k => v k) De‖ ^ 2)
theorem contDiff_coordV {n : ℕ} {m : WithTop ℕ∞} (k : Fin n) :
    ContDiff ℂ m (fun v : V n => v k) :=
  (EuclideanSpace.proj k : V n →L[ℂ] ℂ).contDiff
theorem contDiff_evalV {n : ℕ} {m : WithTop ℕ∞} (p : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ m (fun v : V n => MvPolynomial.eval (fun k => v k) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p k hp => simpa using hp.mul (contDiff_coordV k)
theorem norm_evalV_le {n : ℕ} (p : MvPolynomial (Fin n) ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V n,
    ‖MvPolynomial.eval (fun k => v k) p‖ ≤ C * (1 + ‖v‖) ^ p.totalDegree := by
  refine ⟨∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun v => ?_⟩
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  have h1 : 1 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  calc ∏ i ∈ m.support, ‖v i ^ m i‖ ≤ ∏ i ∈ m.support, (1 + ‖v‖) ^ m i :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((PiLp.norm_apply_le v i).trans (by linarith)) _
    _ = (1 + ‖v‖) ^ ∑ i ∈ m.support, m i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + ‖v‖) ^ p.totalDegree := pow_le_pow_right₀ h1 (MvPolynomial.le_totalDegree hm)
theorem sq_evalV_le {n : ℕ} (p : MvPolynomial (Fin n) ℂ) : ∃ C : ℝ, ∀ v : V n,
    ‖MvPolynomial.eval (fun k => v k) p‖ ^ 2 ≤ C * (1 + ‖v‖ ^ 2) ^ p.totalDegree := by
  obtain ⟨C, hC, h⟩ := norm_evalV_le p
  refine ⟨C ^ 2 * 2 ^ p.totalDegree, fun v => ?_⟩
  have h2 : (1 + ‖v‖) ^ 2 ≤ 2 * (1 + ‖v‖ ^ 2) := by nlinarith [sq_nonneg (‖v‖ - 1)]
  calc ‖MvPolynomial.eval (fun k => v k) p‖ ^ 2 ≤ (C * (1 + ‖v‖) ^ p.totalDegree) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h v) 2
    _ = C ^ 2 * ((1 + ‖v‖) ^ 2) ^ p.totalDegree := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ C ^ 2 * (2 * (1 + ‖v‖ ^ 2)) ^ p.totalDegree := by gcongr
    _ = C ^ 2 * 2 ^ p.totalDegree * (1 + ‖v‖ ^ 2) ^ p.totalDegree := by rw [mul_pow]; ring
theorem isCompact_flatK {n : ℕ} (De : MvPolynomial (Fin n) ℂ) (a : ℝ) :
    IsCompact {v : V n | (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) ≤
      Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2} := by
  obtain ⟨C, hC⟩ := sq_evalV_le De
  have hP : Continuous fun v : V n => MvPolynomial.eval (fun k => v k) De :=
    (contDiff_evalV (m := 0) De).continuous
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le ((continuous_const.add (continuous_norm.pow 2)).pow _)
      (continuous_const.mul (hP.norm.pow 2))) ?_
  refine (Metric.isBounded_closedBall (x := (0 : V n)) (r := Real.exp a * C)).subset
    fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hv' : (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) ≤
      Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2 := hv
  have hr : 0 < (1 + ‖v‖ ^ 2) ^ De.totalDegree := by positivity
  have h3 : (1 + ‖v‖ ^ 2) ^ De.totalDegree * (1 + ‖v‖ ^ 2) ≤
      (1 + ‖v‖ ^ 2) ^ De.totalDegree * (Real.exp a * C) := by
    calc (1 + ‖v‖ ^ 2) ^ De.totalDegree * (1 + ‖v‖ ^ 2)
        = (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) := by ring
      _ ≤ Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2 := hv'
      _ ≤ Real.exp a * (C * (1 + ‖v‖ ^ 2) ^ De.totalDegree) :=
          mul_le_mul_of_nonneg_left (hC v) (Real.exp_pos a).le
      _ = (1 + ‖v‖ ^ 2) ^ De.totalDegree * (Real.exp a * C) := by ring
  have h4 := le_of_mul_le_mul_left h3 hr
  nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
theorem eFl_le_iff {n : ℕ} (De : MvPolynomial (Fin n) ℂ) (a : ℝ) {v : V n}
    (hv : MvPolynomial.eval (fun k => v k) De ≠ 0) :
    eFl De v ≤ a ↔ (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) ≤
      Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2 := by
  have h1 : 0 < 1 + ‖v‖ ^ 2 := by positivity
  have h2 : 0 < ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2 := by
    have := norm_pos_iff.mpr hv
    positivity
  rw [← Real.log_le_log_iff (pow_pos h1 _) (mul_pos (Real.exp_pos a) h2), Real.log_pow,
    Real.log_mul (Real.exp_pos a).ne' h2.ne', Real.log_exp]
  unfold eFl
  push_cast
  constructor <;> intro h <;> linarith
theorem contDiffAt_eFl {n : ℕ} {m : WithTop ℕ∞} (De : MvPolynomial (Fin n) ℂ) {v : V n}
    (hv : MvPolynomial.eval (fun k => v k) De ≠ 0) : ContDiffAt ℝ m (eFl De) v := by
  have hP : ContDiff ℝ m (fun v : V n => MvPolynomial.eval (fun k => v k) De) :=
    (contDiff_evalV De).restrict_scalars ℝ
  have h1 : ContDiffAt ℝ m (fun v : V n => Real.log (1 + ‖v‖ ^ 2)) v :=
    (contDiffAt_const.add (contDiff_norm_sq ℂ).contDiffAt).log (by positivity)
  have h2 : ContDiffAt ℝ m (fun v : V n =>
      Real.log (‖MvPolynomial.eval (fun k => v k) De‖ ^ 2)) v :=
    (((contDiff_norm_sq ℂ).comp hP).contDiffAt).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  exact (contDiffAt_const.mul h1).sub h2
def gFS {n : ℕ} : Fin (n + 1) → V n → ℂ := fun j => Fin.cases (fun _ => 1) (fun k x => x k) j
theorem sum_normSq_gFS {n : ℕ} (x : V n) : ∑ j, Complex.normSq (gFS j x) = 1 + ‖x‖ ^ 2 := by
  rw [Fin.sum_univ_succ, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp [gFS, Complex.normSq_eq_norm_sq]
def uFl {n : ℕ} (De : MvPolynomial (Fin n) ℂ) : Fin (De.totalDegree + 2) → V n → ℝ :=
  fun j => Fin.cases (fun x => Real.log (Complex.normSq ((MvPolynomial.eval (fun k => x k) De)⁻¹)))
    (fun _ x => Real.log (1 + ‖x‖ ^ 2)) j
theorem eFl_eq_sum {n : ℕ} (De : MvPolynomial (Fin n) ℂ) (x : V n) :
    eFl De x = ∑ j, uFl De j x := by
  rw [Fin.sum_univ_succ]
  simp only [uFl, Fin.cases_zero, Fin.cases_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_inv₀, Real.log_inv, Complex.normSq_eq_norm_sq, eFl]
  push_cast
  ring
theorem leviV_eFl_nonneg {n : ℕ} (De : MvPolynomial (Fin n) ℂ) {v : V n}
    (hv : MvPolynomial.eval (fun k => v k) De ≠ 0) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun x => ((eFl De x : ℝ) : ℂ)) v ξ).re := by
  have hPc : ContDiff ℂ 2 (fun x : V n => MvPolynomial.eval (fun k => x k) De) :=
    contDiff_evalV De
  have hg : ∀ j, ContDiffAt ℂ 2 (gFS j) v := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact contDiffAt_const
    · exact (contDiff_coordV k).contDiffAt
  have hinv : ContDiffAt ℂ 2 (fun x : V n => (MvPolynomial.eval (fun k => x k) De)⁻¹) v :=
    hPc.contDiffAt.inv hv
  have hpos0 := Complex.normSq_pos.2 (inv_ne_zero hv)
  have hU1c : ContDiffAt ℝ 2 (fun x : V n => Real.log (1 + ‖x‖ ^ 2)) v :=
    (contDiffAt_const.add (contDiff_norm_sq ℂ).contDiffAt).log (by positivity)
  have hU0c : ContDiffAt ℝ 2 (fun x : V n =>
      Real.log (Complex.normSq ((MvPolynomial.eval (fun k => x k) De)⁻¹))) v :=
    (contDiffAt_normSq_comp hinv).log hpos0.ne'
  have hU1 : 0 ≤ (leviV n (fun x => ((Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ)) v ξ).re := by
    have h := leviV_log_sum_nonneg (u := fun j x => Complex.normSq (gFS j x)) (x := v)
      (fun j => contDiffAt_normSq_comp (hg j)) (fun j => logPshAt_normSq (hg j))
      (by rw [sum_normSq_gFS]; positivity) ξ
    simpa only [sum_normSq_gFS] using h
  have hU0 : 0 ≤ (leviV n (fun x => ((Real.log (Complex.normSq
      ((MvPolynomial.eval (fun k => x k) De)⁻¹)) : ℝ) : ℂ)) v ξ).re := by
    have h := leviV_log_sum_nonneg
      (u := fun (_ : Fin 1) x => Complex.normSq ((MvPolynomial.eval (fun k => x k) De)⁻¹))
      (x := v) (fun _ => contDiffAt_normSq_comp hinv) (fun _ => logPshAt_normSq hinv)
      (by rw [Fin.sum_univ_one]; exact hpos0) ξ
    simpa only [Fin.sum_univ_one] using h
  have hsum : (fun x => ((eFl De x : ℝ) : ℂ)) = fun x => ((∑ j, uFl De j x : ℝ) : ℂ) := by
    funext x
    rw [eFl_eq_sum]
  have hc : ∀ j, ContDiffAt ℝ 2 (uFl De j) v := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [uFl] using hU0c
    · simpa [uFl] using hU1c
  rw [hsum, leviV_ofReal_sum hc, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [uFl] using hU0
  · simpa [uFl] using hU1
theorem flatE_smooth {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    SmoothR n (fun y : A.Mset w0 s De => A.zmap w0 s y) (fun y => A.flatE w0 s De y) := by
  intro e he
  have hc : ContDiffOn ℝ ∞ (fun v => ((eFl De v : ℝ) : ℂ))
      {v : V n | MvPolynomial.eval (fun k => v k) De ≠ 0} := fun v hv =>
    (Complex.ofRealCLM.contDiff.contDiffAt.comp v (contDiffAt_eFl De hv)).contDiffWithinAt
  refine (hc.mono fun v hv => ?_).congr fun v hv => ?_
  · have h1 := chart_z_symm n _ e he v hv
    have h2 : _ ∧ _ := (e.symm v).2
    have h3 := h2.2
    rw [h1] at h3
    exact h3
  · have h1 := chart_z_symm n _ e he v hv
    simp only [Function.comp_apply]
    rw [show A.flatE w0 s De (e.symm v) = eFl De (A.zmap w0 s (e.symm v)) from rfl, h1]
theorem flatE_levi {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    LeviNonneg n (fun y : A.Mset w0 s De => A.zmap w0 s y) (fun y => A.flatE w0 s De y) := by
  intro x ξ
  obtain ⟨e, he, hx⟩ := exists_chart n _ hF.localHomeo x
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  have hmem : A.zmap w0 s x ∈ e.target := by
    have h0 : A.zmap w0 s x = e x := he hx
    rw [h0]
    exact e.map_source hx
  have hev : (fun v => ((A.flatE w0 s De (e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (A.zmap w0 s x)]
      fun v => ((eFl De v : ℝ) : ℂ) := by
    filter_upwards [e.open_target.mem_nhds hmem] with v hv
    have h1 := chart_z_symm n _ e he v hv
    rw [show A.flatE w0 s De (e.symm v) = eFl De (A.zmap w0 s (e.symm v)) from rfl, h1]
  rw [leviV_congr hev]
  have h2 : _ ∧ _ := x.2
  exact leviV_eFl_nonneg De h2.2 ξ
theorem flatE_isCompact {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (a : ℝ) :
    IsCompact {y : A.Mset w0 s De | A.flatE w0 s De y ≤ a} := by
  rw [Subtype.isCompact_iff]
  have hne : ∀ v ∈ {v : V n | (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) ≤
      Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2},
      MvPolynomial.eval (fun k => v k) De ≠ 0 := by
    intro v hv h0
    have hv' : (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) ≤
        Real.exp a * ‖MvPolynomial.eval (fun k => v k) De‖ ^ 2 := hv
    rw [h0, norm_zero] at hv'
    have : 0 < (1 + ‖v‖ ^ 2) ^ (De.totalDegree + 1) := by positivity
    simp at hv'
    linarith
  have hK := hF.proper _ (isCompact_flatK De a) hne
  convert hK using 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h2 : _ ∧ _ := y.2
    exact ⟨y.2, (eFl_le_iff De a h2.2).1 hy⟩
  · rintro ⟨hx, hk⟩
    have h2 : _ ∧ _ := hx
    exact ⟨⟨x, hx⟩, (eFl_le_iff De a h2.2).2 hk, rfl⟩
def flatStein {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    EtaleStein n (A.Mset w0 s De) where
  z := fun y => A.zmap w0 s y
  isLocalHomeomorph := hF.localHomeo
  e := fun y => A.flatE w0 s De y
  smooth_e := flatE_smooth A hD hF
  levi_e := flatE_levi A hD hF
  isCompact_le := flatE_isCompact A hD hF
end
end ReciprocityTheory.L2DbarEstimates.Y


