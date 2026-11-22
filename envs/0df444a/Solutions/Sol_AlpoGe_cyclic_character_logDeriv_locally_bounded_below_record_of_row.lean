-- Prove2me | solution 1 for AlpoGe.cyclic_character_logDeriv_locally_bounded_below_record_of_row
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:18:52.464947+00:00
-- url     : https://prove2.me/submissions/ec3fed44-ec86-4fa3-af42-39ffc91ec007
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlpoGeB008
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Theorems.Thm_AlpoGe_cyclic_character_logDeriv_real_bounded_frequently_from_right_of_row

open Filter Set
open scoped Topology Classical
set_option autoImplicit false

theorem solution
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ (0.8749570698 : ℝ) →
        ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] s,
          ‖logDeriv (fun w => ∏ η ∈ Finset.univ.filter (· ∈ Subgroup.zpowers χ),
            DirichletCharacter.LFunction η w) z‖ ≤ C := by
  classical
  intro N _ χ hχ s hs hcap
  let X : Finset (DirichletCharacter ℂ N) :=
    Finset.univ.filter (· ∈ Subgroup.zpowers χ)
  let F (z : ℂ) := ∏ η ∈ X, DirichletCharacter.LFunction η z
  have hLt : s.re < 1 := hcap.trans_lt (by norm_num)
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hLt
  have hFactors (η : DirichletCharacter ℂ N) :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction η) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (η.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hProduct (A : Finset (DirichletCharacter ℂ N)) (z : ℂ)
      (hz : z ∈ ({1}ᶜ : Set ℂ)) :
      AnalyticAt ℂ (fun w => ∏ η ∈ A, DirichletCharacter.LFunction η w) z := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (analyticAt_const :
        AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
    | @insert η A hη ih =>
      simpa only [Finset.prod_insert hη, Pi.mul_def] using (hFactors η z hz).mul ih
  have hAnalytic : AnalyticOnNhd ℂ F ({1}ᶜ : Set ℂ) := hProduct X
  have h2 : F 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun η _ =>
      η.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num)
  have hConnected : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hAt2 : analyticOrderAt F 2 = 0 :=
    (hAnalytic 2 h2mem).analyticOrderAt_eq_zero.mpr h2
  have hFinite : analyticOrderAt F s ≠ ⊤ :=
    hAnalytic.analyticOrderAt_ne_top_of_isPreconnected hConnected.isPreconnected h2mem hs1
      (by rw [hAt2]; exact ENat.zero_ne_top)
  have hAtS : AnalyticAt ℂ F s := hAnalytic s hs1
  have hNonzero : F s ≠ 0 := by
    intro hZero
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hFinite
    have hmNe : m ≠ 0 := by
      intro hz
      apply hAtS.analyticOrderAt_ne_zero.mpr hZero
      simpa [hz] using hm.symm
    obtain ⟨g, hg, hg0, hEq⟩ := hAtS.analyticOrderAt_eq_natCast.mp hm.symm
    have hFact : F =ᶠ[𝓝 s] (fun z => (z - s) ^ m * g z) := by
      simpa only [Filter.EventuallyEq, smul_eq_mul] using hEq
    have hGC : ContinuousAt (logDeriv g) s :=
      hg.deriv.continuousAt.div hg.continuousAt hg0
    let path (y : ℝ) := s + (y : ℂ)
    have hPath : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 s) :=
      (by
        simpa only [path, Complex.ofReal_zero, add_zero] using
          (show Continuous (fun y : ℝ => s + (y : ℂ)) by fun_prop).tendsto 0 :
         Tendsto path (𝓝 (0 : ℝ)) (𝓝 s)).mono_left nhdsWithin_le_nhds
    have hPos : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), 0 < y := self_mem_nhdsWithin
    have hLd :
        ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), logDeriv F (path y) =
          (m : ℂ) / (y : ℂ) + logDeriv g (path y) := by
      filter_upwards [hPath.eventually (logDeriv_congr_nhds hFact),
        hPath.eventually hg.eventually_analyticAt,
        hPath.eventually (hg.continuousAt.eventually_ne hg0), hPos]
        with y hy hgAn hgNe hyPos
      have hyPath : path y - s = (y : ℂ) := by dsimp [path]; ring
      have hyNe : path y - s ≠ 0 := by rw [hyPath]; exact Complex.ofReal_ne_zero.mpr hyPos.ne'
      rw [hy, logDeriv_mul (f := fun z : ℂ => (z - s) ^ m) (path y)
          (pow_ne_zero m hyNe) hgNe (by fun_prop) hgAn.differentiableAt,
        logDeriv_fun_pow (by fun_prop), logDeriv_apply, deriv_sub_const, deriv_id'',
        hyPath, mul_one_div]
    have hY : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have hRemainder : Tendsto (fun y : ℝ => y * (logDeriv g (path y)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_mul, Function.comp_apply] using
        hY.mul ((Complex.continuous_re.tendsto _).comp (hGC.tendsto.comp hPath))
    have hScaled : Tendsto (fun y : ℝ => y * (logDeriv F (path y)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (m : ℝ)) := by
      have hT : Tendsto (fun y : ℝ => (m : ℝ) + y * (logDeriv g (path y)).re)
          (𝓝[>] (0 : ℝ)) (𝓝 (m : ℝ)) :=
        by simpa only [add_zero] using tendsto_const_nhds.add hRemainder
      apply hT.congr'
      filter_upwards [hLd, hPos] with y hy hyPos
      rw [hy, Complex.add_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re,
        mul_add]
      have hCancel : y * ((m : ℝ) / y) = m := by field_simp [hyPos.ne']
      rw [hCancel]
    obtain ⟨C, hC⟩ := AlpoGe.cyclic_character_logDeriv_real_bounded_frequently_from_right_of_row
      H N χ hχ s hs hcap
    have hmPos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hmNe
    have hLarge : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), (m : ℝ) / 2 < y * (logDeriv F (path y)).re :=
      hScaled.eventually (Ioi_mem_nhds (half_lt_self hmPos))
    have hSmall : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y * (|C| + 1) < (m : ℝ) / 2 := by
      have hT := hY.mul tendsto_const_nhds (f := fun y : ℝ => y) (g := fun _ : ℝ => |C| + 1)
      rw [zero_mul] at hT
      exact hT.eventually (Iio_mem_nhds (half_pos hmPos))
    have hNot : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), ¬ (logDeriv F (path y)).re ≤ C := by
      filter_upwards [hLarge, hSmall, hPos] with y hL hS hy hBad
      have hB := mul_le_mul_of_nonneg_left (hBad.trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))) hy.le
      linarith
    exact hC hNot
  have hCont : ContinuousAt (fun z => ‖logDeriv F z‖) s :=
    (hAtS.deriv.continuousAt.div hAtS.continuousAt hNonzero).norm
  refine ⟨‖logDeriv F s‖ + 1, ?_⟩
  exact nhdsWithin_le_nhds
    ((hCont.tendsto.eventually (Iio_mem_nhds (by linarith))).mono fun _ h => h.le)
