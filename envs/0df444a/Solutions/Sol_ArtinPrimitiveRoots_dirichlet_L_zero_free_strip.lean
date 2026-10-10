-- Prove2me | solution 1 for ArtinPrimitiveRoots.dirichlet_L_zero_free_strip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T16:37:29.778233+00:00
-- url     : https://prove2.me/submissions/0f220a3b-86f2-461e-9c88-03e21c1b5734

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_L_bound_near_one

section
/-!
# Landau's local formula for the logarithmic derivative

For `f` analytic on a neighbourhood of `closedBall c R` with `f c ≠ 0` and
`‖f z‖ ≤ e^M ‖f c‖` there, the zeros of `f` in `closedBall c (R/4)` number at most `M / log 2`
(with multiplicity), and on `closedBall c (R/16)`
`f'/f(z) = Σ_{ρ} m_ρ/(z-ρ) + O(M/R)` with the explicit constant `32`.

Proof: factor out the zeros in the small disk (`MeromorphicOn.extract_zeros_poles`), apply the
maximum modulus principle to the quotient on `closedBall c (3R/4)`, take a holomorphic logarithm
(a primitive of `G'/G`, Morera on a disk), and finish with Borel–Carathéodory and Cauchy's
estimate.
-/

namespace ArtinPrimitiveRoots.L31Z

open Complex Metric Set Filter Topology

/-- Factor the zeros of `f` lying in `closedBall c r` out of `f` on `ball c R`. -/
theorem factor_zeros {f : ℂ → ℂ} {c : ℂ} {R r : ℝ} (hR : 0 < R) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (G : ℂ → ℂ),
      (∀ u ∈ Z, u ∈ closedBall c r ∧ 0 < m u) ∧
      AnalyticOnNhd ℂ G (closedBall c R) ∧
      (∀ z ∈ closedBall c r, G z ≠ 0) ∧
      (∀ z ∈ ball c R, f =ᶠ[𝓝 z] fun w => (∏ u ∈ Z, (w - u) ^ m u) * G w) := by
  classical
  set U := closedBall c R with hU
  have hmero : MeromorphicOn f U := hf.meromorphicOn
  have hcU : c ∈ U := mem_closedBall_self hR.le
  have hord_c : meromorphicOrderAt f c ≠ ⊤ := by
    rw [(hf c hcU).meromorphicOrderAt_eq, ((hf c hcU).analyticOrderAt_eq_zero).mpr hfc]
    simp
  have hord : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := fun u =>
    hmero.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      hcU u.2 hord_c
  have hfin : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hmero.extract_zeros_poles hord hfin
  set D := MeromorphicOn.divisor f U with hD
  have hD0 : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
  set S := hfin.toFinset with hS
  set m : ℂ → ℕ := fun u => (D u).toNat with hm
  set Zin := S.filter (fun u => u ∈ closedBall c r) with hZin
  set Zout := S.filter (fun u => u ∉ closedBall c r) with hZout
  set G : ℂ → ℂ := fun z => (∏ u ∈ Zout, (z - u) ^ m u) * g z with hG
  have hprod : ∀ x, (∏ᶠ u, (fun x => x - u) ^ D u) x =
      (∏ u ∈ Zin, (x - u) ^ m u) * ∏ u ∈ Zout, (x - u) ^ m u := by
    intro x
    rw [Function.FactorizedRational.finprod_eq_fun hfin]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [Finset.prod_filter_mul_prod_filter_not]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hD0 u)]
    · intro u hu
      simp only [Function.mem_mulSupport] at hu
      rw [Finset.mem_coe, hS, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      apply hu
      rw [h0, zpow_zero]
  have hpoly : ∀ (T : Finset ℂ), Differentiable ℂ (fun w => ∏ u ∈ T, (w - u) ^ m u) := by
    intro T
    fun_prop
  refine ⟨Zin, m, G, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [hZin, Finset.mem_filter, hS, Set.Finite.mem_toFinset, Function.mem_support] at hu
    refine ⟨hu.2, ?_⟩
    have := hD0 u
    simp only [hm]
    omega
  · intro z hz
    exact ((hpoly Zout).analyticAt z).mul (hg_an z hz)
  · intro z hz
    refine mul_ne_zero ?_ (hg_ne ⟨z, closedBall_subset_closedBall hrR hz⟩)
    rw [Finset.prod_ne_zero_iff]
    intro u hu
    rw [hZout, Finset.mem_filter] at hu
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    rintro rfl
    exact hu.2 hz
  · intro z hz
    have hzU : z ∈ U := ball_subset_closedBall hz
    have hcont1 : ContinuousAt f z := (hf z hzU).continuousAt
    have hcont2 : ContinuousAt (fun w => (∏ u ∈ Zin, (w - u) ^ m u) * G w) z :=
      (((hpoly Zin).analyticAt z).mul (((hpoly Zout).analyticAt z).mul (hg_an z hzU))).continuousAt
    rw [← hcont1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont2]
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg_eq) z hzU
    have h2 : U ∈ 𝓝[≠] z :=
      mem_nhdsWithin_of_mem_nhds (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
    filter_upwards [h1, h2] with w hw1 hw2
    rcases hw1 with hw1 | hw1
    · rw [Set.mem_ofPred_eq] at hw1
      rw [hw1, Pi.smul_apply', smul_eq_mul, hprod, hG]
      ring
    · exact absurd hw2 hw1

/-- **Landau's lemma** (local formula for `f'/f`), with explicit constants. -/
theorem landau_logDeriv {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c R, ‖f z‖ ≤ Real.exp M * ‖f c‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ u ∈ Z, u ∈ closedBall c (R / 4) ∧ 0 < m u ∧ f u = 0) ∧
      (∀ u ∈ closedBall c (R / 4), f u = 0 → u ∈ Z) ∧
      ((∑ u ∈ Z, m u : ℕ) : ℝ) * Real.log 2 ≤ M ∧
      ∀ z ∈ closedBall c (R / 16), f z ≠ 0 →
        ‖deriv f z / f z - ∑ u ∈ Z, (m u : ℂ) / (z - u)‖ ≤ 32 * M / R := by
  obtain ⟨Z, m, G, hZ, hG_an, hG_ne, hfeq⟩ :=
    factor_zeros (r := R / 4) hR (by linarith) hf hfc
  set P : ℂ → ℂ := fun w => ∏ u ∈ Z, (w - u) ^ m u with hP
  have hPdiff : Differentiable ℂ P := by rw [hP]; fun_prop
  have hfpt : ∀ z ∈ ball c R, f z = P z * G z := fun z hz => (hfeq z hz).eq_of_nhds
  have hR4 : ∀ z ∈ closedBall c (R / 4), z ∈ ball c R := fun z hz =>
    closedBall_subset_ball (by linarith) hz
  have hPc : P c ≠ 0 := fun h => hfc (by rw [hfpt c (mem_ball_self hR), h, zero_mul])
  have hGc : G c ≠ 0 := hG_ne c (mem_closedBall_self (by linarith))
  have hGdiff : DifferentiableOn ℂ G (closedBall c R) := hG_an.differentiableOn
  set N := ∑ u ∈ Z, m u with hN
  -- on the circle of radius `3R/4`, every factor of `P` is at least twice its value at `c`
  have hPsphere : ∀ z ∈ sphere c (3 * R / 4), (2:ℝ) ^ N * ‖P c‖ ≤ ‖P z‖ := by
    intro z hz
    simp only [hP, norm_prod, norm_pow, hN]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun u hu => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hu' : dist u c ≤ R / 4 := (hZ u hu).1
    have hz' : dist z c = 3 * R / 4 := hz
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm c u]
    linarith [dist_triangle z u c]
  -- maximum modulus for `G` on `closedBall c (3R/4)`
  have hGmax : ∀ z ∈ closedBall c (3 * R / 4), (2:ℝ) ^ N * ‖G z‖ ≤ Real.exp M * ‖G c‖ := by
    intro z hz
    have h2N : (0:ℝ) < 2 ^ N := by positivity
    rw [← le_div_iff₀' h2N]
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c (3 * R / 4))
      isBounded_ball (hGdiff.diffContOnCl_ball (closedBall_subset_closedBall (by linarith))) ?_ ?_
    · intro w hw
      rw [frontier_ball c (by positivity)] at hw
      have hwb : w ∈ ball c R := by
        rw [mem_sphere] at hw
        rw [mem_ball]
        linarith
      have hPw := hPsphere w hw
      have hPc' : 0 < ‖P c‖ := norm_pos_iff.mpr hPc
      have hfw := hbd w (ball_subset_closedBall hwb)
      rw [hfpt w hwb, norm_mul, hfpt c (mem_ball_self hR), norm_mul] at hfw
      rw [le_div_iff₀' h2N]
      have : (2 ^ N * ‖G w‖) * ‖P c‖ ≤ (Real.exp M * ‖G c‖) * ‖P c‖ := by
        calc (2 ^ N * ‖G w‖) * ‖P c‖ = (2 ^ N * ‖P c‖) * ‖G w‖ := by ring
          _ ≤ ‖P w‖ * ‖G w‖ := by gcongr
          _ ≤ Real.exp M * (‖P c‖ * ‖G c‖) := hfw
          _ = (Real.exp M * ‖G c‖) * ‖P c‖ := by ring
      exact le_of_mul_le_mul_right this hPc'
    · rw [closure_ball c (by positivity)]
      exact hz
  have hcount : (N : ℝ) * Real.log 2 ≤ M := by
    have h := hGmax c (mem_closedBall_self (by linarith))
    have hGc' : 0 < ‖G c‖ := norm_pos_iff.mpr hGc
    have h2 : (2:ℝ) ^ N ≤ Real.exp M := le_of_mul_le_mul_right h hGc'
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow, Real.log_exp] at this
  have hGbd : ∀ z ∈ closedBall c (3 * R / 4), ‖G z‖ ≤ Real.exp M * ‖G c‖ := by
    intro z hz
    have h1 : (1:ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have := hGmax z hz
    nlinarith [norm_nonneg (G z)]
  -- a holomorphic logarithm of `G` on `ball c (R/4)`
  set B := ball c (R / 4) with hB
  have hBR : ∀ z ∈ B, z ∈ closedBall c R := fun z hz =>
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)
  have hGne_B : ∀ z ∈ B, G z ≠ 0 := fun z hz => hG_ne z (ball_subset_closedBall hz)
  have hφ : DifferentiableOn ℂ (fun z => deriv G z / G z) B :=
    (hG_an.deriv.differentiableOn.mono hBR).div (hGdiff.mono hBR) hGne_B
  obtain ⟨H, hH⟩ := hφ.isExactOn_ball
  have hHdiff : DifferentiableOn ℂ H B := fun z hz =>
    (hH z hz).differentiableAt.differentiableWithinAt
  have hK : ∀ z ∈ B, G z * Complex.exp (-H z) = G c * Complex.exp (-H c) := by
    intro z hz
    have hderiv : ∀ w ∈ B, HasDerivAt (fun w => G w * Complex.exp (-H w)) 0 w := by
      intro w hw
      have hGw : HasDerivAt G (deriv G w) w := (hG_an w (hBR w hw)).differentiableAt.hasDerivAt
      have hEw : HasDerivAt (fun w => Complex.exp (-H w))
          (Complex.exp (-H w) * (-(deriv G w / G w))) w := (hH w hw).neg.cexp
      have hGw0 := hGne_B w hw
      refine (hGw.mul hEw).congr_deriv ?_
      field_simp
      ring
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c _).isPreconnected
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hderiv w hw).deriv) hz (mem_ball_self (by linarith))
  have hHre : ∀ z ∈ B, (H z - H c).re ≤ M := by
    intro z hz
    have hGz : G z = G c * Complex.exp (H z - H c) := by
      calc G z = G z * Complex.exp (-H z) * Complex.exp (H z) := by
            rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
        _ = G c * Complex.exp (-H c) * Complex.exp (H z) := by rw [hK z hz]
        _ = G c * Complex.exp (H z - H c) := by
            rw [mul_assoc, ← Complex.exp_add, neg_add_eq_sub]
    have hbound := hGbd z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))
    rw [hGz, norm_mul, Complex.norm_exp] at hbound
    have hGc' : 0 < ‖G c‖ := norm_pos_iff.mpr hGc
    have : Real.exp (H z - H c).re ≤ Real.exp M := by
      have h' : ‖G c‖ * Real.exp (H z - H c).re ≤ ‖G c‖ * Real.exp M := by linarith
      exact le_of_mul_le_mul_left h' hGc'
    exact Real.exp_le_exp.mp this
  -- Borel–Carathéodory
  have hBC : ∀ w ∈ closedBall c (R / 8), ‖H w - H c‖ ≤ 2 * M := by
    intro w hw
    have hmemB : ∀ ζ ∈ ball (0:ℂ) (R / 4), c + ζ ∈ B := by
      intro ζ hζ
      rw [mem_ball_zero_iff] at hζ
      rw [hB, mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hζ
    have hdiff0 : DifferentiableOn ℂ (fun ζ => H (c + ζ) - H c) (ball 0 (R / 4)) := by
      intro ζ hζ
      have h1 : DifferentiableAt ℂ (fun ζ => H (c + ζ)) ζ :=
        (hH _ (hmemB ζ hζ)).differentiableAt.comp ζ (differentiableAt_id.const_add c)
      exact (h1.sub_const _).differentiableWithinAt
    have hmaps : MapsTo (fun ζ => H (c + ζ) - H c) (ball 0 (R / 4)) {z | z.re ≤ M} :=
      fun ζ hζ => hHre (c + ζ) (hmemB ζ hζ)
    have hnorm : ‖w - c‖ ≤ R / 8 := by rw [← dist_eq_norm]; exact hw
    have hwζ : w - c ∈ ball (0:ℂ) (R / 4) := by
      rw [mem_ball_zero_iff]; linarith
    have h := Complex.borelCaratheodory_zero hM hdiff0 hmaps (by linarith) hwζ (by simp)
    simp only [add_sub_cancel] at h
    calc ‖H w - H c‖ ≤ 2 * M * ‖w - c‖ / (R / 4 - ‖w - c‖) := h
      _ ≤ 2 * M := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hM.le (by linarith : (0:ℝ) ≤ R / 4 - 2 * ‖w - c‖)]
  -- Cauchy's estimate
  have hGlog : ∀ z ∈ closedBall c (R / 16), ‖deriv G z / G z‖ ≤ 32 * M / R := by
    intro z hz
    have hz' : dist z c ≤ R / 16 := hz
    have hzB : z ∈ B := by rw [hB, mem_ball]; linarith
    have hsub : closedBall z (R / 16) ⊆ B := by
      intro ζ hζ
      have : dist ζ z ≤ R / 16 := hζ
      rw [hB, mem_ball]
      linarith [dist_triangle ζ z c]
    have hDiff : DifferentiableOn ℂ (fun ζ => H ζ - H c) B := hHdiff.sub_const _
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : (0:ℝ) < R / 16)
      (hDiff.diffContOnCl_ball hsub) (C := 2 * M) (fun ζ hζ => by
        refine hBC ζ ?_
        have : dist ζ z = R / 16 := hζ
        show dist ζ c ≤ R / 8
        linarith [dist_triangle ζ z c])
    rw [deriv_sub_const, (hH z hzB).deriv] at h
    calc _ ≤ 2 * M / (R / 16) := h
      _ = 32 * M / R := by field_simp; ring
  -- the formula
  have hlogf : ∀ z ∈ closedBall c (R / 16), f z ≠ 0 →
      deriv f z / f z - ∑ u ∈ Z, (m u : ℂ) / (z - u) = deriv G z / G z := by
    intro z hz hfz
    have hz' : dist z c ≤ R / 16 := hz
    have hzR : z ∈ ball c R := by rw [mem_ball]; linarith
    have hzG : z ∈ closedBall c (R / 4) := by
      show dist z c ≤ R / 4
      linarith
    have hPz : P z ≠ 0 := fun h => hfz (by rw [hfpt z hzR, h, zero_mul])
    have hGz : G z ≠ 0 := hG_ne z hzG
    have h1 : deriv f z / f z = logDeriv (fun w => P w * G w) z := by
      rw [← logDeriv_apply, (logDeriv_congr_nhds (hfeq z hzR)).eq_of_nhds]
    have hPz' := Finset.prod_ne_zero_iff.mp hPz
    have h2 : logDeriv P z = ∑ u ∈ Z, (m u : ℂ) / (z - u) := by
      rw [hP, logDeriv_prod (f := fun u w => (w - u) ^ m u)]
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [logDeriv_fun_pow (f := fun w => w - u) (by fun_prop), logDeriv_apply,
          deriv_sub_const, deriv_id'']
        ring
      · exact hPz'
      · intro u _
        fun_prop
    rw [h1, logDeriv_mul z hPz hGz (hPdiff z) (hG_an z (hBR z (by
      rw [hB, mem_ball]; linarith))).differentiableAt, h2, logDeriv_apply]
    ring
  refine ⟨Z, m, fun u hu => ⟨(hZ u hu).1, (hZ u hu).2, ?_⟩, ?_, hcount, ?_⟩
  · rw [hfpt u (hR4 u (hZ u hu).1)]
    have : P u = 0 := Finset.prod_eq_zero hu (by rw [sub_self, zero_pow (hZ u hu).2.ne'])
    rw [this, zero_mul]
  · intro u hu hfu
    rw [hfpt u (hR4 u hu)] at hfu
    rcases mul_eq_zero.mp hfu with h | h
    · obtain ⟨v, hv, hv0⟩ := Finset.prod_eq_zero_iff.mp h
      rw [sub_eq_zero.mp (eq_zero_of_pow_eq_zero hv0)]
      exact hv
    · exact absurd h (hG_ne u hu)
  · intro z hz hfz
    rw [hlogf z hz hfz]
    exact hGlog z hz

end ArtinPrimitiveRoots.L31Z
end

section
/-!
# Dirichlet-series facts to the right of `Re s = 1` (L31Z)

* `norm_LFunction_ge`: `‖L(s, χ)‖ ≥ (σ - 1)/σ` for `σ = Re s > 1`;
* `LSeries_vonMangoldt_re_le`: `Σ Λ(n) n^{-σ} ≤ 1/(σ - 1) + C₀` for `1 < σ ≤ 2`;
* `three_four_one`: `0 ≤ 3 Σ Λ(n)n^{-σ} - 4 Re L'/L(σ+iv, χ) - Re L'/L(σ+2iv, χ²)`.
-/

namespace ArtinPrimitiveRoots.L31Z

open Complex LSeries DirichletCharacter ArithmeticFunction

open scoped LSeries.notation ArithmeticFunction.Moebius

/-- `Σ_{n ≥ 1} n^{-σ} ≤ σ/(σ-1)`. -/
lemma tsum_norm_term_one_le {s : ℂ} (hs : 1 < s.re) :
    ∑' n, ‖term 1 s n‖ ≤ s.re / (s.re - 1) := by
  have hsum : Summable (fun n => ‖term 1 s n‖) := (LSeriesSummable_one_iff.mpr hs).norm
  rw [hsum.tsum_eq_zero_add]
  simp only [term_zero, norm_zero, zero_add]
  have h1 : ∀ n : ℕ, ‖term 1 s (n + 1)‖ = 1 / ((n : ℝ) + 1) ^ s.re := by
    intro n
    rw [norm_term_eq]
    simp
  simp_rw [h1]
  have h2 := ZetaAsymptotics.termTSum_of_lt hs
  have h3 : 0 ≤ ZetaAsymptotics.termTSum s.re :=
    tsum_nonneg fun n => ZetaAsymptotics.term_nonneg _ _
  have hσ0 : 0 < s.re := by linarith
  have hσ1 : 0 < s.re - 1 := by linarith
  rw [h2] at h3
  rw [le_div_iff₀ hσ1]
  have h4 : 1 / s.re * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re ≤ 1 / (s.re - 1) := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hσ0 hσ1] at h4
  linarith

/-- An L-series with coefficients of norm `≤ 1` is bounded by `σ/(σ-1)`. -/
lemma norm_LSeries_le_of_norm_le_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ s.re / (s.re - 1) := by
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hle : ∀ n, ‖term f s n‖ ≤ ‖term 1 s n‖ := fun n =>
    norm_term_le s (by simpa using hf n)
  have hf' : Summable fun n => ‖term f s n‖ :=
    h1.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  calc ‖LSeries f s‖ ≤ ∑' n, ‖term f s n‖ := norm_tsum_le_tsum_norm hf'
    _ ≤ ∑' n, ‖term 1 s n‖ := hf'.tsum_le_tsum hle h1.norm
    _ ≤ s.re / (s.re - 1) := tsum_norm_term_one_le hs

/-- Lower bound for `L(s, χ)` to the right of `1`: `‖L(s,χ)‖ ≥ (σ-1)/σ`. -/
lemma norm_LFunction_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  rw [LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hb : ‖LSeries (↗χ * ↗μ) s‖ ≤ s.re / (s.re - 1) := by
    refine norm_LSeries_le_of_norm_le_one (fun n => ?_) hs
    rw [Pi.mul_apply, norm_mul]
    have h1 : ‖(χ n : ℂ)‖ ≤ 1 := χ.norm_le_one n
    have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    calc ‖(χ n : ℂ)‖ * ‖((μ n : ℤ) : ℂ)‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have h1 : ‖LSeries ↗χ s‖ * ‖LSeries (↗χ * ↗μ) s‖ = 1 := by
    rw [← norm_mul, h, norm_one]
  have hσ0 : 0 < s.re := by linarith
  have hσ1 : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ hσ0]
  have h3 : ‖LSeries ↗χ s‖ * ‖LSeries (↗χ * ↗μ) s‖ ≤ ‖LSeries ↗χ s‖ * (s.re / (s.re - 1)) := by
    gcongr
  rw [h1, mul_div_assoc', le_div_iff₀ hσ1, one_mul] at h3
  linarith

/-- `Σ Λ(n) n^{-σ} ≤ 1/(σ-1) + C₀` for `1 < σ ≤ 2`. -/
lemma LSeries_vonMangoldt_re_le : ∃ C₀ : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (LSeries ↗Λ σ).re ≤ 1 / (σ - 1) + C₀ := by
  have hcont := ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux
    (q := 1) (1 : ZMod 1)
  have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' Set.Icc 1 2) :=
    isCompact_Icc.image continuous_ofReal
  have hsub : (fun x : ℝ => (x : ℂ)) '' Set.Icc 1 2 ⊆ {s | 1 ≤ s.re} := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx.1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨C₀, fun σ hσ1 hσ2 => ?_⟩
  have heq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) (a := 1)
    isUnit_one (show (σ : ℂ) ∈ {s : ℂ | 1 < s.re} by simpa using hσ1)
  have hres : (fun n => ((ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n : ℝ) : ℂ))
      = ↗Λ := by
    ext n
    simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 1]
  simp only [hres, Nat.totient_one, Nat.cast_one, inv_one] at heq
  have hb := hC₀ σ ⟨σ, ⟨hσ1.le, hσ2⟩, rfl⟩
  have hL : LSeries ↗Λ σ =
      ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) σ + 1 / (σ - 1) := by
    rw [heq]
    ring
  rw [hL, add_re]
  have h1 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  rw [h1]
  have := (re_le_norm _).trans hb
  linarith

/-- The elementary inequality `3 + 4 Re z + Re z² ≥ 0` for `‖z‖ ≤ 1`, scaled by `a ≥ 0`. -/
lemma re_comb_nonneg {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 * a + 4 * ((a : ℂ) * z).re + ((a : ℂ) * z ^ 2).re := by
  have h1 : ((a : ℂ) * z).re = a * z.re := by simp
  have h2 : ((a : ℂ) * z ^ 2).re = a * (z.re ^ 2 - z.im ^ 2) := by
    simp [sq]
  rw [h1, h2]
  have hz2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have : 0 ≤ 3 + 4 * z.re + (z.re ^ 2 - z.im ^ 2) := by nlinarith
  nlinarith

lemma term_comb_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ v : ℝ) (n : ℕ) :
    0 ≤ 3 * (term ↗Λ σ n).re + 4 * (term (↗χ * ↗Λ) (σ + v * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) (σ + 2 * v * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero]
  rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn]
  set u := (n : ℂ) ^ ((v : ℂ) * I) with hu_def
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have e1 : (n : ℂ) ^ ((σ : ℂ) + v * I) = (n : ℂ) ^ (σ : ℂ) * u := cpow_add _ _ hn'
  have e2 : (n : ℂ) ^ ((σ : ℂ) + 2 * v * I) = (n : ℂ) ^ (σ : ℂ) * u ^ 2 := by
    rw [show (σ : ℂ) + 2 * v * I = σ + ((2 : ℕ) : ℂ) * (v * I) by push_cast; ring,
      cpow_add _ _ hn', cpow_nat_mul]
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have e0 : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [ofReal_cpow (Nat.cast_nonneg n)]
    simp
  have hnσ : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
  set a : ℝ := Λ n / (n : ℝ) ^ σ with ha_def
  set z : ℂ := χ n / u with hz_def
  have hA : (Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ) = (a : ℂ) := by
    rw [e0, ha_def]
    push_cast
    rfl
  have hB : (↗χ * ↗Λ) n / (n : ℂ) ^ ((σ : ℂ) + v * I) = (a : ℂ) * z := by
    rw [e1, e0, ha_def, hz_def, Pi.mul_apply]
    have : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hnσ.ne'
    push_cast
    field_simp
  have hC : (↗(χ ^ 2) * ↗Λ) n / (n : ℂ) ^ ((σ : ℂ) + 2 * v * I) = (a : ℂ) * z ^ 2 := by
    rw [e2, e0, ha_def, hz_def, Pi.mul_apply, MulChar.pow_apply' χ two_ne_zero]
    have : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hnσ.ne'
    push_cast
    field_simp
  rw [hA, hB, hC, ofReal_re]
  have ha : 0 ≤ a := div_nonneg vonMangoldt_nonneg hnσ.le
  have hz : ‖z‖ ≤ 1 := by
    rw [hz_def, norm_div, hu, div_one]
    exact χ.norm_le_one n
  exact re_comb_nonneg ha hz

/-- `-L'/L(s, χ) = Σ χ(n)Λ(n)n^{-s}` for `Re s > 1`. -/
lemma neg_logDeriv_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s) = LSeries (↗χ * ↗Λ) s := by
  rw [LSeries_twist_vonMangoldt_eq χ hs, deriv_LFunction_eq_deriv_LSeries χ hs,
    LFunction_eq_LSeries χ hs, neg_div]

/-- **The 3–4–1 inequality** for logarithmic derivatives. -/
lemma three_four_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (v : ℝ) :
    0 ≤ 3 * (LSeries ↗Λ σ).re
      - 4 * (deriv (LFunction χ) (σ + v * I) / LFunction χ (σ + v * I)).re
      - (deriv (LFunction (χ ^ 2)) (σ + 2 * v * I) / LFunction (χ ^ 2) (σ + 2 * v * I)).re := by
  have hs1 : 1 < ((σ : ℂ) + v * I).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * v * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have e1 := neg_logDeriv_LFunction_eq χ hs1
  have e2 := neg_logDeriv_LFunction_eq (χ ^ 2) hs2
  have hA := (LSeriesSummable_vonMangoldt hs0).LSeriesHasSum
  have hB := (LSeriesSummable_twist_vonMangoldt χ hs1).LSeriesHasSum
  have hC := (LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2).LSeriesHasSum
  have hsum := (((hasSum_re hA).mul_left 3).add ((hasSum_re hB).mul_left 4)).add (hasSum_re hC)
  have h := hsum.nonneg (fun n => term_comb_nonneg χ σ v n)
  have r1 : (deriv (LFunction χ) (σ + v * I) / LFunction χ (σ + v * I)).re =
      -(LSeries (↗χ * ↗Λ) (σ + v * I)).re := by
    rw [← e1, neg_re, neg_neg]
  have r2 : (deriv (LFunction (χ ^ 2)) (σ + 2 * v * I) / LFunction (χ ^ 2) (σ + 2 * v * I)).re =
      -(LSeries (↗(χ ^ 2) * ↗Λ) (σ + 2 * v * I)).re := by
    rw [← e2, neg_re, neg_neg]
  rw [r1, r2]
  linarith

end ArtinPrimitiveRoots.L31Z
end

section
/-!
# [22] Lemmas 3.5–3.6: a zero-free strip and a log-derivative bound (L31Z)

From the bound `‖L(σ+iv, χ)‖ ≤ exp(K T²)` near `Re s = 1` (`dirichlet_L_bound_near_one`), with
`L = log x`, `T = log L`, `r* = T⁴/L`:

* no zero in `Re s ≥ 1 - cT²/L`, `1 ≤ |Im s| ≤ x³` (de la Vallée Poussin: Landau's lemma at
  `σ + iv` for `χ` and at `σ + 2iv` for `χ²`, radius `9r*`, `σ = 1 + 20cT²/L`, and the 3–4–1
  inequality);
* `‖L'/L(s)‖ ≤ K L` for `1 - cT²/(2L) ≤ Re s ≤ 1 + 1/L`, `2 ≤ |Im s| ≤ x³/2` (Landau's lemma at
  `1 + r*/2 + i Im s`; every zero in the sum lies at horizontal distance `≥ cT²/(2L)`).
-/

namespace ArtinPrimitiveRoots.L31Z

open Complex Metric DirichletCharacter

open scoped LSeries.notation

lemma analyticAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : z ≠ 1) : AnalyticAt ℂ (LFunction χ) z := by
  have hd : DifferentiableOn ℂ (LFunction χ) {1}ᶜ := fun w hw =>
    (differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)

lemma mem_closedBall_re_im {c₀ z : ℂ} {R : ℝ} (hz : z ∈ closedBall c₀ R) :
    |z.re - c₀.re| ≤ R ∧ |z.im - c₀.im| ≤ R := by
  have h : ‖z - c₀‖ ≤ R := by rw [← dist_eq_norm]; exact hz
  constructor
  · calc |z.re - c₀.re| = |(z - c₀).re| := by rw [sub_re]
      _ ≤ ‖z - c₀‖ := abs_re_le_norm _
      _ ≤ R := h
  · calc |z.im - c₀.im| = |(z - c₀).im| := by rw [sub_im]
      _ ≤ ‖z - c₀‖ := abs_im_le_norm _
      _ ≤ R := h

/-- Landau's lemma for a Dirichlet L-function, centred to the right of `Re s = 1`. -/
lemma landau_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hc₀ : 1 < c₀.re) (hB : 0 < B)
    (him : ∀ z ∈ closedBall c₀ R, z.im ≠ 0)
    (hbd : ∀ z ∈ closedBall c₀ R, ‖LFunction χ z‖ ≤ Real.exp B) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ u ∈ Z, u ∈ closedBall c₀ (R / 4) ∧ 0 < m u ∧ LFunction χ u = 0) ∧
      (∀ u ∈ closedBall c₀ (R / 4), LFunction χ u = 0 → u ∈ Z) ∧
      ((∑ u ∈ Z, m u : ℕ) : ℝ) * Real.log 2 ≤ B + Real.log (c₀.re / (c₀.re - 1)) ∧
      ∀ z ∈ closedBall c₀ (R / 16), LFunction χ z ≠ 0 →
        ‖deriv (LFunction χ) z / LFunction χ z - ∑ u ∈ Z, (m u : ℂ) / (z - u)‖ ≤
          32 * (B + Real.log (c₀.re / (c₀.re - 1))) / R := by
  have hσ1 : 0 < c₀.re - 1 := by linarith
  have hσ0 : 0 < c₀.re := by linarith
  have hratio : 1 < c₀.re / (c₀.re - 1) := by rw [one_lt_div hσ1]; linarith
  have hlog : 0 < Real.log (c₀.re / (c₀.re - 1)) := Real.log_pos hratio
  have hlow := norm_LFunction_ge χ hc₀
  have hlow0 : 0 < (c₀.re - 1) / c₀.re := div_pos hσ1 hσ0
  have hfc : LFunction χ c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  refine landau_logDeriv hR (by linarith) ?_ hfc ?_
  · intro z hz
    apply analyticAt_LFunction
    intro h1
    exact him z hz (by rw [h1, one_im])
  · intro z hz
    calc ‖LFunction χ z‖ ≤ Real.exp B := hbd z hz
      _ = Real.exp (B + Real.log (c₀.re / (c₀.re - 1))) * ((c₀.re - 1) / c₀.re) := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
        field_simp
      _ ≤ Real.exp (B + Real.log (c₀.re / (c₀.re - 1))) * ‖LFunction χ c₀‖ := by gcongr

lemma re_div_nonneg_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) (m : ℕ) : 0 ≤ ((m : ℂ) / w).re := by
  rw [div_re]
  simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hw) (normSq_nonneg w)

/-- Lower bounds for `Re L'/L` at the centre: every zero contributes nonnegatively. -/
lemma re_logDeriv_center {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hc₀ : 1 < c₀.re) (hB : 0 < B)
    (him : ∀ z ∈ closedBall c₀ R, z.im ≠ 0)
    (hbd : ∀ z ∈ closedBall c₀ R, ‖LFunction χ z‖ ≤ Real.exp B) :
    -(32 * (B + Real.log (c₀.re / (c₀.re - 1))) / R) ≤
        (deriv (LFunction χ) c₀ / LFunction χ c₀).re ∧
    ∀ ρ ∈ closedBall c₀ (R / 4), LFunction χ ρ = 0 →
      (1 / (c₀ - ρ)).re - 32 * (B + Real.log (c₀.re / (c₀.re - 1))) / R ≤
        (deriv (LFunction χ) c₀ / LFunction χ c₀).re := by
  obtain ⟨Z, m, hZ, hZall, -, hform⟩ := landau_LFunction χ hR hc₀ hB him hbd
  set E := 32 * (B + Real.log (c₀.re / (c₀.re - 1))) / R with hE
  have hlow := norm_LFunction_ge χ hc₀
  have hlow0 : 0 < (c₀.re - 1) / c₀.re := div_pos (by linarith) (by linarith)
  have hfc : LFunction χ c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have h := hform c₀ (mem_closedBall_self (by positivity)) hfc
  set S := ∑ u ∈ Z, (m u : ℂ) / (c₀ - u) with hS
  set X := deriv (LFunction χ) c₀ / LFunction χ c₀ with hX
  have hXS : S.re - E ≤ X.re := by
    have h1 := abs_re_le_norm (X - S)
    have h2 := neg_abs_le (X - S).re
    rw [sub_re] at h1 h2
    linarith
  have hterm : ∀ u ∈ Z, 0 ≤ ((m u : ℂ) / (c₀ - u)).re := by
    intro u hu
    apply re_div_nonneg_of_re_nonneg
    obtain ⟨hu1, -, hu0⟩ := hZ u hu
    have hu1' : u ∈ closedBall c₀ R :=
      closedBall_subset_closedBall (by linarith) hu1
    have hune : u ≠ 1 := by
      intro h1
      exact him u hu1' (by rw [h1, one_im])
    have : u.re < 1 := by
      by_contra hcon
      push Not at hcon
      exact LFunction_ne_zero_of_one_le_re χ (Or.inr hune) hcon hu0
    rw [sub_re]
    linarith
  have hSre : S.re = ∑ u ∈ Z, ((m u : ℂ) / (c₀ - u)).re := by
    rw [hS, Complex.re_sum]
  constructor
  · have : 0 ≤ S.re := by
      rw [hSre]
      exact Finset.sum_nonneg hterm
    linarith
  · intro ρ hρ hρ0
    have hρZ := hZall ρ hρ hρ0
    have h1 : ((m ρ : ℂ) / (c₀ - ρ)).re ≤ S.re := by
      rw [hSre]
      exact Finset.single_le_sum hterm hρZ
    have h2 : (1 / (c₀ - ρ)).re ≤ ((m ρ : ℂ) / (c₀ - ρ)).re := by
      have hm := (hZ ρ hρZ).2.1
      have e : ((m ρ : ℂ) / (c₀ - ρ)).re = (m ρ : ℝ) * (1 / (c₀ - ρ)).re := by
        rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]
      have hnn : 0 ≤ (1 / (c₀ - ρ)).re := by
        have := hterm ρ hρZ
        rw [e] at this
        have hm' : (0 : ℝ) < m ρ := by exact_mod_cast hm
        exact nonneg_of_mul_nonneg_right (by linarith) hm'
      rw [e]
      have : (1 : ℝ) ≤ m ρ := by exact_mod_cast hm
      exact le_mul_of_one_le_left hnn this
    linarith

/-- **[22] Lemma 3.6, zero-free part**, with all parameters explicit. -/
lemma zero_free_core {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {LL T K₁ C₀ c X : ℝ}
    (hT : 2 ≤ T) (hK₁ : 1 ≤ K₁)
    (hc : c = 17 / (420 * (18 * (K₁ + 1) + 1)))
    (hlogL : Real.log LL = T) (h18 : 18 * T ^ 4 ≤ LL) (h10c : 1 ≤ 10 * c * T ^ 2)
    (h3C : 3 * C₀ * T ^ 2 < LL) (hX : 1 ≤ X)
    (hbound : ∀ ψ : DirichletCharacter ℂ q, ∀ z : ℂ, |z.re - 1| ≤ 10 * (T ^ 4 / LL) →
      1 / 2 ≤ |z.im| → |z.im| ≤ 3 * X → ‖LFunction ψ z‖ ≤ Real.exp (K₁ * T ^ 2))
    (hvM : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries ↗ArithmeticFunction.vonMangoldt σ).re ≤ 1 / (σ - 1) + C₀)
    (s : ℂ) (hs1 : 1 - c * T ^ 2 / LL ≤ s.re) (hs2 : 1 ≤ |s.im|) (hs3 : |s.im| ≤ X) :
    LFunction χ s ≠ 0 := by
  intro hzero
  have hs_ne1 : s ≠ 1 := by
    intro h
    rw [h, one_im, abs_zero] at hs2
    linarith
  by_cases hβ : 1 ≤ s.re
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inr hs_ne1) hβ hzero
  push Not at hβ
  have hT0 : 0 < T := by linarith
  have hT2 : 4 ≤ T ^ 2 := by nlinarith
  have hL : 0 < LL := by nlinarith [pow_pos hT0 4]
  have hQ : 0 < 18 * (K₁ + 1) + 1 := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc20 : 20 * c ≤ 1 := by
    rw [hc, mul_div_assoc', div_le_one (by positivity)]
    linarith
  set D := T ^ 2 / LL with hD
  set r := T ^ 4 / LL with hr
  have hD0 : 0 < D := by positivity
  have hr0 : 0 < r := by positivity
  have hrD : r = T ^ 2 * D := by rw [hr, hD]; ring
  have hr18 : 18 * r ≤ 1 := by
    rw [hr, mul_div_assoc', div_le_one hL]
    exact h18
  set μ := 20 * c * D with hμ
  have hμ0 : 0 < μ := by positivity
  have hμr : μ ≤ r := by
    rw [hrD, hμ]
    exact mul_le_mul_of_nonneg_right (by linarith) hD0.le
  set σ := 1 + μ with hσ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  set R := 9 * r with hR
  have hR0 : 0 < R := by positivity
  have hRhalf : R ≤ 1 / 2 := by linarith
  set v := s.im with hv
  set c₁ : ℂ := (σ : ℂ) + (v : ℂ) * I with hc₁
  set c₂ : ℂ := (σ : ℂ) + 2 * (v : ℂ) * I with hc₂
  have hc₁re : c₁.re = σ := by simp [hc₁]
  have hc₁im : c₁.im = v := by simp [hc₁]
  have hc₂re : c₂.re = σ := by simp [hc₂]
  have hc₂im : c₂.im = 2 * v := by simp [hc₂]
  have hB : 0 < K₁ * T ^ 2 := by positivity
  have hre_ok : ∀ z : ℂ, |z.re - σ| ≤ R → |z.re - 1| ≤ 10 * (T ^ 4 / LL) := by
    intro z hz
    rw [← hr]
    have h1 : |z.re - 1| ≤ |z.re - σ| + |σ - 1| := abs_sub_le _ _ _
    rw [abs_of_pos (by linarith : (0 : ℝ) < σ - 1)] at h1
    linarith
  have hreg1 : ∀ z ∈ closedBall c₁ R,
      |z.re - 1| ≤ 10 * (T ^ 4 / LL) ∧ 1 / 2 ≤ |z.im| ∧ |z.im| ≤ 3 * X := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_closedBall_re_im hz
    rw [hc₁re] at h1
    rw [hc₁im] at h2
    have h3 := abs_sub_abs_le_abs_sub v z.im
    have h4 := abs_sub_abs_le_abs_sub z.im v
    rw [abs_sub_comm] at h3
    exact ⟨hre_ok z h1, by linarith, by linarith⟩
  have hreg2 : ∀ z ∈ closedBall c₂ R,
      |z.re - 1| ≤ 10 * (T ^ 4 / LL) ∧ 1 / 2 ≤ |z.im| ∧ |z.im| ≤ 3 * X := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_closedBall_re_im hz
    rw [hc₂re] at h1
    rw [hc₂im] at h2
    have h3 := abs_sub_abs_le_abs_sub (2 * v) z.im
    have h4 := abs_sub_abs_le_abs_sub z.im (2 * v)
    rw [abs_sub_comm] at h3
    have h5 : |2 * v| = 2 * |v| := by rw [abs_mul, abs_two]
    exact ⟨hre_ok z h1, by linarith, by linarith⟩
  have him1 : ∀ z ∈ closedBall c₁ R, z.im ≠ 0 := fun z hz h0 => by
    have := (hreg1 z hz).2.1
    rw [h0, abs_zero] at this
    linarith
  have him2 : ∀ z ∈ closedBall c₂ R, z.im ≠ 0 := fun z hz h0 => by
    have := (hreg2 z hz).2.1
    rw [h0, abs_zero] at this
    linarith
  have hbd1 : ∀ z ∈ closedBall c₁ R, ‖LFunction χ z‖ ≤ Real.exp (K₁ * T ^ 2) := fun z hz =>
    hbound χ z (hreg1 z hz).1 (hreg1 z hz).2.1 (hreg1 z hz).2.2
  have hbd2 : ∀ z ∈ closedBall c₂ R, ‖LFunction (χ ^ 2) z‖ ≤ Real.exp (K₁ * T ^ 2) :=
    fun z hz => hbound (χ ^ 2) z (hreg2 z hz).1 (hreg2 z hz).2.1 (hreg2 z hz).2.2
  have hc₁re' : 1 < c₁.re := by rw [hc₁re]; exact hσ1
  have hc₂re' : 1 < c₂.re := by rw [hc₂re]; exact hσ1
  obtain ⟨-, hA2⟩ := re_logDeriv_center χ hR0 hc₁re' hB him1 hbd1
  obtain ⟨hB1, -⟩ := re_logDeriv_center (χ ^ 2) hR0 hc₂re' hB him2 hbd2
  rw [hc₁re] at hA2
  rw [hc₂re] at hB1
  set M := K₁ * T ^ 2 + Real.log (σ / (σ - 1)) with hM
  set E := 32 * M / R with hE
  -- the zero `s` lies in the small disk around `c₁`
  set w := σ - s.re with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  have hcD : c * T ^ 2 / LL = c * D := by rw [hD]; ring
  have hw21 : w ≤ 21 * c * D := by
    rw [hw, hσ, hμ]
    rw [hcD] at hs1
    linarith
  have hsc : c₁ - s = ((w : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hc₁, hw]
    · simp [hc₁, hv]
  have hs_ball : s ∈ closedBall c₁ (R / 4) := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hsc, norm_real, Real.norm_eq_abs,
      abs_of_pos hw0]
    rw [hR, hrD]
    have h1 : (21 * c) * D ≤ (9 * T ^ 2 / 4) * D :=
      mul_le_mul_of_nonneg_right (by linarith) hD0.le
    linarith
  have hX1 := hA2 s hs_ball hzero
  rw [hsc] at hX1
  have hre_w : (1 / ((w : ℝ) : ℂ)).re = 1 / w := by
    rw [← ofReal_one, ← ofReal_div, ofReal_re]
  rw [hre_w] at hX1
  have h341 := three_four_one χ hσ1 v
  have hA := hvM σ hσ1 hσ2
  have hσμ : σ - 1 = μ := by rw [hσ]; ring
  rw [hσμ] at hA
  -- `log (σ/(σ-1)) ≤ T²`
  have hlogσ : Real.log (σ / (σ - 1)) ≤ T ^ 2 := by
    have h1 : σ / (σ - 1) ≤ LL := by
      rw [div_le_iff₀ (by linarith)]
      have : LL * (σ - 1) = 20 * c * T ^ 2 := by
        rw [hσμ, hμ, hD]
        field_simp
      rw [this]
      linarith
    calc Real.log (σ / (σ - 1)) ≤ Real.log LL :=
          Real.log_le_log (div_pos (by linarith) (by linarith)) h1
      _ = T := hlogL
      _ ≤ T ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hMle : M ≤ (K₁ + 1) * T ^ 2 := by rw [hM]; linarith
  -- combine: `0 ≤ 3/μ + 3C₀ - 4/w + 5E`
  have key : 0 ≤ 3 * (1 / μ) + 3 * C₀ - 4 * (1 / w) + 5 * E := by
    have e1 : (deriv (LFunction χ) ((σ : ℂ) + (v : ℂ) * I) /
        LFunction χ ((σ : ℂ) + (v : ℂ) * I)).re = (deriv (LFunction χ) c₁ / LFunction χ c₁).re :=
      rfl
    linarith
  have hDμ : D * (1 / μ) = 1 / (20 * c) := by
    rw [hμ]
    field_simp
  have hDw : 1 / (21 * c) ≤ D * (1 / w) := by
    have h1 : D / (21 * c * D) ≤ D / w := div_le_div_of_nonneg_left hD0.le hw0 hw21
    have h2 : D / (21 * c * D) = 1 / (21 * c) := by field_simp
    rw [h2] at h1
    rw [mul_one_div]
    exact h1
  have hDE : D * E ≤ 32 * (K₁ + 1) / 9 := by
    rw [hE, hR, hrD]
    have hT2pos : 0 < T ^ 2 := by positivity
    rw [show D * (32 * M / (9 * (T ^ 2 * D))) = 32 * M / (9 * T ^ 2) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hfrac : 3 * (1 / (20 * c)) - 4 * (1 / (21 * c)) = -(18 * (K₁ + 1) + 1) := by
    rw [hc]
    field_simp
    ring
  have hCD : 3 * C₀ * D < 1 := by
    rw [hD, mul_div_assoc', div_lt_one hL]
    exact h3C
  have hprod := mul_nonneg hD0.le key
  have expand : D * (3 * (1 / μ) + 3 * C₀ - 4 * (1 / w) + 5 * E) =
      3 * (D * (1 / μ)) + 3 * C₀ * D - 4 * (D * (1 / w)) + 5 * (D * E) := by ring
  rw [expand] at hprod
  linarith

/-- **[22] Lemma 3.6, log-derivative part** (3.17), with all parameters explicit. -/
lemma logDeriv_bound_core {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {LL T K₁ c X : ℝ}
    (hT : 2 ≤ T) (hK₁ : 1 ≤ K₁) (hc0 : 0 < c) (hc1 : 8 * c ≤ 1)
    (hlogL : Real.log LL = T) (h18 : 18 * T ^ 4 ≤ LL)
    (hbound : ∀ z : ℂ, |z.re - 1| ≤ 10 * (T ^ 4 / LL) →
      1 / 2 ≤ |z.im| → |z.im| ≤ 3 * X → ‖LFunction χ z‖ ≤ Real.exp (K₁ * T ^ 2))
    (hzf : ∀ s : ℂ, 1 - c * T ^ 2 / LL ≤ s.re → 1 ≤ |s.im| → |s.im| ≤ X → LFunction χ s ≠ 0)
    (s : ℂ) (hs1 : 1 - c * T ^ 2 / (2 * LL) ≤ s.re) (hs2 : s.re ≤ 1 + 1 / LL)
    (hs3 : 2 ≤ |s.im|) (hs4 : |s.im| ≤ X / 2) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ (K₁ + 1) * (3 / c + 4) * LL := by
  have hT0 : 0 < T := by linarith
  have hT2 : 4 ≤ T ^ 2 := by nlinarith
  have hT4 : 16 ≤ T ^ 4 := by nlinarith
  have hL : 0 < LL := by nlinarith
  set r := T ^ 4 / LL with hr
  have hr0 : 0 < r := by positivity
  have hr18 : 18 * r ≤ 1 := by
    rw [hr, mul_div_assoc', div_le_one hL]
    exact h18
  have hrL : r * LL = T ^ 4 := by rw [hr]; field_simp
  set R := 9 * r with hR
  have hR0 : 0 < R := by positivity
  have hRhalf : R ≤ 1 / 2 := by linarith
  set t := s.im with ht
  set σ₀ := 1 + r / 2 with hσ₀
  set c₀ : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hc₀
  have hc₀re : c₀.re = σ₀ := by simp [hc₀]
  have hc₀im : c₀.im = t := by simp [hc₀]
  have hreg : ∀ z ∈ closedBall c₀ R,
      |z.re - 1| ≤ 10 * (T ^ 4 / LL) ∧ 1 / 2 ≤ |z.im| ∧ |z.im| ≤ 3 * X := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_closedBall_re_im hz
    rw [hc₀re] at h1
    rw [hc₀im] at h2
    have h3 := abs_sub_abs_le_abs_sub t z.im
    have h4 := abs_sub_abs_le_abs_sub z.im t
    rw [abs_sub_comm] at h3
    have h5 : |z.re - 1| ≤ |z.re - σ₀| + |σ₀ - 1| := abs_sub_le _ _ _
    rw [abs_of_pos (by rw [hσ₀]; linarith : (0 : ℝ) < σ₀ - 1)] at h5
    refine ⟨?_, by linarith, by linarith⟩
    rw [← hr]
    rw [hσ₀] at h5
    linarith
  have him : ∀ z ∈ closedBall c₀ R, z.im ≠ 0 := fun z hz h0 => by
    have := (hreg z hz).2.1
    rw [h0, abs_zero] at this
    linarith
  have hbd : ∀ z ∈ closedBall c₀ R, ‖LFunction χ z‖ ≤ Real.exp (K₁ * T ^ 2) := fun z hz =>
    hbound z (hreg z hz).1 (hreg z hz).2.1 (hreg z hz).2.2
  have hB : 0 < K₁ * T ^ 2 := by positivity
  have hc₀re' : 1 < c₀.re := by rw [hc₀re, hσ₀]; linarith
  obtain ⟨Z, m, hZ, -, hcount, hform⟩ := landau_LFunction χ hR0 hc₀re' hB him hbd
  rw [hc₀re] at hcount hform
  set M := K₁ * T ^ 2 + Real.log (σ₀ / (σ₀ - 1)) with hM
  have hσ₀1 : σ₀ - 1 = r / 2 := by rw [hσ₀]; ring
  have hlog : Real.log (σ₀ / (σ₀ - 1)) ≤ T ^ 2 := by
    have h1 : σ₀ / (σ₀ - 1) ≤ LL := by
      rw [div_le_iff₀ (by rw [hσ₀1]; positivity), hσ₀1]
      have : LL * (r / 2) = T ^ 4 / 2 := by rw [← hrL]; ring
      rw [this, hσ₀]
      linarith
    calc Real.log (σ₀ / (σ₀ - 1)) ≤ Real.log LL :=
          Real.log_le_log (div_pos (by rw [hσ₀]; linarith) (by rw [hσ₀1]; positivity)) h1
      _ = T := hlogL
      _ ≤ T ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hMle : M ≤ (K₁ + 1) * T ^ 2 := by rw [hM]; linarith
  -- `s` lies in the small disk
  have hsc : s - c₀ = ((s.re - σ₀ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hc₀]
    · simp [hc₀, ht]
  have hcT : c * T ^ 2 / (2 * LL) * 16 ≤ r := by
    rw [hr, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hL]
    have h8 : 8 * c * T ^ 2 ≤ T ^ 4 := by
      have h1 : (8 * c) * T ^ 2 ≤ 1 * T ^ 2 := mul_le_mul_of_nonneg_right hc1 (by positivity)
      have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right h8 hL.le
    linarith
  have hLr : 1 / LL ≤ r := by
    rw [hr, div_le_div_iff_of_pos_right hL]
    linarith
  have hs_ball : s ∈ closedBall c₀ (R / 16) := by
    rw [mem_closedBall, dist_eq_norm, hsc, norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · rw [hR, hσ₀]
      linarith
    · rw [hR, hσ₀]
      linarith
  have hdl : c * T ^ 2 / LL = 2 * (c * T ^ 2 / (2 * LL)) := by
    field_simp
  set dl := c * T ^ 2 / (2 * LL) with hdldef
  have hdl0 : 0 < dl := by positivity
  have hfs : LFunction χ s ≠ 0 := hzf s (by linarith) (by linarith) (by linarith)
  have hF := hform s hs_ball hfs
  have hterm : ∀ u ∈ Z, ‖(m u : ℂ) / (s - u)‖ ≤ (m u : ℝ) / dl := by
    intro u hu
    obtain ⟨hu1, -, hu0⟩ := hZ u hu
    obtain ⟨-, hu2⟩ := mem_closedBall_re_im hu1
    rw [hc₀im] at hu2
    have hure : u.re < 1 - c * T ^ 2 / LL := by
      by_contra hcon
      push Not at hcon
      have h3 := abs_sub_abs_le_abs_sub t u.im
      have h4 := abs_sub_abs_le_abs_sub u.im t
      rw [abs_sub_comm] at h3
      exact hzf u hcon (by linarith) (by linarith) hu0
    have hdist : dl ≤ ‖s - u‖ := by
      calc dl ≤ (s - u).re := by rw [sub_re]; linarith
        _ ≤ |(s - u).re| := le_abs_self _
        _ ≤ ‖s - u‖ := abs_re_le_norm _
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdl0 hdist
  have hsum : ‖∑ u ∈ Z, (m u : ℂ) / (s - u)‖ ≤ ((∑ u ∈ Z, m u : ℕ) : ℝ) / dl := by
    calc ‖∑ u ∈ Z, (m u : ℂ) / (s - u)‖ ≤ ∑ u ∈ Z, ‖(m u : ℂ) / (s - u)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ Z, (m u : ℝ) / dl := Finset.sum_le_sum hterm
      _ = ((∑ u ∈ Z, m u : ℕ) : ℝ) / dl := by rw [← Finset.sum_div]; push_cast; rfl
  have htri : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      ((∑ u ∈ Z, m u : ℕ) : ℝ) / dl + 32 * M / R := by
    calc ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ‖∑ u ∈ Z, (m u : ℂ) / (s - u)‖ +
          ‖deriv (LFunction χ) s / LFunction χ s - ∑ u ∈ Z, (m u : ℂ) / (s - u)‖ :=
          norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := add_le_add hsum hF
  set N : ℝ := ((∑ u ∈ Z, m u : ℕ) : ℝ) with hN
  have hlog2 : 2 / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hN' : N ≤ (K₁ + 1) * T ^ 2 * (3 / 2) := by
    have h1 : N * Real.log 2 ≤ (K₁ + 1) * T ^ 2 := hcount.trans hMle
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have h2 := mul_le_mul_of_nonneg_left hlog2.le hN0
    linarith
  have h1 : N / dl ≤ (K₁ + 1) * (3 / c) * LL := by
    rw [div_le_iff₀ hdl0]
    have : (K₁ + 1) * (3 / c) * LL * dl = (K₁ + 1) * T ^ 2 * (3 / 2) := by
      rw [hdldef]
      field_simp
    linarith
  have h2 : 32 * M / R ≤ (K₁ + 1) * 4 * LL := by
    rw [div_le_iff₀ hR0]
    have : (K₁ + 1) * 4 * LL * R = (K₁ + 1) * 36 * T ^ 4 := by
      rw [hR, ← hrL]
      ring
    rw [this]
    have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h3 : (K₁ + 1) * T ^ 2 ≤ (K₁ + 1) * T ^ 4 := mul_le_mul_of_nonneg_left hT24 (by linarith)
    have h4 : 0 ≤ (K₁ + 1) * T ^ 4 := by positivity
    linarith
  calc ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ N / dl + 32 * M / R := htri
    _ ≤ (K₁ + 1) * (3 / c) * LL + (K₁ + 1) * 4 * LL := add_le_add h1 h2
    _ = (K₁ + 1) * (3 / c + 4) * LL := by ring

end ArtinPrimitiveRoots.L31Z

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (C : ℝ) (hC : 0 < C) :
    ∃ c K x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ log x ^ C →
      ∀ χ : DirichletCharacter ℂ q,
        (∀ s : ℂ, 1 - c * log (log x) ^ 2 / log x ≤ s.re → 1 ≤ |s.im| → |s.im| ≤ x ^ 3 →
          DirichletCharacter.LFunction χ s ≠ 0) ∧
        (∀ s : ℂ, 1 - c * log (log x) ^ 2 / (2 * log x) ≤ s.re → s.re ≤ 1 + 1 / log x →
          2 ≤ |s.im| → |s.im| ≤ x ^ 3 / 2 →
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
            K * log x) := by
  obtain ⟨K₀, xB, hB⟩ := dirichlet_L_bound_near_one C hC
  obtain ⟨C₀, hC₀⟩ := L31Z.LSeries_vonMangoldt_re_le
  set K₁ := max K₀ 1 with hK₁
  set C₀' := max C₀ 0 with hC₀'
  have hK₁1 : 1 ≤ K₁ := le_max_right _ _
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  set c := 17 / (420 * (18 * (K₁ + 1) + 1)) with hc
  have hQ : 0 < 18 * (K₁ + 1) + 1 := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc8 : 8 * c ≤ 1 := by
    rw [hc, mul_div_assoc', div_le_one (by positivity)]
    linarith
  set T₀ := max 2 (max C₀' (1 / (10 * c))) with hT₀
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      xB ≤ x ∧ 1 ≤ x ∧ T₀ ≤ log (log x) ∧ 18 * log (log x) ^ 4 ≤ log x := by
    have hT : Filter.Tendsto (fun x => log (log x)) Filter.atTop Filter.atTop :=
      tendsto_log_atTop.comp tendsto_log_atTop
    have h4 : ∀ᶠ y : ℝ in Filter.atTop, 18 * log y ^ 4 ≤ y := by
      have := (isLittleO_pow_log_id_atTop (n := 4)).bound (show (0 : ℝ) < 1 / 18 by norm_num)
      filter_upwards [this, Filter.eventually_ge_atTop 0] with y hy hy0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg hy0] at hy
      have := le_abs_self (log y ^ 4)
      linarith
    filter_upwards [Filter.eventually_ge_atTop xB, Filter.eventually_ge_atTop 1,
      hT.eventually_ge_atTop T₀, tendsto_log_atTop.eventually h4] with x h1 h2 h3 h5
    exact ⟨h1, h2, h3, h5⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨c, (K₁ + 1) * (3 / c + 4), x₀, hc0, ?_⟩
  intro x hx q _ hq χ
  obtain ⟨hxB, hx1, hT₀x, h18⟩ := hx₀ x hx
  have hT2 : 2 ≤ log (log x) := le_trans (le_max_left _ _) hT₀x
  have hTC : C₀' ≤ log (log x) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT₀x
  have hTc : 1 / (10 * c) ≤ log (log x) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT₀x
  have hT0 : 0 < log (log x) := by linarith
  have h10c : 1 ≤ 10 * c * log (log x) ^ 2 := by
    have h' : 1 ≤ 10 * c * log (log x) := by
      rw [div_le_iff₀ (by positivity)] at hTc
      linarith
    have h'' : (1 : ℝ) * 1 ≤ (10 * c * log (log x)) * log (log x) :=
      mul_le_mul h' (by linarith) (by norm_num) (by positivity)
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (10 * c * log (log x)) * log (log x) := h''
      _ = 10 * c * log (log x) ^ 2 := by ring
  have h3C : 3 * C₀' * log (log x) ^ 2 < log x := by
    have : 3 * C₀' * log (log x) ^ 2 < 18 * log (log x) ^ 4 := by
      have hpos : 0 < log (log x) ^ 2 := by positivity
      have h2T : 2 * log (log x) ≤ log (log x) * log (log x) :=
        mul_le_mul_of_nonneg_right hT2 hT0.le
      have h' : 3 * C₀' < 18 * log (log x) ^ 2 := by
        rw [sq]
        linarith
      have := mul_lt_mul_of_pos_right h' hpos
      calc 3 * C₀' * log (log x) ^ 2 < 18 * log (log x) ^ 2 * log (log x) ^ 2 := this
        _ = 18 * log (log x) ^ 4 := by ring
    linarith
  have hX : 1 ≤ x ^ 3 := one_le_pow₀ hx1
  have hbound : ∀ ψ : DirichletCharacter ℂ q, ∀ z : ℂ,
      |z.re - 1| ≤ 10 * (log (log x) ^ 4 / log x) → 1 / 2 ≤ |z.im| → |z.im| ≤ 3 * x ^ 3 →
      ‖DirichletCharacter.LFunction ψ z‖ ≤ exp (K₁ * log (log x) ^ 2) := by
    intro ψ z h1 h2 h3
    have := hB x hxB q hq ψ z.re z.im h1 h2 h3
    rw [Complex.re_add_im] at this
    refine this.trans (exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hvM : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ).re ≤ 1 / (σ - 1) + C₀' :=
    fun σ h1 h2 => (hC₀ σ h1 h2).trans (by linarith [le_max_left C₀ 0])
  have hzf : ∀ s : ℂ, 1 - c * log (log x) ^ 2 / log x ≤ s.re → 1 ≤ |s.im| →
      |s.im| ≤ x ^ 3 → DirichletCharacter.LFunction χ s ≠ 0 :=
    fun s h1 h2 h3 => L31Z.zero_free_core χ hT2 hK₁1 hc rfl h18 h10c h3C hX hbound hvM
      s h1 h2 h3
  refine ⟨hzf, ?_⟩
  intro s h1 h2 h3 h4
  exact L31Z.logDeriv_bound_core χ hT2 hK₁1 hc0 hc8 rfl h18 (hbound χ) hzf s h1 h2 h3 h4
end
