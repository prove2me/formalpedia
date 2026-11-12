-- Prove2me | solution 1 for ALAVI.subproblem_unique
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:07:40.585855+00:00
-- url     : https://prove2.me/submissions/3e673cc4-fb20-431d-aff1-121847596853

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_IsSubproblemSol
import Theorems.Thm_ALAVI_eq_32_optimality

namespace Aux_ALAVI_subproblem

open ContinuousLinearMap

lemma isClosed_real_epigraph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {J : E → EReal} (hJlsc : LowerSemicontinuous J) :
    IsClosed {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := by
  have hpre : {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} =
      (Prod.map (id : E → E) (Real.toEReal : ℝ → EReal)) ⁻¹' {p : E × EReal | J p.1 ≤ p.2} := by
    ext ⟨w, r⟩
    rfl
  rw [hpre]
  exact hJlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)

lemma exists_affine_minorant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {J : E → EReal} (hJ : GoldenRatioVI.Fixed.IsProperConvexLSC J)
    {a : E} (haJ : a ∈ GoldenRatioVI.Fixed.effDom J) :
    ∃ (u : E →L[ℝ] ℝ) (c₀ : ℝ), ∀ w ∈ GoldenRatioVI.Fixed.effDom J,
      c₀ - ‖u‖ * ‖w‖ ≤ (J w).toReal := by
  rcases hJ with ⟨hJbot, _, hJcv, hJlsc⟩
  let A : Set (E × ℝ) := {p : E × ℝ | J p.1 ≤ (p.2 : EReal)}
  have hAc : IsClosed A := isClosed_real_epigraph hJlsc
  have hnot : (a, (J a).toReal - 1) ∉ A := by
    intro hmem
    change J a ≤ (((J a).toReal - 1 : ℝ) : EReal) at hmem
    have hJa : J a = ((J a).toReal : EReal) := (EReal.coe_toReal haJ (hJbot a)).symm
    have hmem' : ((J a).toReal : EReal) ≤ (((J a).toReal - 1 : ℝ) : EReal) := hJa ▸ hmem
    have hreal := EReal.coe_le_coe_iff.mp hmem'
    linarith
  obtain ⟨L, b, hb_lt, hb_gt⟩ := geometric_hahn_banach_point_closed hJcv hAc hnot
  have hv : ∀ r : ℝ, L (0, r) = r * L (0, 1) := by
    intro r
    have h := L.map_smul r ((0 : E), (1 : ℝ))
    simpa [Prod.smul_mk, smul_eq_mul] using h
  have hsplit : ∀ (w : E) (r : ℝ), L (w, r) = L (w, 0) + r * L (0, 1) := by
    intro w r
    have h : ((w, r) : E × ℝ) = (w, 0) + (0, r) := by ext <;> simp
    rw [h, L.map_add, hv r]
  have ha_mem : (a, (J a).toReal) ∈ A := by
    show J a ≤ ((J a).toReal : EReal)
    rw [EReal.coe_toReal haJ (hJbot a)]
  have ha_ineq : L (a, (J a).toReal - 1) < L (a, (J a).toReal) :=
    hb_lt.trans (hb_gt _ ha_mem)
  rw [hsplit a ((J a).toReal - 1), hsplit a (J a).toReal] at ha_ineq
  have hL01_pos : 0 < L (0, 1) := by linarith
  let u : E →L[ℝ] ℝ := (L (0, 1))⁻¹ • (L.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let c₀ : ℝ := (L (0, 1))⁻¹ * L (a, (J a).toReal - 1)
  refine ⟨u, c₀, fun w hwJ => ?_⟩
  have hw_mem : (w, (J w).toReal) ∈ A := by
    show J w ≤ ((J w).toReal : EReal)
    rw [EReal.coe_toReal hwJ (hJbot w)]
  have hw_ineq : L (a, (J a).toReal - 1) < L (w, (J w).toReal) :=
    hb_lt.trans (hb_gt _ hw_mem)
  rw [hsplit w (J w).toReal] at hw_ineq
  have hmul := mul_lt_mul_of_pos_left hw_ineq (inv_pos.mpr hL01_pos)
  have hL_ne : L (0, 1) ≠ 0 := ne_of_gt hL01_pos
  have hrhs : (L (0, 1))⁻¹ * (L (w, 0) + (J w).toReal * L (0, 1)) =
      u w + (J w).toReal := by
    simp only [u, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    field_simp
  have hu_le : -‖u‖ * ‖w‖ ≤ -u w := by
    have h := u.le_opNorm w
    rw [Real.norm_eq_abs] at h
    have habs := le_abs_self (u w)
    linarith
  linarith

lemma continuousOn_Theta {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {U : Set E} {Θ : E → F} {τ : ℝ}
    (hΘLip : ∀ a ∈ U, ∀ b ∈ U, ‖Θ a - Θ b‖ ≤ τ * ‖a - b‖) :
    ContinuousOn Θ U := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / (|τ| + 1), div_pos hε (by positivity), fun y hy hdist => ?_⟩
  rw [dist_eq_norm] at hdist ⊢
  have h1 : ‖Θ y - Θ x‖ ≤ |τ| * ‖y - x‖ :=
    (hΘLip y hy x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self τ) (norm_nonneg _))
  have h2 : |τ| * ‖y - x‖ ≤ (|τ| + 1) * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hpos : 0 < |τ| + 1 := by positivity
  have h3 : (|τ| + 1) * ‖y - x‖ < ε := (lt_div_iff₀' hpos).mp hdist
  linarith

end Aux_ALAVI_subproblem

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ α : ℝ)
    (hA : Standing U C G J Θ L τ) (hα : 0 < α) (g v : E) (q : F) (hq : q ∈ ProperCone.innerDual (C : Set F))
    (hfeas : ∃ a ∈ U, a ∈ GoldenRatioVI.Fixed.effDom J) :
    ∃! x, IsSubproblemSol U J Θ α g q v x := by
  have hUc : IsClosed U := hA.1
  have hJ : GoldenRatioVI.Fixed.IsProperConvexLSC J := hA.2.2.2.2.1
  have hJbot : ∀ y, J y ≠ ⊥ := hJ.1
  have hJlsc : LowerSemicontinuous J := hJ.2.2.2
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hΘLip : ∀ a ∈ U, ∀ b ∈ U, ‖Θ a - Θ b‖ ≤ τ * ‖a - b‖ := hA.2.2.2.2.2.2.2
  rcases hfeas with ⟨a, haU, haJ⟩
  let φ : E → ℝ := fun w => inner ℝ g w + inner ℝ q (Θ w) + ‖w - v‖ ^ 2 / (2 * α)
  let F_obj : E → EReal := fun w => (φ w : EReal) + J w
  have hφ_cont : ContinuousOn φ U := by
    have hg_cont : ContinuousOn (fun w : E => inner ℝ g w) U :=
      (continuous_const.inner continuous_id).continuousOn
    have hq_cont : ContinuousOn (fun w : E => inner ℝ q (Θ w)) U :=
      continuousOn_const.inner (Aux_ALAVI_subproblem.continuousOn_Theta hΘLip)
    have hn_cont : ContinuousOn (fun w : E => ‖w - v‖ ^ 2 / (2 * α)) U :=
      (((continuous_id.sub continuous_const).norm.pow 2).div_const (2 * α)).continuousOn
    exact (hg_cont.add hq_cont).add hn_cont
  let sublvl : ℝ → Set E := fun c => {w ∈ U | F_obj w ≤ (c : EReal)}
  have hsublvl_char : ∀ (c : ℝ) (w : E),
      w ∈ sublvl c ↔ w ∈ U ∧ J w ≤ ((c - φ w : ℝ) : EReal) := by
    intro c w
    simp only [sublvl, Set.mem_setOf_eq, F_obj]
    constructor
    · rintro ⟨hwU, hle⟩
      refine ⟨hwU, ?_⟩
      have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
        intro htop
        rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hle
        exact EReal.coe_ne_top _ (top_le_iff.mp hle)
      rw [← EReal.coe_toReal hwJ (hJbot w), ← EReal.coe_add] at hle
      have hr := EReal.coe_le_coe_iff.mp hle
      rw [← EReal.coe_toReal hwJ (hJbot w)]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rintro ⟨hwU, hle⟩
      refine ⟨hwU, ?_⟩
      have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
        intro htop
        rw [htop] at hle
        exact EReal.coe_ne_top _ (top_le_iff.mp hle)
      rw [← EReal.coe_toReal hwJ (hJbot w)] at hle ⊢
      have hr := EReal.coe_le_coe_iff.mp hle
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hsublvl_closed : ∀ c : ℝ, IsClosed (sublvl c) := by
    intro c
    have heq : sublvl c =
        U ∩ (fun w : E => (w, c - φ w)) ⁻¹' {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := by
      ext w
      exact hsublvl_char c w
    rw [heq]
    have hmap_cont : ContinuousOn (fun w : E => (w, c - φ w)) U :=
      continuousOn_id.prodMk (continuousOn_const.sub hφ_cont)
    exact hmap_cont.preimage_isClosed_of_isClosed hUc
      (Aux_ALAVI_subproblem.isClosed_real_epigraph hJlsc)
  obtain ⟨u_lin, c₀, hminor⟩ := Aux_ALAVI_subproblem.exists_affine_minorant hJ haJ
  have hcoercive : ∃ (K₁ K₀ : ℝ), 0 ≤ K₁ ∧
      ∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
        ‖w‖ ^ 2 / (4 * α) - K₁ * ‖w‖ - K₀ ≤ φ w + (J w).toReal := by
    refine ⟨‖g‖ + ‖q‖ * τ + ‖u_lin‖,
      ‖q‖ * (‖Θ a‖ + τ * ‖a‖) + ‖v‖ ^ 2 / (2 * α) - c₀, by positivity, ?_⟩
    intro w hwU hwJ
    have hg_lb : -‖g‖ * ‖w‖ ≤ inner ℝ g w := by
      have h := real_inner_le_norm (-g) w
      rw [inner_neg_left, norm_neg] at h
      linarith
    have hΘ_norm : ‖Θ w‖ ≤ ‖Θ a‖ + τ * ‖a‖ + τ * ‖w‖ := by
      have h1 : ‖Θ w‖ ≤ ‖Θ a‖ + ‖Θ w - Θ a‖ := by
        simpa [sub_add_cancel] using norm_add_le (Θ a) (Θ w - Θ a)
      have h2 := hΘLip w hwU a haU
      have h3 : ‖w - a‖ ≤ ‖w‖ + ‖a‖ := norm_sub_le w a
      have h4 : τ * ‖w - a‖ ≤ τ * (‖w‖ + ‖a‖) := mul_le_mul_of_nonneg_left h3 hτ.le
      linarith
    have hq_lb : -‖q‖ * (‖Θ a‖ + τ * ‖a‖ + τ * ‖w‖) ≤ inner ℝ q (Θ w) := by
      have h := real_inner_le_norm (-q) (Θ w)
      rw [inner_neg_left, norm_neg] at h
      have hm := mul_le_mul_of_nonneg_left hΘ_norm (norm_nonneg q)
      linarith
    have hnorm_lb : ‖w‖ ^ 2 / (4 * α) - ‖v‖ ^ 2 / (2 * α) ≤ ‖w - v‖ ^ 2 / (2 * α) := by
      have htri : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
        simpa [sub_add_cancel] using norm_add_le (w - v) v
      have hsq1 : ‖w‖ ^ 2 ≤ (‖w - v‖ + ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg w) htri 2
      have hsq2 : 0 ≤ (‖w - v‖ - ‖v‖) ^ 2 := sq_nonneg _
      have hsq3 : ‖w‖ ^ 2 ≤ 2 * ‖w - v‖ ^ 2 + 2 * ‖v‖ ^ 2 := by linarith
      have hdiv := div_le_div_of_nonneg_right hsq3 (by linarith : 0 ≤ 4 * α)
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have hrhs : (2 * ‖w - v‖ ^ 2 + 2 * ‖v‖ ^ 2) / (4 * α) =
          ‖w - v‖ ^ 2 / (2 * α) + ‖v‖ ^ 2 / (2 * α) := by
        field_simp
        ring
      linarith
    have hJ_lb := hminor w hwJ
    dsimp only [φ]
    linarith
  rcases hcoercive with ⟨K₁, K₀, hK₁_nonneg, hcoer⟩
  have hsublvl_bdd : ∀ c : ℝ, Bornology.IsBounded (sublvl c) := by
    intro c
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max 1 (4 * α * (|c + K₀| + K₁ + 1)), fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨hwU, hwJ_le⟩ := (hsublvl_char c w).mp hw
    have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
      intro htop
      rw [htop] at hwJ_le
      exact EReal.coe_ne_top _ (top_le_iff.mp hwJ_le)
    rw [← EReal.coe_toReal hwJ (hJbot w)] at hwJ_le
    have hw_real : φ w + (J w).toReal ≤ c := by linarith [EReal.coe_le_coe_iff.mp hwJ_le]
    have hlb := hcoer w hwU hwJ
    by_cases hw1 : ‖w‖ ≤ 1
    · exact hw1.trans (le_max_left _ _)
    · push_neg at hw1
      have h1 : ‖w‖ ^ 2 / (4 * α) ≤ (K₁ + |c + K₀|) * ‖w‖ := by
        have habs : c + K₀ ≤ |c + K₀| := le_abs_self _
        have hm : |c + K₀| ≤ |c + K₀| * ‖w‖ := le_mul_of_one_le_right (abs_nonneg _) hw1.le
        linarith
      have h2 : ‖w‖ * (‖w‖ / (4 * α)) ≤ ‖w‖ * (K₁ + |c + K₀|) := by
        have hα_ne : α ≠ 0 := ne_of_gt hα
        have hid : ‖w‖ * (‖w‖ / (4 * α)) = ‖w‖ ^ 2 / (4 * α) := by
          field_simp
        linarith
      have h3 : ‖w‖ / (4 * α) ≤ K₁ + |c + K₀| :=
        le_of_mul_le_mul_left h2 (by linarith : 0 < ‖w‖)
      have h4 : ‖w‖ ≤ 4 * α * (|c + K₀| + K₁ + 1) := by
        have hm := (div_le_iff₀' (by linarith : 0 < 4 * α)).mp h3
        linarith
      exact h4.trans (le_max_right _ _)
  let M₀ : ℝ := φ a + (J a).toReal
  have ha_mem : a ∈ sublvl M₀ := by
    rw [hsublvl_char]
    refine ⟨haU, ?_⟩
    rw [← EReal.coe_toReal haJ (hJbot a)]
    exact EReal.coe_le_coe_iff.mpr (by simp [M₀])
  let ValSet : Set ℝ := (fun w => φ w + (J w).toReal) '' sublvl M₀
  have hVal_ne : ValSet.Nonempty := ⟨M₀, a, ha_mem, rfl⟩
  have hVal_bdd : BddBelow ValSet := by
    refine ⟨-(4 * α * K₁ ^ 2 + K₀), ?_⟩
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨hwU, hwJ_le⟩ := (hsublvl_char M₀ w).mp hw
    have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
      intro htop
      rw [htop] at hwJ_le
      exact EReal.coe_ne_top _ (top_le_iff.mp hwJ_le)
    have hlb := hcoer w hwU hwJ
    have hsq : 0 ≤ (‖w‖ / (2 * Real.sqrt α) - Real.sqrt α * K₁) ^ 2 := sq_nonneg _
    have hexp : (‖w‖ / (2 * Real.sqrt α) - Real.sqrt α * K₁) ^ 2 =
        ‖w‖ ^ 2 / (4 * α) - K₁ * ‖w‖ + α * K₁ ^ 2 := by
      have hsqα : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
      have hsqrt_ne : Real.sqrt α ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hα)
      field_simp
      rw [hsqα]
      ring
    have hpos_extra : α * K₁ ^ 2 ≤ 4 * α * K₁ ^ 2 := by nlinarith [sq_nonneg K₁]
    linarith
  let m : ℝ := sInf ValSet
  let seq : ℕ → Set E := fun n => sublvl (min M₀ (m + 1 / (n + 1 : ℝ)))
  have hseq_anti : ∀ n, seq (n + 1) ⊆ seq n := by
    intro n w hw
    rw [hsublvl_char] at hw ⊢
    refine ⟨hw.1, hw.2.trans ?_⟩
    apply EReal.coe_le_coe_iff.mpr
    have hfrac : 1 / ((n + 1 : ℕ) + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    have hmin : min M₀ (m + 1 / ((n + 1 : ℕ) + 1 : ℝ)) ≤ min M₀ (m + 1 / (n + 1 : ℝ)) :=
      min_le_min_left M₀ (by linarith)
    linarith
  have hseq_ne : ∀ n, (seq n).Nonempty := by
    intro n
    have hlt : m < m + 1 / (n + 1 : ℝ) := by
      have hp : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    obtain ⟨y, ⟨w, hwM₀, rfl⟩, hy_lt⟩ := exists_lt_of_csInf_lt hVal_ne hlt
    refine ⟨w, ?_⟩
    rw [hsublvl_char] at hwM₀ ⊢
    refine ⟨hwM₀.1, ?_⟩
    have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
      intro htop
      rw [htop] at hwM₀
      exact EReal.coe_ne_top _ (top_le_iff.mp hwM₀.2)
    rw [← EReal.coe_toReal hwJ (hJbot w)] at hwM₀ ⊢
    have h1 : φ w + (J w).toReal ≤ M₀ := by linarith [EReal.coe_le_coe_iff.mp hwM₀.2]
    have hmin : φ w + (J w).toReal ≤ min M₀ (m + 1 / (n + 1 : ℝ)) := le_min h1 hy_lt.le
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hseq_compact0 : IsCompact (seq 0) :=
    Metric.isCompact_of_isClosed_isBounded (hsublvl_closed _) (hsublvl_bdd _)
  have hseq_closed : ∀ n, IsClosed (seq n) := fun n => hsublvl_closed _
  obtain ⟨x, hx_inter⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    seq hseq_anti hseq_ne hseq_compact0 hseq_closed
  rw [Set.mem_iInter] at hx_inter
  have hx0 := hx_inter 0
  have hxM₀ : x ∈ sublvl M₀ := by
    rw [hsublvl_char] at hx0 ⊢
    refine ⟨hx0.1, hx0.2.trans ?_⟩
    exact EReal.coe_le_coe_iff.mpr (by linarith [min_le_left M₀ (m + 1 / (0 + 1 : ℝ))])
  have hxU : x ∈ U := hxM₀.1
  have hxJ : x ∈ GoldenRatioVI.Fixed.effDom J := by
    obtain ⟨_, hle⟩ := (hsublvl_char M₀ x).mp hxM₀
    intro htop
    rw [htop] at hle
    exact EReal.coe_ne_top _ (top_le_iff.mp hle)
  have hx_le_m : φ x + (J x).toReal ≤ m := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
    have hxn := (hsublvl_char _ x).mp (hx_inter n)
    rw [← EReal.coe_toReal hxJ (hJbot x)] at hxn
    have hreal := EReal.coe_le_coe_iff.mp hxn.2
    have hmin := min_le_right M₀ (m + 1 / (n + 1 : ℝ))
    linarith
  have hx_sol : IsSubproblemSol U J Θ α g q v x := by
    refine ⟨hxU, fun w hwU => ?_⟩
    change F_obj x ≤ F_obj w
    have hFx : F_obj x = ((φ x + (J x).toReal : ℝ) : EReal) := by
      calc F_obj x = (φ x : EReal) + J x := rfl
        _ = (φ x : EReal) + ((J x).toReal : EReal) := by rw [EReal.coe_toReal hxJ (hJbot x)]
        _ = ((φ x + (J x).toReal : ℝ) : EReal) := (EReal.coe_add _ _).symm
    by_cases hwM₀ : w ∈ sublvl M₀
    · have hwJ : w ∈ GoldenRatioVI.Fixed.effDom J := by
        obtain ⟨_, hle⟩ := (hsublvl_char M₀ w).mp hwM₀
        intro htop
        rw [htop] at hle
        exact EReal.coe_ne_top _ (top_le_iff.mp hle)
      have hFw : F_obj w = ((φ w + (J w).toReal : ℝ) : EReal) := by
        calc F_obj w = (φ w : EReal) + J w := rfl
          _ = (φ w : EReal) + ((J w).toReal : EReal) := by rw [EReal.coe_toReal hwJ (hJbot w)]
          _ = ((φ w + (J w).toReal : ℝ) : EReal) := (EReal.coe_add _ _).symm
      have hm_le : m ≤ φ w + (J w).toReal := csInf_le hVal_bdd ⟨w, hwM₀, rfl⟩
      rw [hFx, hFw]
      exact EReal.coe_le_coe_iff.mpr (hx_le_m.trans hm_le)
    · have hgt : (M₀ : EReal) < F_obj w := by
        by_contra hle
        push_neg at hle
        exact hwM₀ ⟨hwU, hle⟩
      exact hxM₀.2.trans hgt.le
  refine ⟨x, hx_sol, fun y hy_sol => ?_⟩
  have hx32 := (ALAVI.eq_32_optimality U C G J Θ L τ α hA hα g v q hq ⟨a, haU, haJ⟩ x).mp hx_sol
  have hy32 := (ALAVI.eq_32_optimality U C G J Θ L τ α hA hα g v q hq ⟨a, haU, haJ⟩ y).mp hy_sol
  have h1 := hx32.2.2 y hy32.1 hy32.2.1
  have h2 := hy32.2.2 x hx32.1 hx32.2.1
  have hg_cancel : inner ℝ g (y - x) + inner ℝ g (x - y) = 0 := by
    have hneg : x - y = -(y - x) := by abel
    rw [hneg, inner_neg_right]
    ring
  have hq_cancel : inner ℝ q (Θ y - Θ x) + inner ℝ q (Θ x - Θ y) = 0 := by
    have hneg : Θ x - Θ y = -(Θ y - Θ x) := by abel
    rw [hneg, inner_neg_right]
    ring
  have hv_sum : inner ℝ (x - v) (y - x) + inner ℝ (y - v) (x - y) = -‖y - x‖ ^ 2 := by
    have hneg : x - y = -(y - x) := by abel
    have hdiff : (x - v) - (y - v) = -(y - x) := by abel
    rw [hneg, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left, hdiff, inner_neg_left,
      real_inner_self_eq_norm_sq]
  have hv_mul : 1 / α * inner ℝ (x - v) (y - x) + 1 / α * inner ℝ (y - v) (x - y) =
      1 / α * (-‖y - x‖ ^ 2) := by
    rw [← mul_add, hv_sum]
  have hsum : 0 ≤ 1 / α * (-‖y - x‖ ^ 2) := by linarith [h1, h2, hg_cancel, hq_cancel, hv_mul]
  have hsq_le : ‖y - x‖ ^ 2 ≤ 0 := by
    have hpos : 0 < 1 / α := one_div_pos.mpr hα
    have hnonpos : -‖y - x‖ ^ 2 ≥ 0 := nonneg_of_mul_nonneg_right hsum hpos
    linarith
  have hnorm_zero : ‖y - x‖ = 0 := by
    have hnonneg : 0 ≤ ‖y - x‖ ^ 2 := sq_nonneg _
    have hzero_sq : ‖y - x‖ ^ 2 = 0 := le_antisymm hsq_le hnonneg
    exact sq_eq_zero_iff.mp hzero_sq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
