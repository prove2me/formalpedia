-- Prove2me | solution 1 for ApproachRegret.ToApproach.corollary18_lifted_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:23:39.226489+00:00
-- url     : https://prove2.me/submissions/e3bedfb5-a4e8-4285-90c6-70678b4acebe

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace ApproachRegret66f6

open ApproachRegret.ToOLO ApproachRegret.ToApproach

theorem convex_of_cc {d : ℕ} {C : Set (E d)} (hC : IsConvexCone C) : Convex ℝ C := by
  intro z hz w hw a b ha hb _
  exact hC.2 _ (hC.1 a ha z hz) _ (hC.1 b hb w hw)

theorem closure_smul_mem {d : ℕ} {C : Set (E d)} (hC : IsConvexCone C) {α : ℝ} (hα : 0 ≤ α)
    {z : E d} (hz : z ∈ closure C) : α • z ∈ closure C :=
  map_mem_closure (continuous_const_smul α) hz (fun w hw => hC.1 α hα w hw)

theorem upper {d : ℕ} {C : Set (E d)} (hCne : C.Nonempty) (x θ : E d)
    (hθ : θ ∈ polar C) (hθn : θ ∈ Metric.closedBall (0 : E d) 1) :
    ⟪θ, x⟫ ≤ Metric.infDist x C := by
  rw [Metric.le_infDist hCne]
  intro y hy
  have h1 : ⟪θ, y⟫ ≤ 0 := hθ y hy
  have h2 : ⟪θ, x - y⟫ ≤ ‖θ‖ * ‖x - y‖ := real_inner_le_norm θ (x - y)
  have h3 : ‖θ‖ ≤ 1 := by simpa using hθn
  have h4 : ⟪θ, x - y⟫ = ⟪θ, x⟫ - ⟪θ, y⟫ := inner_sub_right θ x y
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y), norm_nonneg θ]

end ApproachRegret66f6

theorem AR64aa_lemma13 {d : ℕ} (C : Set (ApproachRegret.ToOLO.E d)) (hC : ApproachRegret.ToApproach.IsConvexCone C) (hCne : C.Nonempty)
    (x : ApproachRegret.ToOLO.E d) :
    IsGreatest ((fun θ : ApproachRegret.ToOLO.E d => ⟪θ, x⟫) '' (ApproachRegret.ToOLO.polar C ∩ Metric.closedBall 0 1))
      (Metric.infDist x C) := by
  set K := closure C with hK
  have hKc : Convex ℝ K := (ApproachRegret66f6.convex_of_cc hC).closure
  have hKne : K.Nonempty := hCne.closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKc x
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hKc hpK).1 hp
  -- ⟪x - p, p⟫ = 0
  have h0 : (0 : ApproachRegret.ToOLO.E d) ∈ K := by
    obtain ⟨c, hc⟩ := hCne
    have := ApproachRegret66f6.closure_smul_mem hC (le_refl 0) (subset_closure hc)
    simpa using this
  have h2p : (2 : ℝ) • p ∈ K := ApproachRegret66f6.closure_smul_mem hC (by norm_num) hpK
  have hA := hvar 0 h0
  have hB := hvar _ h2p
  have hpp : ⟪x - p, p⟫ = 0 := by
    have e1 : (0 : ApproachRegret.ToOLO.E d) - p = -p := by simp
    have e2 : (2 : ℝ) • p - p = p := by rw [two_smul]; abel
    rw [e1, inner_neg_right] at hA
    rw [e2] at hB
    linarith
  -- x - p is in the polar
  have hpol : ∀ z ∈ C, ⟪x - p, z⟫ ≤ 0 := by
    intro z hz
    have hm : (2 : ℝ) • ((1/2 : ℝ) • p + (1/2 : ℝ) • z) ∈ K :=
      ApproachRegret66f6.closure_smul_mem hC (by norm_num)
        (hKc hpK (subset_closure hz) (by norm_num) (by norm_num) (by norm_num))
    have e : (2 : ℝ) • ((1/2 : ℝ) • p + (1/2 : ℝ) • z) - p = z := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    have := hvar _ hm
    rwa [e] at this
  set v := x - p with hv
  set θ := ‖v‖⁻¹ • v with hθ
  have hθpol : θ ∈ ApproachRegret.ToOLO.polar C := by
    intro z hz
    show ⟪‖v‖⁻¹ • v, z⟫ ≤ 0
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) (hpol z hz)
  have hθball : θ ∈ Metric.closedBall (0 : ApproachRegret.ToOLO.E d) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hθ, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖v‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hθx : ⟪θ, x⟫ = ‖v‖ := by
    have hx : x = v + p := by rw [hv]; abel
    rw [hθ, real_inner_smul_left]
    conv_lhs => rw [hx]
    rw [inner_add_right, hpp, add_zero, real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖v‖ 0 with h | h
    · rw [h]; simp
    · field_simp
  have hup := ApproachRegret66f6.upper hCne x θ hθpol hθball
  have hlow : Metric.infDist x C ≤ ‖v‖ := by
    rw [← Metric.infDist_closure, ← hK, hv, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hpK
  refine ⟨⟨θ, ⟨hθpol, hθball⟩, ?_⟩, ?_⟩
  · show ⟪θ, x⟫ = Metric.infDist x C
    linarith
  · rintro r ⟨φ, ⟨hφp, hφb⟩, rfl⟩
    exact ApproachRegret66f6.upper hCne x φ hφp hφb

namespace AR64aa

open ApproachRegret.ToOLO ApproachRegret.ToApproach

theorem lift_zero_apply {d : ℕ} (a : ℝ) (v : E d) : lift a v 0 = a := rfl
theorem lift_succ_apply {d : ℕ} (a : ℝ) (v : E d) (j : Fin d) : lift a v j.succ = v j := rfl

theorem lift_ext {d : ℕ} {z w : E (d + 1)} (h0 : z 0 = w 0)
    (hs : ∀ j : Fin d, z j.succ = w j.succ) : z = w := by
  ext i
  induction i using Fin.cases with
  | zero => exact h0
  | succ j => exact hs j

theorem lift_add {d : ℕ} (a b : ℝ) (v w : E d) : lift (a + b) (v + w) = lift a v + lift b w :=
  lift_ext (by simp only [PiLp.add_apply, lift_zero_apply])
    (fun j => by simp only [PiLp.add_apply, lift_succ_apply])

theorem lift_sub {d : ℕ} (a b : ℝ) (v w : E d) : lift a v - lift b w = lift (a - b) (v - w) :=
  lift_ext (by simp only [PiLp.sub_apply, lift_zero_apply])
    (fun j => by simp only [PiLp.sub_apply, lift_succ_apply])

theorem lift_smul {d : ℕ} (c a : ℝ) (v : E d) : c • lift a v = lift (c * a) (c • v) :=
  lift_ext (by simp only [PiLp.smul_apply, lift_zero_apply, smul_eq_mul])
    (fun j => by simp only [PiLp.smul_apply, lift_succ_apply, smul_eq_mul])

theorem lift_zero {d : ℕ} : lift (0 : ℝ) (0 : E d) = 0 :=
  lift_ext (by simp only [PiLp.zero_apply, lift_zero_apply])
    (fun j => by simp only [PiLp.zero_apply, lift_succ_apply])

theorem norm_sq_lift {d : ℕ} (a : ℝ) (v : E d) : ‖lift a v‖ ^ 2 = a ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [lift_zero_apply, lift_succ_apply, Real.norm_eq_abs, sq_abs]

theorem sum_lift {d : ℕ} (κ : ℝ) (g : ℕ → E d) (s : Finset ℕ) :
    ∑ t ∈ s, lift κ (g t) = lift ((s.card : ℝ) * κ) (∑ t ∈ s, g t) := by
  induction s using Finset.induction_on with
  | empty => simp [lift_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih,
      ← lift_add]
    congr 1
    push_cast
    ring

theorem avgPayoff_lifted {n m d : ℕ} (κ : ℝ) (u : E n → E m → E d) (x : ℕ → E n)
    (y : ℕ → E m) (T : ℕ) (hT : 1 ≤ T) :
    avgPayoff (liftedPayoff κ u) x y T = lift κ (avgPayoff u x y T) := by
  unfold avgPayoff liftedPayoff
  rw [sum_lift, Nat.card_Icc, lift_smul]
  have hT' : (T : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  congr 1
  rw [Nat.add_sub_cancel]
  field_simp

theorem norm_le_setNorm {d : ℕ} {S : Set (E d)} (hS : IsCompact S) {s : E d} (hs : s ∈ S) :
    ‖s‖ ≤ setNorm S :=
  le_csSup (hS.image continuous_norm).bddAbove (Set.mem_image_of_mem _ hs)

/-- Lemma 14, second half, for every point. -/
theorem lemma14b {d : ℕ} (K : Set (E d)) (hKc : IsCompact K) (hKne : K.Nonempty) (x : E d) :
    Metric.infDist x K ≤ 2 * Metric.infDist (lift (setNorm K) x) (cone (lift (setNorm K) '' K)) := by
  set κ := setNorm K with hκ
  obtain ⟨s0, hs0⟩ := hKne
  have hne : (cone (lift κ '' K)).Nonempty :=
    ⟨lift κ s0, 1, zero_le_one, lift κ s0, Set.mem_image_of_mem _ hs0, (one_smul ℝ _).symm⟩
  have key : Metric.infDist x K / 2 ≤ Metric.infDist (lift κ x) (cone (lift κ '' K)) := by
    rw [Metric.le_infDist hne]
    rintro z ⟨α, hα, _, ⟨s, hs, rfl⟩, rfl⟩
    have hsκ : ‖s‖ ≤ κ := norm_le_setNorm hKc hs
    have hκ0 : 0 ≤ κ := le_trans (norm_nonneg s) hsκ
    rw [dist_eq_norm, lift_smul, lift_sub]
    set D := ‖lift (κ - α * κ) (x - α • s)‖ with hD
    have hD0 : 0 ≤ D := norm_nonneg _
    have hD2 : D ^ 2 = (κ - α * κ) ^ 2 + ‖x - α • s‖ ^ 2 := norm_sq_lift _ _
    have hA : ‖x - α • s‖ ≤ D := by
      have h := Real.sqrt_le_sqrt (show ‖x - α • s‖ ^ 2 ≤ D ^ 2 by nlinarith [sq_nonneg (κ - α * κ)])
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hD0] at h
    have hB : |κ - α * κ| ≤ D := by
      have h := Real.sqrt_le_sqrt (show (κ - α * κ) ^ 2 ≤ D ^ 2 by nlinarith [sq_nonneg ‖x - α • s‖])
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hD0] at h
    have hdist : Metric.infDist x K ≤ ‖x - s‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hs
    have htri : ‖x - s‖ ≤ ‖x - α • s‖ + ‖α • s - s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hsm : ‖α • s - s‖ = |α - 1| * ‖s‖ := by
      rw [show α • s - s = (α - 1) • s by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
    have hκB : |κ - α * κ| = |α - 1| * κ := by
      rw [show κ - α * κ = (1 - α) * κ by ring, abs_mul, abs_of_nonneg hκ0, abs_sub_comm]
    have h3 : |α - 1| * ‖s‖ ≤ |α - 1| * κ := mul_le_mul_of_nonneg_left hsκ (abs_nonneg _)
    linarith
  linarith

/-- The cone rate (Theorem 17) for a nonempty convex cone, without closedness. -/
theorem cone_rate {n m D : ℕ} (Y : Set (E m)) (u : E n → E m → E D) (C : Set (E D))
    (hC : IsConvexCone C) (hCne : C.Nonempty) (O : E D → ℝ → E n) (X : Set (E n))
    (hO : IsValidOracle X Y u C O)
    (L : (t : ℕ) → (Fin t → E D) → E D)
    (hL : ∀ t h, L t h ∈ polar C ∩ Metric.closedBall 0 1)
    (y : ℕ → E m) (T : ℕ) (hT : 1 ≤ T) (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Y)
    (θ : ℕ → E D) (x : ℕ → E n) (f : ℕ → E D) (hrun : IsAlg2Run u O L y T θ x f) :
    (T : ℝ) * Metric.infDist (avgPayoff u x y T) C ≤ regret (polar C ∩ Metric.closedBall 0 1) θ f T := by
  obtain ⟨⟨φs, hφs, hφx⟩, -⟩ := AR64aa_lemma13 C hC hCne (avgPayoff u x y T)
  have hT' : (T : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  -- each regret term of the algorithm is nonnegative
  have hpos : 0 ≤ ∑ t ∈ Finset.Icc 1 T, ⟪f t, θ t⟫ := by
    apply Finset.sum_nonneg
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨hθt, hxt, hft⟩ := hrun t ht.1 ht.2
    have hθmem : θ t ∈ polar C := by rw [hθt]; exact (hL _ _).1
    have hsub : C ⊆ halfspace (θ t) 0 := fun z hz => hθmem z hz
    have hval := (hO (θ t) 0 hsub).2 (y t) (hy t ht.1 ht.2)
    rw [← hxt] at hval
    have : ⟪θ t, u (x t) (y t)⟫ ≤ 0 := hval
    rw [hft, inner_neg_left, real_inner_comm]
    linarith
  -- the comparator
  have hcomp : ∑ t ∈ Finset.Icc 1 T, ⟪f t, φs⟫ = -((T : ℝ) * Metric.infDist (avgPayoff u x y T) C) := by
    have hsum : ∑ t ∈ Finset.Icc 1 T, ⟪f t, φs⟫ = -⟪φs, ∑ t ∈ Finset.Icc 1 T, u (x t) (y t)⟫ := by
      rw [inner_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_Icc] at ht
      rw [(hrun t ht.1 ht.2).2.2, inner_neg_left, real_inner_comm]
    have hav : ∑ t ∈ Finset.Icc 1 T, u (x t) (y t) = (T : ℝ) • avgPayoff u x y T := by
      unfold avgPayoff
      rw [smul_smul, mul_inv_cancel₀ hT', one_smul]
    have hφx' : ⟪φs, avgPayoff u x y T⟫ = Metric.infDist (avgPayoff u x y T) C := hφx
    rw [hsum, hav, real_inner_smul_right, hφx']
  have hbdd : BddBelow ((fun φ : E D => ∑ t ∈ Finset.Icc 1 T, ⟪f t, φ⟫) '' (polar C ∩ Metric.closedBall 0 1)) := by
    refine BddBelow.mono (Set.image_mono Set.inter_subset_right) ?_
    exact (isCompact_closedBall (0 : E D) 1).bddBelow_image (by fun_prop)
  have hinf := csInf_le hbdd (Set.mem_image_of_mem (fun φ : E D => ∑ t ∈ Finset.Icc 1 T, ⟪f t, φ⟫) hφs)
  unfold regret
  rw [hcomp] at hinf
  linarith

theorem liftedSet_cc {d : ℕ} (S : Set (E d)) (hScvx : Convex ℝ S) :
    IsConvexCone (liftedSet S) := by
  set κ := setNorm S
  refine ⟨?_, ?_⟩
  · rintro β hβ z ⟨α, hα, w, hw, rfl⟩
    exact ⟨β * α, mul_nonneg hβ hα, w, hw, by rw [smul_smul]⟩
  · rintro z ⟨α, hα, _, ⟨s, hs, rfl⟩, rfl⟩ w ⟨β, hβ, _, ⟨s', hs', rfl⟩, rfl⟩
    rcases eq_or_lt_of_le (add_nonneg hα hβ) with h0 | hpos
    · have ha0 : α = 0 := by linarith
      have hb0 : β = 0 := by linarith
      subst ha0; subst hb0
      exact ⟨0, le_refl 0, lift κ s, Set.mem_image_of_mem _ hs, by simp⟩
    · set γ := α + β with hγ
      have hp : (α / γ) • s + (β / γ) • s' ∈ S :=
        hScvx hs hs' (div_nonneg hα hpos.le) (div_nonneg hβ hpos.le) (by
          rw [← add_div]; exact div_self hpos.ne')
      refine ⟨γ, hpos.le, _, Set.mem_image_of_mem _ hp, ?_⟩
      rw [lift_smul, lift_smul, lift_smul, ← lift_add, smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne', hγ, add_mul]

theorem liftedSet_ne {d : ℕ} (S : Set (E d)) (hSne : S.Nonempty) : (liftedSet S).Nonempty := by
  obtain ⟨s, hs⟩ := hSne
  exact ⟨_, 1, zero_le_one, _, Set.mem_image_of_mem _ hs, (one_smul ℝ _).symm⟩

end AR64aa

open ApproachRegret.ToApproach in
theorem solution {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m))
    (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) (S : Set (ApproachRegret.ToOLO.E d)) (hInst : IsBlackwellInstance X Y u S)
    (hScpt : IsCompact S) (hSne : S.Nonempty)
    (O' : ApproachRegret.ToOLO.E (d + 1) → ℝ → ApproachRegret.ToOLO.E n)
    (hO' : IsValidOracle X Y (liftedPayoff (setNorm S) u) (liftedSet S) O')
    (L : (t : ℕ) → (Fin t → ApproachRegret.ToOLO.E (d + 1)) → ApproachRegret.ToOLO.E (d + 1))
    (hL : ∀ t h, L t h ∈ ApproachRegret.ToOLO.polar (liftedSet S) ∩ Metric.closedBall 0 1)
    (y : ℕ → ApproachRegret.ToOLO.E m) (T : ℕ) (hT : 1 ≤ T) (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Y)
    (θ : ℕ → ApproachRegret.ToOLO.E (d + 1)) (x : ℕ → ApproachRegret.ToOLO.E n) (f : ℕ → ApproachRegret.ToOLO.E (d + 1))
    (hrun : IsAlg2Run (liftedPayoff (setNorm S) u) O' L y T θ x f) :
    Metric.infDist (avgPayoff u x y T) S ≤
        2 * Metric.infDist (avgPayoff (liftedPayoff (setNorm S) u) x y T) (liftedSet S) ∧
      2 * Metric.infDist (avgPayoff (liftedPayoff (setNorm S) u) x y T) (liftedSet S) ≤
        2 / T * regret (ApproachRegret.ToOLO.polar (liftedSet S) ∩ Metric.closedBall 0 1) θ f T := by
  refine ⟨?_, ?_⟩
  · rw [AR64aa.avgPayoff_lifted _ _ _ _ _ hT]
    exact AR64aa.lemma14b S hScpt hSne _
  · have h := AR64aa.cone_rate Y _ _ (AR64aa.liftedSet_cc S hInst.2.2.2.2.2.1)
      (AR64aa.liftedSet_ne S hSne) O' X hO' L hL y T hT hy θ x f hrun
    have hTpos : (0 : ℝ) < T := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hTpos]
    linarith
