-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.eq_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:03:40.725985+00:00
-- url     : https://prove2.me/submissions/e75abb92-7dcf-4020-a25b-601f74bda558

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting
import Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_2_2
import Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_4
import Theorems.Thm_AggDiscountStopping_OneBarrier_harris_fkg_chebyshev

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

namespace ADSAux

lemma ae_nonneg (M : Model) (hM : M.Valid) : ∀ᵐ r ∂M.F, 0 ≤ r := by
  rw [ae_iff]
  have : {r : ℝ | ¬ 0 ≤ r} = Iio 0 := by ext r; simp
  rw [this]; exact hM.F_nonneg

/-- A continuous path started strictly above `c ≥ 0` enters `[0, c]` exactly at `c`. -/
lemma entry_point {Ω : Type*} [MeasurableSpace Ω] (D : Diffusion Ω) (hD : D.Valid)
    (c x : ℝ) (hc : 0 ≤ c) (hcx : c < x) (ω : Ω) (hen : D.enters x (Icc 0 c) ω) :
    D.X x (D.entryTime x (Icc 0 c) ω) ω = c := by
  set f : ℝ≥0 → ℝ := fun t => D.X x t ω with hf
  have hfc : Continuous f := hD.cont x ω
  have hf0 : f 0 = x := hD.start x ω
  set S : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ Icc 0 c} with hS
  have hne : S.Nonempty := hen
  have hτ : D.entryTime x (Icc 0 c) ω = sInf S := rfl
  rw [hτ]
  have hcl : IsClosed {t : ℝ≥0 | f t ∈ Icc 0 c} := isClosed_Icc.preimage hfc
  have hmem : sInf S ∈ {t : ℝ≥0 | f t ∈ Icc 0 c} := by
    have h1 := csInf_mem_closure hne (OrderBot.bddBelow S)
    have h2 : closure S ⊆ {t : ℝ≥0 | f t ∈ Icc 0 c} :=
      closure_minimal (fun t ht => ht.2) hcl
    exact h2 h1
  have hle : f (sInf S) ≤ c := hmem.2
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hivt := intermediate_value_Icc' (zero_le : (0:ℝ≥0) ≤ sInf S) hfc.continuousOn
  have hcmem : c ∈ Icc (f (sInf S)) (f 0) := ⟨hlt.le, by rw [hf0]; exact hcx.le⟩
  obtain ⟨s, hs, hfs⟩ := hivt hcmem
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; rw [hf0] at hfs; linarith
    · exact h
  have hsS : s ∈ S := ⟨hs0, by show f s ∈ Icc 0 c; rw [hfs]; exact ⟨hc, le_rfl⟩⟩
  have := csInf_le (OrderBot.bddBelow S) hsS
  have hseq : s = sInf S := le_antisymm hs.2 this
  rw [← hseq] at hlt
  exact absurd hfs (ne_of_lt hlt)

/-- Entering `[0, c]` from above is the same as hitting `c`, at the same time. -/
lemma entry_eq {Ω : Type*} [MeasurableSpace Ω] (D : Diffusion Ω) (hD : D.Valid)
    (c x : ℝ) (hc : 0 ≤ c) (hcx : c < x) (ω : Ω) :
    (D.enters x (Icc 0 c) ω ↔ D.enters x {c} ω) ∧
      (D.enters x (Icc 0 c) ω → D.entryTime x (Icc 0 c) ω = D.entryTime x {c} ω) := by
  have key : D.enters x (Icc 0 c) ω →
      0 < D.entryTime x (Icc 0 c) ω ∧ D.X x (D.entryTime x (Icc 0 c) ω) ω = c := by
    intro hen
    have hX := entry_point D hD c x hc hcx ω hen
    refine ⟨?_, hX⟩
    rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ D.entryTime x (Icc 0 c) ω) with h | h
    · rw [← h, hD.start] at hX; linarith
    · exact h
  have hsub : {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ ({c} : Set ℝ)} ⊆
      {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ Icc 0 c} := by
    rintro t ⟨ht, hXt⟩
    refine ⟨ht, ?_⟩
    rw [mem_singleton_iff] at hXt
    rw [hXt]; exact ⟨hc, le_rfl⟩
  refine ⟨⟨fun hen => ?_, fun hen => ?_⟩, fun hen => ?_⟩
  · obtain ⟨h1, h2⟩ := key hen
    exact ⟨_, h1, by rw [h2]; rfl⟩
  · obtain ⟨t, ht, hXt⟩ := hen
    exact ⟨t, hsub ⟨ht, hXt⟩⟩
  · obtain ⟨h1, h2⟩ := key hen
    have hen' : D.enters x {c} ω := ⟨_, h1, by rw [h2]; rfl⟩
    apply le_antisymm
    · exact csInf_le_csInf (OrderBot.bddBelow _) hen' hsub
    · exact csInf_le (OrderBot.bddBelow _) ⟨h1, by rw [h2]; rfl⟩

lemma disc_eq {Ω : Type*} [MeasurableSpace Ω] (M : Model) (D : Diffusion Ω) (hD : D.Valid)
    (c x : ℝ) (hc : 0 ≤ c) (hcx : c < x) (r : ℝ) (ω : Ω) :
    discPayoff M D r x (Icc 0 c) ω = M.g c * D.hitDisc r c x ω := by
  obtain ⟨hiff, htime⟩ := entry_eq D hD c x hc hcx ω
  unfold discPayoff Diffusion.hitDisc
  by_cases hen : D.enters x (Icc 0 c) ω
  · rw [if_pos hen, if_pos (hiff.1 hen), entry_point D hD c x hc hcx ω hen, htime hen]
    ring
  · rw [if_neg hen, if_neg (fun h => hen (hiff.2 h))]
    ring

lemma q_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ) (r : ℝ) (hr : 0 ≤ r) (c x : ℝ) (hc : 0 < c) (hcx : c ≤ x) :
    0 < φ r x / φ r c ∧ φ r x / φ r c ≤ 1 := by
  have h1 := (hφ.sol r hr).pos c hc
  have h2 := (hφ.sol r hr).pos x (lt_of_lt_of_le hc hcx)
  have h3 : φ r x ≤ φ r c :=
    (hφ.sol r hr).anti (show c ∈ Ioi (0:ℝ) from hc) (show x ∈ Ioi (0:ℝ) from lt_of_lt_of_le hc hcx) hcx
  exact ⟨div_pos h2 h1, (div_le_one h1).mpr h3⟩

lemma q_anti {Ω : Type*} [MeasurableSpace Ω] (M : Model) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ) (c x : ℝ) (hc : 0 < c) (hcx : c ≤ x) :
    AntitoneOn (fun r => φ r x / φ r c) (Ici 0) := by
  intro r1 hr1 r2 hr2 h12
  simp only
  rw [← hφ.laplace r1 hr1 c x hc hcx, ← hφ.laplace r2 hr2 c x hc hcx]
  have hint : ∀ r, 0 ≤ r → Integrable (D.hitDisc r c x) D.P := by
    intro r hr
    apply Integrable.of_integral_ne_zero
    have := hφ.laplace r hr c x hc hcx
    unfold Diffusion.hitLaplace at this
    rw [this]
    exact (q_pos M D φ hφ r hr c x hc hcx).1.ne'
  unfold Diffusion.hitLaplace
  apply integral_mono (hint r2 hr2) (hint r1 hr1)
  intro ω
  unfold Diffusion.hitDisc
  split_ifs
  · apply Real.exp_le_exp.mpr
    have := (D.entryTime x {c} ω).2
    have h1 : (0:ℝ) ≤ r1 := hr1
    nlinarith
  · exact le_rfl

lemma aesm_of_antiOn (M : Model) (hM : M.Valid) (u : ℝ → ℝ) (hu : AntitoneOn u (Ici 0)) :
    AEStronglyMeasurable u M.F := by
  set v : ℝ → ℝ := fun r => u (max r 0) with hv
  have hva : Antitone v := by
    intro r1 r2 h
    exact hu (mem_Ici.mpr (le_max_right r1 0))
      (mem_Ici.mpr (le_max_right r2 0)) (max_le_max h le_rfl)
  refine hva.measurable.aestronglyMeasurable.congr ?_
  filter_upwards [ae_nonneg M hM] with r hr
  simp [hv, max_eq_left hr]

/-- `ϕ′ > 0` on `(0, ∞)` under C-(iii). -/
lemma att_facts (M : Model) (hCiii : M.CondIII) :
    (∀ y, 0 < y → DifferentiableAt ℝ M.att y) ∧ (∀ c, 0 < c → 0 < deriv M.att c) := by
  obtain ⟨hattc, hattd, hattsm, hattm⟩ := hCiii
  have hattdiff : ∀ y, 0 < y → DifferentiableAt ℝ M.att y := fun y hy =>
    ((hattd.differentiableOn one_ne_zero) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
  refine ⟨hattdiff, ?_⟩
  intro c hc
  by_contra hle
  push Not at hle
  have hnp : ∀ y ∈ Ioo (c / 2) c, deriv M.att y ≤ 0 := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have h1 : deriv M.att y * y ≤ deriv M.att c * c :=
      hattm (show y ∈ Ioi (0:ℝ) from hy0) (show c ∈ Ioi (0:ℝ) from hc) hy.2.le
    have h2 : deriv M.att c * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hc.le
    by_contra hpos
    push Not at hpos
    have : 0 < deriv M.att y * y := mul_pos hpos hy0
    linarith
  have hanti : AntitoneOn M.att (Icc (c / 2) c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact hattc.mono (fun y hy => show (0:ℝ) ≤ y by linarith [hy.1])
    · intro y hy
      rw [interior_Icc] at hy
      exact (hattdiff y (by linarith [hy.1])).differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact hnp y hy
  have hlt := hattsm (show c / 2 ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith)
    (show c ∈ Ici (0:ℝ) from hc.le) (by linarith : c / 2 < c)
  have hge := hanti (show c / 2 ∈ Icc (c / 2) c from ⟨le_rfl, by linarith⟩)
    (show c ∈ Icc (c / 2) c from ⟨by linarith, le_rfl⟩) (by linarith : c / 2 ≤ c)
  linarith

/-- The value of a one-barrier region `[0, c]` seen from `x ≥ c`. -/
lemma J_eq {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid) (D : Diffusion Ω)
    (hD : D.Valid) (φ : ℝ → ℝ → ℝ) (hφ : IsLaplaceRep M D φ) (c x : ℝ) (hc : 0 < c)
    (hcx : c ≤ x) (hcK : c ≤ M.K) :
    J M D x (Icc 0 c) = ∫ r, M.att ((M.K - c) * (φ r x / φ r c)) ∂M.F := by
  have hgc : M.g c = M.K - c := by unfold Model.g; exact max_eq_left (by linarith)
  rcases eq_or_lt_of_le hcx with h | h
  · subst h
    rw [(lemma_2_2 M hM D hD φ hφ c hc c hc.le le_rfl).2, hgc]
    have hF := hM.F_prob
    have : (fun r => M.att ((M.K - c) * (φ r c / φ r c))) =ᵐ[M.F] fun _ => M.att (M.K - c) := by
      filter_upwards [ae_nonneg M hM] with r hr
      rw [div_self ((hφ.sol r hr).pos c hc).ne', mul_one]
    rw [integral_congr_ae this]
    simp
  · unfold J
    apply integral_congr_ae
    filter_upwards [ae_nonneg M hM] with r hr
    have : (fun ω => discPayoff M D r x (Icc 0 c) ω) = fun ω => M.g c * D.hitDisc r c x ω := by
      funext ω; exact disc_eq M D hD c x hc.le h r ω
    simp only [this]
    rw [integral_const_mul]
    have := hφ.laplace r hr c x hc hcx
    unfold Diffusion.hitLaplace at this
    rw [this, hgc]

/-- Bounds and measurability of the integrand `r ↦ ϕ((K − c) φ_r(x)/φ_r(c))`. -/
lemma integrand_facts {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCiii : M.CondIII) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ) (hφ : IsLaplaceRep M D φ)
    (c x : ℝ) (hc : 0 < c) (hcx : c ≤ x) (hcK : c ≤ M.K) :
    AEStronglyMeasurable (fun r => M.att ((M.K - c) * (φ r x / φ r c))) M.F ∧
      Integrable (fun r => M.att ((M.K - c) * (φ r x / φ r c))) M.F := by
  obtain ⟨hattc, hattd, hattsm, hattm⟩ := hCiii
  have hmono : MonotoneOn M.att (Ici 0) := hattsm.monotoneOn
  have hKc : 0 ≤ M.K - c := by linarith
  have hmeas : AEStronglyMeasurable (fun r => M.att ((M.K - c) * (φ r x / φ r c))) M.F := by
    apply aesm_of_antiOn M hM
    intro r1 hr1 r2 hr2 h12
    have hq := q_anti M D φ hφ c x hc hcx hr1 hr2 h12
    have p1 := (q_pos M D φ hφ r1 hr1 c x hc hcx).1
    have p2 := (q_pos M D φ hφ r2 hr2 c x hc hcx).1
    simp only at hq ⊢
    apply hmono (show (M.K - c) * (φ r2 x / φ r2 c) ∈ Ici (0:ℝ) from mul_nonneg hKc p2.le)
      (show (M.K - c) * (φ r1 x / φ r1 c) ∈ Ici (0:ℝ) from mul_nonneg hKc p1.le)
    exact mul_le_mul_of_nonneg_left hq hKc
  refine ⟨hmeas, ?_⟩
  have hF := hM.F_prob
  refine Integrable.of_bound hmeas (max |M.att 0| |M.att M.K|) ?_
  filter_upwards [ae_nonneg M hM] with r hr
  obtain ⟨p1, p2⟩ := q_pos M D φ hφ r hr c x hc hcx
  have hy0 : 0 ≤ (M.K - c) * (φ r x / φ r c) := mul_nonneg hKc p1.le
  have hyK : (M.K - c) * (φ r x / φ r c) ≤ M.K := by
    have : (M.K - c) * (φ r x / φ r c) ≤ (M.K - c) * 1 := mul_le_mul_of_nonneg_left p2 hKc
    linarith
  have l1 := hmono (mem_Ici.mpr (le_refl (0:ℝ))) (show _ ∈ Ici (0:ℝ) from hy0) hy0
  have l2 := hmono (show _ ∈ Ici (0:ℝ) from hy0) (show M.K ∈ Ici (0:ℝ) from hM.K_pos.le) hyK
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (M.att 0)
    have := le_max_left |M.att 0| |M.att M.K|
    linarith
  · have := le_abs_self (M.att M.K)
    have := le_max_right |M.att 0| |M.att M.K|
    linarith

/-- `x ↦ φ_r(x)` is differentiable on `(0, ∞)` with nonpositive derivative. -/
lemma phi_deriv {Ω : Type*} [MeasurableSpace Ω] (M : Model) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ) (r : ℝ) (hr : 0 ≤ r) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (φ r) (deriv (φ r) x) x ∧ deriv (φ r) x ≤ 0 := by
  have hs := (hφ.sol r hr).smooth
  have hd : DifferentiableAt ℝ (φ r) x :=
    ((hs.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
  refine ⟨hd.hasDerivAt, ?_⟩
  have := (hφ.sol r hr).anti.derivWithin_nonpos (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioi hx] at this

end ADSAux

namespace ADSAux

lemma arg_mem {Ω : Type*} [MeasurableSpace Ω] (M : Model) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ) (r : ℝ) (hr : 0 ≤ r) (c x : ℝ) (hc : 0 < c) (hcx : c ≤ x)
    (hcK : c ≤ M.K) : (M.K - c) * (φ r x / φ r c) ∈ Icc 0 M.K := by
  obtain ⟨p1, p2⟩ := q_pos M D φ hφ r hr c x hc hcx
  have hKc : 0 ≤ M.K - c := by linarith
  refine ⟨mul_nonneg hKc p1.le, ?_⟩
  have : (M.K - c) * (φ r x / φ r c) ≤ (M.K - c) * 1 := mul_le_mul_of_nonneg_left p2 hKc
  linarith

lemma att_bound (M : Model) (hM : M.Valid) (hCiii : M.CondIII) (y : ℝ) (hy : y ∈ Icc 0 M.K) :
    ‖M.att y‖ ≤ max |M.att 0| |M.att M.K| := by
  have hmono : MonotoneOn M.att (Ici 0) := hCiii.2.2.1.monotoneOn
  have l1 := hmono (mem_Ici.mpr (le_refl (0:ℝ))) (show y ∈ Ici (0:ℝ) from hy.1) hy.1
  have l2 := hmono (show y ∈ Ici (0:ℝ) from hy.1) (show M.K ∈ Ici (0:ℝ) from hM.K_pos.le) hy.2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (M.att 0)
    have := le_max_left |M.att 0| |M.att M.K|
    linarith
  · have := le_abs_self (M.att M.K)
    have := le_max_right |M.att 0| |M.att M.K|
    linarith

end ADSAux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (hCiii : M.CondIII) (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ)
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F)
    (aStar : ℝ) (haStar0 : 0 ≤ aStar) (haStarK : aStar < M.K)
    (haStar : ∀ a ∈ Ioo 0 M.K, (0 < G M φ a + 1 / (M.K - a) ↔ aStar < a)) :
    ∀ a b x, 0 < a → aStar ≤ a → a < b → b ≤ x → b ≤ M.K →
      J M D x (Icc 0 b) < J M D x (Icc 0 a) := by
  intro a b x ha haS hab hbx hbK
  have hF := hM.F_prob
  obtain ⟨hattdiff, hattpos⟩ := ADSAux.att_facts M hCiii
  have hattm := hCiii.2.2.2
  have hattc := hCiii.1
  have hx : 0 < x := by linarith
  have hK := hM.K_pos
  set L : ℝ → ℝ := fun c => ∫ r, M.att ((M.K - c) * (φ r x / φ r c)) ∂M.F with hL
  rw [ADSAux.J_eq M hM D hD φ hφ b x (by linarith) hbx hbK,
    ADSAux.J_eq M hM D hD φ hφ a x ha (by linarith) (by linarith)]
  show L b < L a
  set f : ℝ → ℝ → ℝ := fun c r =>
    deriv M.att ((M.K - c) * (φ r x / φ r c)) * ((M.K - c) * (φ r x / φ r c)) with hf
  set h : ℝ → ℝ → ℝ := fun c r => 1 / (M.K - c) + deriv (φ r) c / φ r c with hh
  set B : ℝ := deriv M.att M.K * M.K with hB
  have hB0 : 0 ≤ B := (mul_pos (hattpos _ hK) hK).le
  -- the derivative of each integrand with respect to the barrier
  have hder : ∀ r, 0 ≤ r → ∀ c, 0 < c → c < M.K →
      HasDerivAt (fun c => M.att ((M.K - c) * (φ r x / φ r c))) (-(f c r * h c r)) c := by
    intro r hr c hc hcK
    have hpc := (hφ.sol r hr).pos c hc
    have hpx := (hφ.sol r hr).pos x hx
    have hKc : 0 < M.K - c := by linarith
    have h1 : HasDerivAt (fun c => M.K - c) (-1) c := by
      simpa using (hasDerivAt_id c).const_sub M.K
    have h2 : HasDerivAt (fun c => φ r x / φ r c)
        ((0 * φ r c - φ r x * deriv (φ r) c) / (φ r c) ^ 2) c :=
      (hasDerivAt_const c (φ r x)).div (ADSAux.phi_deriv M D φ hφ r hr c hc).1 hpc.ne'
    have hy : 0 < (M.K - c) * (φ r x / φ r c) := mul_pos hKc (div_pos hpx hpc)
    have := (hattdiff _ hy).hasDerivAt.comp c (h1.mul h2)
    refine HasDerivAt.congr_deriv this ?_
    simp only [hf, hh]
    field_simp
    ring
  -- bounds on f
  have hfb : ∀ r, 0 ≤ r → ∀ c, 0 < c → c < M.K → c ≤ x → 0 < f c r ∧ f c r ≤ B := by
    intro r hr c hc hcK hcx
    obtain ⟨q1, q2⟩ := ADSAux.q_pos M D φ hφ r hr c x hc hcx
    have hKc : 0 < M.K - c := by linarith
    have hy0 : 0 < (M.K - c) * (φ r x / φ r c) := mul_pos hKc q1
    have hyK : (M.K - c) * (φ r x / φ r c) ≤ M.K := by
      have : (M.K - c) * (φ r x / φ r c) ≤ (M.K - c) * 1 := mul_le_mul_of_nonneg_left q2 hKc.le
      linarith
    exact ⟨mul_pos (hattpos _ hy0) hy0,
      hattm (show _ ∈ Ioi (0:ℝ) from hy0) (show M.K ∈ Ioi (0:ℝ) from hK) hyK⟩
  have hfanti : ∀ c, 0 < c → c < M.K → c ≤ x → AntitoneOn (f c) (Ici 0) := by
    intro c hc hcK hcx r1 hr1 r2 hr2 h12
    have hq := ADSAux.q_anti M D φ hφ c x hc hcx hr1 hr2 h12
    have p1 := (ADSAux.q_pos M D φ hφ r1 hr1 c x hc hcx).1
    have p2 := (ADSAux.q_pos M D φ hφ r2 hr2 c x hc hcx).1
    have hKc : 0 < M.K - c := by linarith
    simp only at hq
    exact hattm (show (M.K - c) * (φ r2 x / φ r2 c) ∈ Ioi (0:ℝ) from mul_pos hKc p2)
      (show (M.K - c) * (φ r1 x / φ r1 c) ∈ Ioi (0:ℝ) from mul_pos hKc p1)
      (mul_le_mul_of_nonneg_left hq hKc.le)
  have hfmeas : ∀ c, 0 < c → c < M.K → c ≤ x → AEStronglyMeasurable (f c) M.F :=
    fun c hc hcK hcx => ADSAux.aesm_of_antiOn M hM _ (hfanti c hc hcK hcx)
  have hfint : ∀ c, 0 < c → c < M.K → c ≤ x → Integrable (f c) M.F := by
    intro c hc hcK hcx
    refine Integrable.of_bound (hfmeas c hc hcK hcx) B ?_
    filter_upwards [ADSAux.ae_nonneg M hM] with r hr
    obtain ⟨h1, h2⟩ := hfb r hr c hc hcK hcx
    rw [Real.norm_eq_abs, abs_of_pos h1]; exact h2
  have hhint : ∀ c, 0 < c → Integrable (h c) M.F := fun c hc =>
    (integrable_const _).add (hG c hc)
  -- the log-derivative `φ′_r(c)/φ_r(c)` is antitone in `r`
  have hlogd : ∀ c, 0 < c → AntitoneOn (fun r => deriv (φ r) c / φ r c) (Ici 0) := by
    intro c hc r1 hr1 r2 hr2 h12
    have lim : ∀ r, 0 ≤ r → Tendsto (fun y => Real.log (φ r y / φ r c) / (y - c)) (𝓝[>] c)
        (𝓝 (deriv (φ r) c / φ r c)) := by
      intro r hr
      have hpc := (hφ.sol r hr).pos c hc
      have hd : HasDerivAt (fun y => Real.log (φ r y)) (deriv (φ r) c / φ r c) c :=
        (ADSAux.phi_deriv M D φ hφ r hr c hc).1.log hpc.ne'
      have := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono _ (fun y (hy : c < y) => ne_of_gt hy))
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y (hy : c < y)
      rw [slope_def_field, Real.log_div ((hφ.sol r hr).pos y (by linarith)).ne' hpc.ne']
    apply le_of_tendsto_of_tendsto (lim r2 hr2) (lim r1 hr1)
    filter_upwards [self_mem_nhdsWithin] with y (hy : c < y)
    have hq := ADSAux.q_anti M D φ hφ c y hc hy.le hr1 hr2 h12
    have p2 := (ADSAux.q_pos M D φ hφ r2 hr2 c y hc hy.le).1
    simp only at hq
    exact div_le_div_of_nonneg_right (Real.log_le_log p2 hq) (by linarith)
  -- the integral of `f h` is positive on `(a, b)`
  have hpos : ∀ c ∈ Ioo a b, 0 < ∫ r, f c r * h c r ∂M.F := by
    intro c hc
    have hc0 : 0 < c := by linarith [hc.1]
    have hcK : c < M.K := by linarith [hc.2]
    have hcx : c ≤ x := by linarith [hc.2]
    have hS : M.F (Ici 0)ᶜ = 0 := by rw [compl_Ici]; exact hM.F_nonneg
    have hhm : MonotoneOn (fun r => -h c r) (Ici 0) := by
      intro r1 hr1 r2 hr2 h12
      have := hlogd c hc0 hr1 hr2 h12
      simp only [hh] at this ⊢
      linarith
    have hfhi : Integrable (fun r => f c r * -h c r) M.F := by
      refine (hhint c hc0).neg.bdd_mul (c := B) (hfmeas c hc0 hcK hcx) ?_
      filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      obtain ⟨h1, h2⟩ := hfb r hr c hc0 hcK hcx
      rw [Real.norm_eq_abs, abs_of_pos h1]; exact h2
    have cheb := harris_fkg_chebyshev M.F (Ici 0) hS (f c) (fun r => -h c r)
      (hfanti c hc0 hcK hcx) hhm (hfint c hc0 hcK hcx) (hhint c hc0).neg hfhi
    have e1 : ∫ r, f c r * -h c r ∂M.F = -∫ r, f c r * h c r ∂M.F := by
      rw [← integral_neg]; congr 1; funext r; ring
    have e2 : ∫ r, -h c r ∂M.F = -(G M φ c + 1 / (M.K - c)) := by
      rw [integral_neg, hh]
      simp only
      rw [integral_add (integrable_const _) (hG c hc0)]
      simp [G]; ring
    rw [e1, e2] at cheb
    have hGpos : 0 < G M φ c + 1 / (M.K - c) := (haStar c ⟨hc0, hcK⟩).mpr (by linarith [hc.1])
    have hfpos : 0 < ∫ r, f c r ∂M.F := by
      rw [integral_pos_iff_support_of_nonneg_ae]
      · have h1 : M.F (Ici 0) = 1 := (prob_compl_eq_zero_iff measurableSet_Ici).mp hS
        have h2 : Ici (0:ℝ) ⊆ Function.support (f c) := by
          intro r hr
          exact (hfb r hr c hc0 hcK hcx).1.ne'
        calc (0 : ENNReal) < 1 := one_pos
          _ = M.F (Ici 0) := h1.symm
          _ ≤ _ := measure_mono h2
      · filter_upwards [ADSAux.ae_nonneg M hM] with r hr
        exact (hfb r hr c hc0 hcK hcx).1.le
      · exact hfint c hc0 hcK hcx
    nlinarith [mul_pos hfpos hGpos]
  -- differentiation under the integral sign
  have hLder : ∀ c ∈ Ioo a b, HasDerivAt L (-(∫ r, f c r * h c r ∂M.F)) c := by
    intro c0 hc0
    set δ := min (c0 - a) ((b - c0) / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith [hc0.1]) (by linarith [hc0.2])
    have hδ1 := min_le_left (c0 - a) ((b - c0) / 2)
    have hδ2 := min_le_right (c0 - a) ((b - c0) / 2)
    have hc1 : c0 + δ < M.K := by linarith [hc0.2]
    have hball : ∀ c ∈ Metric.ball c0 δ, a < c ∧ c ≤ c0 + δ := by
      intro c hc
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
      exact ⟨by linarith, by linarith⟩
    have hc00 : 0 < c0 := by linarith [hc0.1]
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.F)
      (F := fun c r => M.att ((M.K - c) * (φ r x / φ r c)))
      (F' := fun c r => -(f c r * h c r)) (x₀ := c0)
      (bound := fun r => B * (1 / (M.K - (c0 + δ)) + mtilde (φ r) a))
      (Metric.ball_mem_nhds c0 hδpos) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← integral_neg]; exact key.2
    · filter_upwards [Metric.ball_mem_nhds c0 hδpos] with c hc
      obtain ⟨h1, h2⟩ := hball c hc
      exact (ADSAux.integrand_facts M hM hCiii D φ hφ c x (by linarith) (by linarith)
        (by linarith)).1
    · exact (ADSAux.integrand_facts M hM hCiii D φ hφ c0 x hc00 (by linarith [hc0.2])
        (by linarith)).2
    · exact ((hfmeas c0 hc00 (by linarith) (by linarith [hc0.2])).mul
        (hhint c0 hc00).aestronglyMeasurable).neg
    · filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      intro c hc
      obtain ⟨hac, hcc⟩ := hball c hc
      have hc' : 0 < c := by linarith
      obtain ⟨f1, f2⟩ := hfb r hr c hc' (by linarith) (by linarith)
      have hpc := (hφ.sol r hr).pos c hc'
      have hdn := (ADSAux.phi_deriv M D φ hφ r hr c hc').2
      have hm0 : 0 ≤ mtilde (φ r) c := by unfold mtilde; exact div_nonneg (by linarith) hpc.le
      have hmt := proposition_4_4 M hM hCi hCii1 r hr (φ r) (hφ.sol r hr)
        (show a ∈ Ioi (0:ℝ) from ha) (show c ∈ Ioi (0:ℝ) from hc') hac.le
      have hA : 1 / (M.K - c) ≤ 1 / (M.K - (c0 + δ)) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      have hA0 : 0 < 1 / (M.K - c) := one_div_pos.mpr (by linarith)
      have hhc : h c r = 1 / (M.K - c) - mtilde (φ r) c := by
        simp only [hh, mtilde]; ring
      have habs : |h c r| ≤ 1 / (M.K - (c0 + δ)) + mtilde (φ r) a := by
        rw [hhc, abs_le]; constructor <;> linarith
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos f1]
      exact mul_le_mul f2 habs (abs_nonneg _) hB0
    · have := ((integrable_const (1 / (M.K - (c0 + δ)))).add (hG a ha).neg).const_mul B
      refine this.congr (Eventually.of_forall fun r => ?_)
      simp [mtilde, neg_div, sub_eq_add_neg]
    · filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      intro c hc
      obtain ⟨hac, hcc⟩ := hball c hc
      exact hder r hr c (by linarith) (by linarith)
  -- continuity on `[a, b]`
  have hcont : ContinuousOn L (Icc a b) := by
    apply continuousOn_of_dominated (bound := fun _ => max |M.att 0| |M.att M.K|)
    · intro c hc
      exact (ADSAux.integrand_facts M hM hCiii D φ hφ c x (by linarith [hc.1]) (by linarith [hc.2])
        (by linarith [hc.2])).1
    · intro c hc
      filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      exact ADSAux.att_bound M hM hCiii _ (ADSAux.arg_mem M D φ hφ r hr c x
        (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.2]))
    · exact integrable_const _
    · filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      have hsub : Icc a b ⊆ Ioi 0 := fun c hc => lt_of_lt_of_le ha hc.1
      have hin : ContinuousOn (fun c => (M.K - c) * (φ r x / φ r c)) (Icc a b) :=
        (continuousOn_const.sub continuousOn_id).mul (continuousOn_const.div
          ((hφ.sol r hr).smooth.continuousOn.mono hsub)
          (fun c hc => ((hφ.sol r hr).pos c (hsub hc)).ne'))
      refine hattc.comp hin ?_
      intro c hc
      exact (ADSAux.arg_mem M D φ hφ r hr c x (by linarith [hc.1]) (by linarith [hc.2])
        (by linarith [hc.2])).1
  have hanti : StrictAntiOn L (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont
    intro c hc
    rw [interior_Icc] at hc
    rw [(hLder c hc).deriv]
    linarith [hpos c hc]
  exact hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
