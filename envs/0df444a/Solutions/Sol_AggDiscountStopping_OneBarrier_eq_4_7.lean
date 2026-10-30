-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:01:54.520972+00:00
-- url     : https://prove2.me/submissions/4e5514b6-a606-4070-aace-6ad520279a50

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting
import Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_2_2
import Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_4

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
    (a : ℝ) (ha : 0 < a) (haK : a < M.K) :
    HasDerivWithinAt (fun x => J M D x (Icc 0 a))
      (deriv M.att (M.K - a) * (M.K - a) * G M φ a) (Ici a) a := by
  have hF := hM.F_prob
  have hKa : 0 < M.K - a := by linarith
  obtain ⟨hattdiff, hattpos⟩ := ADSAux.att_facts M hCiii
  have hattm := hCiii.2.2.2
  set Ψ : ℝ → ℝ → ℝ := fun r x => M.att ((M.K - a) * (φ r x / φ r a)) with hΨ
  set Ψ' : ℝ → ℝ → ℝ := fun r x => deriv M.att ((M.K - a) * (φ r x / φ r a)) *
      ((M.K - a) * (deriv (φ r) x / φ r a)) with hΨ'
  set C : ℝ := deriv M.att (M.K - a) * (M.K - a) with hC
  have hC0 : 0 ≤ C := (mul_pos (hattpos _ hKa) hKa).le
  -- the derivative of each integrand
  have hder : ∀ r, 0 ≤ r → ∀ x, 0 < x → HasDerivAt (Ψ r) (Ψ' r x) x := by
    intro r hr x hx
    have hin : HasDerivAt (fun x => (M.K - a) * (φ r x / φ r a))
        ((M.K - a) * (deriv (φ r) x / φ r a)) x :=
      ((ADSAux.phi_deriv M D φ hφ r hr x hx).1.div_const (φ r a)).const_mul (M.K - a)
    have hy : 0 < (M.K - a) * (φ r x / φ r a) :=
      mul_pos hKa (div_pos ((hφ.sol r hr).pos x hx) ((hφ.sol r hr).pos a ha))
    exact (hattdiff _ hy).hasDerivAt.comp x hin
  -- a uniform bound on the derivative to the right of the barrier
  have hbd : ∀ r, 0 ≤ r → ∀ x, a ≤ x → ‖Ψ' r x‖ ≤ C * mtilde (φ r) a := by
    intro r hr x hax
    have hx : 0 < x := lt_of_lt_of_le ha hax
    obtain ⟨q1, q2⟩ := ADSAux.q_pos M D φ hφ r hr a x ha hax
    have hpa := (hφ.sol r hr).pos a ha
    have hpx := (hφ.sol r hr).pos x hx
    have hy0 : 0 < (M.K - a) * (φ r x / φ r a) := mul_pos hKa q1
    have hyK : (M.K - a) * (φ r x / φ r a) ≤ M.K - a := by
      have : (M.K - a) * (φ r x / φ r a) ≤ (M.K - a) * 1 := mul_le_mul_of_nonneg_left q2 hKa.le
      linarith
    have hf1 : deriv M.att ((M.K - a) * (φ r x / φ r a)) * ((M.K - a) * (φ r x / φ r a)) ≤ C :=
      hattm (show _ ∈ Ioi (0:ℝ) from hy0) (show M.K - a ∈ Ioi (0:ℝ) from hKa) hyK
    have hf0 : 0 < deriv M.att ((M.K - a) * (φ r x / φ r a)) * ((M.K - a) * (φ r x / φ r a)) :=
      mul_pos (hattpos _ hy0) hy0
    have hmt := proposition_4_4 M hM hCi hCii1 r hr (φ r) (hφ.sol r hr)
      (show a ∈ Ioi (0:ℝ) from ha) (show x ∈ Ioi (0:ℝ) from hx) hax
    have hdn := (ADSAux.phi_deriv M D φ hφ r hr x hx).2
    have hm0 : 0 ≤ mtilde (φ r) x := by unfold mtilde; exact div_nonneg (by linarith) hpx.le
    have heq : Ψ' r x = (deriv M.att ((M.K - a) * (φ r x / φ r a)) *
        ((M.K - a) * (φ r x / φ r a))) * (- mtilde (φ r) x) := by
      simp only [hΨ', mtilde]
      field_simp
    rw [heq, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hf0,
      abs_of_nonneg hm0]
    calc _ ≤ C * mtilde (φ r) x := mul_le_mul_of_nonneg_right hf1 hm0
      _ ≤ C * mtilde (φ r) a := mul_le_mul_of_nonneg_left hmt hC0
  have hJ : ∀ x ∈ Ici a, J M D x (Icc 0 a) = ∫ r, Ψ r x ∂M.F := fun x hx =>
    ADSAux.J_eq M hM D hD φ hφ a x ha hx haK.le
  have hint : ∀ x, a ≤ x → Integrable (fun r => Ψ r x) M.F := fun x hx =>
    (ADSAux.integrand_facts M hM hCiii D φ hφ a x ha hx haK.le).2
  -- the value of the derivative
  have hval : deriv M.att (M.K - a) * (M.K - a) * G M φ a = ∫ r, Ψ' r a ∂M.F := by
    have : (fun r => Ψ' r a) =ᵐ[M.F] fun r => C * (deriv (φ r) a / φ r a) := by
      filter_upwards [ADSAux.ae_nonneg M hM] with r hr
      simp only [hΨ', hC]
      rw [div_self ((hφ.sol r hr).pos a ha).ne', mul_one]; ring
    rw [integral_congr_ae this, integral_const_mul]; rfl
  rw [hval]
  refine HasDerivWithinAt.congr ?_ hJ (hJ a (show a ∈ Ici a from le_refl a))
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici a \ {a} = Ioi a := by
    ext y
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h; exact ⟨h.le, h.ne'⟩
  rw [hset]
  have hslope : ∀ x, a < x →
      slope (fun x => ∫ r, Ψ r x ∂M.F) a x = ∫ r, slope (Ψ r) a x ∂M.F := by
    intro x hx
    simp only [slope_def_field]
    rw [integral_div, integral_sub (hint x hx.le) (hint a le_rfl)]
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall (fun x hx => (hslope x hx).symm)) ?_
  apply tendsto_integral_filter_of_dominated_convergence (fun r => C * mtilde (φ r) a)
  · filter_upwards [self_mem_nhdsWithin] with x (hx : a < x)
    simp only [slope_def_field, div_eq_mul_inv]
    exact ((hint x hx.le).aestronglyMeasurable.sub
      (hint a le_rfl).aestronglyMeasurable).mul aestronglyMeasurable_const
  · filter_upwards [self_mem_nhdsWithin] with x (hx : a < x)
    filter_upwards [ADSAux.ae_nonneg M hM] with r hr
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Ψ r) (f' := Ψ' r)
      (s := Icc a x)
      (fun ξ hξ => (hder r hr ξ (lt_of_lt_of_le ha hξ.1)).hasDerivWithinAt)
      (fun ξ hξ => hbd r hr ξ hξ.1) (convex_Icc a x) (left_mem_Icc.mpr hx.le)
      (right_mem_Icc.mpr hx.le)
    have hxa : 0 < x - a := by linarith
    rw [slope_def_field, norm_div, Real.norm_eq_abs (x - a), abs_of_pos hxa, div_le_iff₀ hxa]
    rw [Real.norm_eq_abs (x - a), abs_of_pos hxa] at hmvt
    exact hmvt
  · have := ((hG a ha).neg).const_mul C
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp [mtilde, neg_div]
  · filter_upwards [ADSAux.ae_nonneg M hM] with r hr
    have := (hasDerivAt_iff_tendsto_slope.mp (hder r hr a ha))
    exact this.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_gt hy))
