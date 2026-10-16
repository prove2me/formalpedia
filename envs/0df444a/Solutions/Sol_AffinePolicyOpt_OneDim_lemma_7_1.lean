-- Prove2me | solution 1 for AffinePolicyOpt.OneDim.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:15:35.645986+00:00
-- url     : https://prove2.me/submissions/9c9f2acc-dd4a-427f-96c3-dbe44bc9e4a7

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Setting

set_option autoImplicit false

namespace P172L71

open AffinePolicyOpt.OneDim Set

lemma cont_of_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) : Continuous f :=
  continuousOn_univ.mp (hf.continuousOn isOpen_univ)

lemma bddAbove_shift {f : ℝ → ℝ} (hf : Continuous f) (y a b : ℝ) :
    BddAbove ((fun w => f (y + w)) '' Icc a b) :=
  (isCompact_Icc.image (hf.comp (continuous_const.add continuous_id))).bddAbove

lemma sup_attain {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    ∃ w ∈ Icc a b, sSup ((fun w => f (y + w)) '' Icc a b) = f (y + w) := by
  obtain ⟨w, hw, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab)
    ((hf.comp (continuous_const.add continuous_id)).continuousOn : ContinuousOn (fun w => f (y + w)) (Icc a b))
  refine ⟨w, hw, ?_⟩
  apply IsGreatest.csSup_eq
  exact ⟨⟨w, hw, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hmax hv⟩

lemma sup_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {a b : ℝ} (hab : a ≤ b) :
    ConvexOn ℝ univ (fun y => sSup ((fun w => f (y + w)) '' Icc a b)) := by
  have hfc := cont_of_convex hf
  refine ⟨convex_univ, fun y1 _ y2 _ s t hs ht hst => ?_⟩
  have hne : ((fun w => f (s • y1 + t • y2 + w)) '' Icc a b).Nonempty :=
    ⟨_, a, left_mem_Icc.2 hab, rfl⟩
  apply csSup_le hne
  rintro _ ⟨w, hw, rfl⟩
  have h1 := hf.2 (mem_univ (y1 + w)) (mem_univ (y2 + w)) hs ht hst
  have e : s • (y1 + w) + t • (y2 + w) = s • y1 + t • y2 + w := by
    simp only [smul_eq_mul]
    calc s * (y1 + w) + t * (y2 + w) = s * y1 + t * y2 + (s + t) * w := by ring
      _ = s * y1 + t * y2 + w := by rw [hst, one_mul]
  rw [e] at h1
  have h2 : f (y1 + w) ≤ sSup ((fun w => f (y1 + w)) '' Icc a b) :=
    le_csSup (bddAbove_shift hfc y1 a b) ⟨w, hw, rfl⟩
  have h3 : f (y2 + w) ≤ sSup ((fun w => f (y2 + w)) '' Icc a b) :=
    le_csSup (bddAbove_shift hfc y2 a b) ⟨w, hw, rfl⟩
  calc f (s • y1 + t • y2 + w) ≤ s • f (y1 + w) + t • f (y2 + w) := h1
    _ ≤ _ := by
      simp only [smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_le_mul_of_nonneg_left h3 ht]

lemma gFun_convex {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') : ConvexOn ℝ univ (gFun M k J') := by
  have hf : ConvexOn ℝ univ (fun s => M.h k s + J' s) := (hM.h_convex k).add hJ
  exact sup_convex hf (hM.wlo_le_whi k)


lemma inf_attain {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) {L U : ℝ} (hLU : L ≤ U) (x : ℝ) :
    ∃ u ∈ Icc L U, IsMinOn (fun u => c * u + g (x + u)) (Icc L U) u :=
  isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hLU)
    (((continuous_const.mul continuous_id).add
      (hg.comp (continuous_const.add continuous_id))).continuousOn)

lemma sInf_eq_of_isMinOn {φ : ℝ → ℝ} {S : Set ℝ} {u : ℝ} (hu : u ∈ S) (h : IsMinOn φ S u) :
    sInf (φ '' S) = φ u :=
  IsLeast.csInf_eq ⟨⟨u, hu, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h hv⟩

lemma bddBelow_img {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) (x L U : ℝ) :
    BddBelow ((fun u => c * u + g (x + u)) '' Icc L U) :=
  (isCompact_Icc.image ((continuous_const.mul continuous_id).add
      (hg.comp (continuous_const.add continuous_id)))).bddBelow

lemma bellman_convex {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hg : ConvexOn ℝ univ (gFun M k J')) : ConvexOn ℝ univ (bellman M k J') := by
  have hgc := cont_of_convex hg
  have hLU := hM.L_le_U k
  refine ⟨convex_univ, fun x1 _ x2 _ s t hs ht hst => ?_⟩
  obtain ⟨u1, hu1, hm1⟩ := inf_attain hgc (M.c k) hLU x1
  obtain ⟨u2, hu2, hm2⟩ := inf_attain hgc (M.c k) hLU x2
  have e1 : bellman M k J' x1 = M.c k * u1 + gFun M k J' (x1 + u1) :=
    sInf_eq_of_isMinOn hu1 hm1
  have e2 : bellman M k J' x2 = M.c k * u2 + gFun M k J' (x2 + u2) :=
    sInf_eq_of_isMinOn hu2 hm2
  have hu : s • u1 + t • u2 ∈ Icc (M.L k) (M.U k) := (convex_Icc _ _) hu1 hu2 hs ht hst
  have h1 : bellman M k J' (s • x1 + t • x2) ≤
      M.c k * (s • u1 + t • u2) + gFun M k J' (s • x1 + t • x2 + (s • u1 + t • u2)) :=
    csInf_le (bddBelow_img hgc _ _ _ _) ⟨_, hu, rfl⟩
  have h2 := hg.2 (mem_univ (x1 + u1)) (mem_univ (x2 + u2)) hs ht hst
  have e : s • (x1 + u1) + t • (x2 + u2) = s • x1 + t • x2 + (s • u1 + t • u2) := by
    simp only [smul_eq_mul]; ring
  rw [e] at h2
  rw [e1, e2]
  simp only [smul_eq_mul] at h1 h2 ⊢
  nlinarith [h1, h2, hst]

lemma h_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) : ∃ m, ∀ y, m ≤ M.h k y := by
  have hc := cont_of_convex (hM.h_convex k)
  obtain ⟨x, hx⟩ := hc.exists_forall_le (hM.h_coercive k)
  exact ⟨_, hx⟩

lemma gFun_ge {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (y w : ℝ) (hw : w ∈ Icc (M.wlo k) (M.whi k)) :
    M.h k (y + w) + J' (y + w) ≤ gFun M k J' y := by
  have hf : ConvexOn ℝ univ (fun s => M.h k s + J' s) := (hM.h_convex k).add hJ
  exact le_csSup (bddAbove_shift (cont_of_convex hf) y _ _) ⟨w, hw, rfl⟩

lemma gFun_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (m : ℝ) (hm : ∀ x, m ≤ J' x) :
    ∃ mg, ∀ y, mg ≤ gFun M k J' y := by
  obtain ⟨mh, hmh⟩ := h_bdd M hM k
  refine ⟨mh + m, fun y => ?_⟩
  have := gFun_ge M hM k hJ y (M.wlo k) (left_mem_Icc.2 (hM.wlo_le_whi k))
  linarith [hmh (y + M.wlo k), hm (y + M.wlo k)]

lemma bellman_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (_hg : ConvexOn ℝ univ (gFun M k J')) (mg : ℝ) (hmg : ∀ y, mg ≤ gFun M k J' y) :
    ∃ m, ∀ x, m ≤ bellman M k J' x := by
  refine ⟨M.c k * M.L k + mg, fun x => ?_⟩
  unfold bellman
  refine le_csInf ⟨M.c k * M.L k + gFun M k J' (x + M.L k), M.L k, left_mem_Icc.2 (hM.L_le_U k), rfl⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left hu.1 (hM.c_nonneg k), hmg (x + u)]

lemma Jstar_ge_T {T : ℕ} (M : Model T) (j : ℕ) (hj : ¬ j < T) : Jstar M j = fun _ => 0 := by
  rw [Jstar, dif_neg hj]

lemma Jstar_lt_T {T : ℕ} (M : Model T) (j : ℕ) (hj : j < T) :
    Jstar M j = bellman M ⟨j, hj⟩ (Jstar M (j + 1)) := by
  rw [Jstar, dif_pos hj]

lemma good_all {T : ℕ} (M : Model T) (hM : M.Standing) :
    ∀ j : ℕ, ConvexOn ℝ univ (Jstar M j) ∧ ∃ m, ∀ x, m ≤ Jstar M j x := by
  have key : ∀ d j : ℕ, T ≤ j + d →
      ConvexOn ℝ univ (Jstar M j) ∧ ∃ m, ∀ x, m ≤ Jstar M j x := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [Jstar_ge_T M j (by omega)]
      exact ⟨convexOn_const 0 convex_univ, 0, fun _ => le_refl _⟩
    | succ d ih =>
      intro j hj
      by_cases hjT : j < T
      · obtain ⟨hc, m, hm⟩ := ih (j + 1) (by omega)
        rw [Jstar_lt_T M j hjT]
        have hg := gFun_convex M hM ⟨j, hjT⟩ hc
        obtain ⟨mg, hmg⟩ := gFun_bdd M hM ⟨j, hjT⟩ hc m hm
        exact ⟨bellman_convex M hM _ hg, bellman_bdd M hM _ hg mg hmg⟩
      · rw [Jstar_ge_T M j hjT]
        exact ⟨convexOn_const 0 convex_univ, 0, fun _ => le_refl _⟩
  exact fun j => key T j (by omega)


lemma proj_min {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) {L U u0 : ℝ} (hLU : L ≤ U)
    (h0 : ∀ u, ψ u0 ≤ ψ u) : IsMinOn ψ (Icc L U) (max L (min U u0)) := by
  intro u hu
  show ψ (max L (min U u0)) ≤ ψ u
  rcases lt_or_ge u0 L with h | h
  · have e : max L (min U u0) = L := by
      rw [min_eq_right (by linarith), max_eq_left h.le]
    rw [e]
    have := hψ.le_max_of_mem_Icc (mem_univ u0) (mem_univ u) (⟨h.le, hu.1⟩ : L ∈ Icc u0 u)
    exact this.trans (max_le (h0 u) le_rfl)
  · rcases le_or_gt u0 U with h' | h'
    · have e : max L (min U u0) = u0 := by rw [min_eq_right h', max_eq_right h]
      rw [e]; exact h0 u
    · have e : max L (min U u0) = U := by rw [min_eq_left h'.le, max_eq_right hLU]
      rw [e]
      have := hψ.le_max_of_mem_Icc (mem_univ u) (mem_univ u0) (⟨hu.2, h'.le⟩ : U ∈ Icc u u0)
      exact this.trans (max_le le_rfl (h0 u))

lemma clamp_mem {L U t : ℝ} (hLU : L ≤ U) : max L (min U t) ∈ Icc L U :=
  ⟨le_max_left _ _, max_le hLU (min_le_left _ _)⟩

lemma convex_psi {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (c x : ℝ) :
    ConvexOn ℝ univ (fun u => c * u + g (x + u)) := by
  refine ⟨convex_univ, fun u1 _ u2 _ s t hs ht hst => ?_⟩
  have h2 := hg.2 (mem_univ (x + u1)) (mem_univ (x + u2)) hs ht hst
  have e : s • (x + u1) + t • (x + u2) = x + (s • u1 + t • u2) := by
    simp only [smul_eq_mul]
    calc s * (x + u1) + t * (x + u2) = (s + t) * x + (s * u1 + t * u2) := by ring
      _ = x + (s * u1 + t * u2) := by rw [hst, one_mul]
  rw [e] at h2
  simp only [smul_eq_mul] at h2 ⊢
  nlinarith [h2]

lemma clamp_opt {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (c L U ystar : ℝ) (hLU : L ≤ U)
    (hy : IsMinOn (fun y => c * y + g y) univ ystar) (x : ℝ) :
    IsMinOn (fun u => c * u + g (x + u)) (Icc L U) (max L (min U (ystar - x))) := by
  apply proj_min (convex_psi hg c x) hLU
  intro u
  have h1 : c * ystar + g ystar ≤ c * (x + u) + g (x + u) := hy (mem_univ (x + u))
  have e : x + (ystar - x) = ystar := by ring
  show c * (ystar - x) + g (x + (ystar - x)) ≤ c * u + g (x + u)
  rw [e]
  nlinarith [h1]

lemma mono_of_no_min {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hlim : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hno : ¬ ∃ y, IsMinOn φ univ y) : Monotone φ := by
  intro p q hpq
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨r, hr1, hr2⟩ := ((hlim.eventually_gt_atTop (φ p)).and
    (Filter.eventually_gt_atTop q)).exists
  have hφc := cont_of_convex hφ
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (hpq.trans hr2.le))
    hφc.continuousOn
  apply hno
  refine ⟨m, fun y _ => ?_⟩
  show φ m ≤ φ y
  by_cases hyp : y < p
  · have h1 := hφ.le_max_of_mem_Icc (mem_univ y) (mem_univ q) (⟨hyp.le, hpq⟩ : p ∈ Icc y q)
    have h2 : φ p ≤ φ y := by
      rcases le_max_iff.1 h1 with h | h
      · exact h
      · exact absurd h (not_le.2 hlt)
    exact (hmin (⟨le_rfl, hpq.trans hr2.le⟩ : p ∈ Icc p r)).trans h2
  · by_cases hyr : r < y
    · have h1 := hφ.le_max_of_mem_Icc (mem_univ q) (mem_univ y) (⟨hr2.le, hyr.le⟩ : r ∈ Icc q y)
      have h2 : φ r ≤ φ y := by
        rcases le_max_iff.1 h1 with h | h
        · exact absurd h (not_le.2 (by linarith))
        · exact h
      exact (hmin (⟨hpq.trans hr2.le, le_rfl⟩ : r ∈ Icc p r)).trans h2
    · exact hmin (⟨not_lt.1 hyp, not_lt.1 hyr⟩ : y ∈ Icc p r)

lemma phi_tendsto {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (m : ℝ) (hm : ∀ x, m ≤ J' x) :
    Filter.Tendsto (fun y => M.c k * y + gFun M k J' y) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (M.h k) Filter.atTop Filter.atTop :=
    (hM.h_coercive k).mono_left atTop_le_cocompact
  have h2 : Filter.Tendsto (fun y => M.h k (y + M.wlo k) + m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      (h1.comp (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id))
  refine Filter.tendsto_atTop_mono' _ ?_ h2
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
  have := gFun_ge M hM k hJ y (M.wlo k) (left_mem_Icc.2 (hM.wlo_le_whi k))
  nlinarith [mul_nonneg (hM.c_nonneg k) hy, hm (y + M.wlo k)]

lemma Jstar_fin {T : ℕ} (M : Model T) (k : Fin T) :
    Jstar M (k : ℕ) = bellman M k (Jstar M ((k : ℕ) + 1)) := by
  have := Jstar_lt_T M (k : ℕ) k.2
  simpa using this

theorem lemma_7_1 {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) :
    ConvexOn ℝ Set.univ (Jstar M k) ∧
    ConvexOn ℝ Set.univ (gFun M k (Jstar M ((k : ℕ) + 1))) ∧
    (∀ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (max (M.L k) (min (M.U k) (ystar - x))) ∧
          Jstar M k x = M.c k * max (M.L k) (min (M.U k) (ystar - x)) +
              gFun M k (Jstar M ((k : ℕ) + 1)) (x + max (M.L k) (min (M.U k) (ystar - x)))) ∧
    ((¬ ∃ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar) →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (M.L k) ∧
          Jstar M k x = M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k)) := by
  obtain ⟨hc1, m1, hm1⟩ := good_all M hM ((k : ℕ) + 1)
  obtain ⟨hcK, _⟩ := good_all M hM (k : ℕ)
  have hg := gFun_convex M hM k hc1
  have hLU := hM.L_le_U k
  refine ⟨hcK, hg, ?_, ?_⟩
  · intro ystar hy x
    have hmin := clamp_opt hg (M.c k) (M.L k) (M.U k) ystar hLU hy x
    refine ⟨hmin, ?_⟩
    rw [Jstar_fin M k]
    exact sInf_eq_of_isMinOn (clamp_mem hLU) hmin
  · intro hno x
    have hφ : ConvexOn ℝ univ (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) := by
      simpa using convex_psi hg (M.c k) 0
    have hmono := mono_of_no_min hφ (phi_tendsto M hM k hc1 m1 hm1) hno
    have hmin : IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
        (Icc (M.L k) (M.U k)) (M.L k) := by
      intro u hu
      show M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k) ≤
        M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u)
      have h1 := hmono (show x + M.L k ≤ x + u by linarith [hu.1])
      simp only at h1
      nlinarith [h1]
    refine ⟨hmin, ?_⟩
    rw [Jstar_fin M k]
    exact sInf_eq_of_isMinOn (left_mem_Icc.2 hLU) hmin

end P172L71

open AffinePolicyOpt.OneDim in
theorem solution {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) :
    ConvexOn ℝ Set.univ (Jstar M k) ∧
    ConvexOn ℝ Set.univ (gFun M k (Jstar M ((k : ℕ) + 1))) ∧
    (∀ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (max (M.L k) (min (M.U k) (ystar - x))) ∧
          Jstar M k x = M.c k * max (M.L k) (min (M.U k) (ystar - x)) +
              gFun M k (Jstar M ((k : ℕ) + 1)) (x + max (M.L k) (min (M.U k) (ystar - x)))) ∧
    ((¬ ∃ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar) →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (M.L k) ∧
          Jstar M k x = M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k)) := by
  exact P172L71.lemma_7_1 M hM k
