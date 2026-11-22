-- Prove2me | solution 1 for ApproxFiniteCase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:27.16785+00:00
-- url     : https://prove2.me/submissions/684349cb-44b6-4acb-ac6c-f60347e10244

import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_Noncritical
import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
import Definitions.Def_PHigherOrder_TaylorPolyFarBound
import Definitions.Def_PHigherOrder_TaylorPolyRescale
import Definitions.Def_PHigherOrder_TaylorRemainder
import Definitions.Def_PHigherOrder_ApproxFiniteCase
import Theorems.Thm_Noncritical
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_TaylorPolyDeriv
import Theorems.Thm_TaylorPolyFarBound
import Theorems.Thm_TaylorPolyRescale
import Theorems.Thm_TaylorRemainder


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (hsm : SmoothAwayFromCriticalInput p)
    (hS : DivFormSchauderInput) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (δ : ℝ) (hδ : 0 < δ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g → v 0 = 0 →
        ∀ (R : ℕ → ℝ) (L : ℕ), R 0 = 1 → (∀ l : ℕ, 0 < R l) → (∀ l : ℕ, R l ≤ 1) →
          (∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ ((k : ℝ) + β)) →
          (∀ l < L, θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) →
          δ < R L ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ →
          (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
              |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ C * ‖w‖ ^ j)
            ∧ (∀ y : Plane, ‖y‖ < 1 →
                |v y - TaylorPoly k v 0 y| ≤ C * ‖y‖ ^ ((k : ℝ) + β)) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs0 : (0 : ℝ) < (k : ℝ) + β := by linarith
  have hsk : (k : ℝ) ≤ (k : ℝ) + β := by linarith
  have hks1 : ((k : ℝ) + β) < (k : ℝ) + 1 := by linarith
  -- STEP 0:  the constants, fixed before `v`.
  obtain ⟨τ, hτ0, hτ4, Cδ, hCδ, hNC⟩ := Noncritical p hp hp2 k F hsm hS δ hδ
  have hτ1 : τ ≤ 1 := by linarith
  have hfac : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ, t = max (max Cδ (Cδ / (Nat.factorial (k + 1) : ℝ)))
      (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β))
        + (k : ℝ) * Cδ * τ ^ (-((k : ℝ) + β))) := ⟨_, rfl⟩
  have hCδC : Cδ ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCfC : Cδ / (Nat.factorial (k + 1) : ℝ) ≤ C := by
    rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCfarC : τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β))
      + (k : ℝ) * Cδ * τ ^ (-((k : ℝ) + β)) ≤ C := by
    rw [hCdef]; exact le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hCδ hCδC
  refine ⟨C, hC0, ?_⟩
  intro v g hph hv0 R L hR0 hRpos hRle1 hGood hsand hbig
  -- STEP 1:  the rescaled solution.
  obtain ⟨S, hSdef⟩ : ∃ t : ℝ, t = R L := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hSdef]; exact hRpos L
  have hS1 : S ≤ 1 := by rw [hSdef]; exact hRle1 L
  have hSne : S ≠ 0 := ne_of_gt hS0
  obtain ⟨M, hMdef⟩ : ∃ t : ℝ, t = S ^ ((k : ℝ) + β) := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hMdef]; exact Real.rpow_pos_of_pos hS0 _
  have hMne : M ≠ 0 := ne_of_gt hM0
  obtain ⟨vL, hvLdef⟩ : ∃ f : Plane → ℝ, f = fun x => v (S • x) / M := ⟨_, rfl⟩
  have hvLapp : ∀ x : Plane, vL x = v (S • x) / M := by intro x; rw [hvLdef]
  have hSsm : ∀ x : Plane, ‖x‖ < 1 → ‖S • x‖ < S := by
    intro x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hS0]
    calc S * ‖x‖ < S * 1 := mul_lt_mul_of_pos_left hx hS0
      _ = S := by ring
  -- (1a)
  have hPN := PHarmNormalize p hp hp2 (Metric.ball 0 1) v g 0 S M 0 hS0 hM0 hph
  have hsubset : Metric.ball (0 : Plane) 1
      ⊆ {x : Plane | (0 : Plane) + S • x ∈ Metric.ball 0 1} := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hb : ‖(0 : Plane) + S • x‖ < 1 := by
      rw [zero_add]
      exact lt_of_lt_of_le (hSsm x hx) hS1
    simpa [Metric.mem_ball, dist_zero_right] using hb
  have hvLsimp : (fun x : Plane => (v ((0 : Plane) + S • x) - 0) / M) = vL := by
    funext x
    rw [hvLdef, zero_add, sub_zero]
  have hphL : IsPHarm p (Metric.ball 0 1) vL
      (fun x => (S / M) • g ((0 : Plane) + S • x)) := by
    rw [← hvLsimp]
    exact (PHarmRestrict p hp hp2 _ _ _ hPN).1 _ Metric.isOpen_ball hsubset
  -- (1b)
  have hvLbd : ∀ x ∈ Metric.ball (0 : Plane) 1, |vL x| ≤ 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have h := hGood L (S • x) (by rw [← hSdef]; exact hSsm x hx)
    rw [← hSdef, ← hMdef] at h
    rw [hvLapp, abs_div, abs_of_pos hM0, div_le_one hM0]
    exact h
  -- (1c)
  have h0mem : (0 : Plane) ∈ Metric.ball (0 : Plane) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ, hρ, Cim, hCim, hρsub, hvCk, -⟩ :=
    hIM.reg (Metric.ball 0 1) v g hph k β hβ0 hβ1 hks 0 h0mem
  -- (1d)
  obtain ⟨hjetid, hpolyid⟩ :=
    TaylorPolyRescale k ((k : ℝ) + β) v ρ hρ hvCk S hS0 vL
      (by intro x; rw [hvLapp, hMdef])
  -- (1e)
  have hvdiff : DifferentiableAt ℝ v 0 := by
    have h0 : (0 : Plane) ∈ Metric.ball (0 : Plane) ρ := Metric.mem_ball_self hρ
    exact ((hvCk.differentiableOn (by exact_mod_cast (by omega : k ≠ 0))) 0 h0).differentiableAt
      (Metric.isOpen_ball.mem_nhds h0)
  have hgradL : gradient vL 0 = (M⁻¹ * S) • gradient v 0 := by
    have hlin : HasFDerivAt (fun x : Plane => S • x) (S • ContinuousLinearMap.id ℝ Plane) 0 :=
      (S • ContinuousLinearMap.id ℝ Plane).hasFDerivAt
    have h1 : HasFDerivAt v (fderiv ℝ v 0) (S • (0 : Plane)) := by
      rw [smul_zero]; exact hvdiff.hasFDerivAt
    have hfull : HasFDerivAt (fun x : Plane => M⁻¹ * v (S • x))
        (M⁻¹ • ((fderiv ℝ v 0).comp (S • ContinuousLinearMap.id ℝ Plane))) 0 :=
      (h1.comp 0 hlin).const_mul M⁻¹
    have hvLeq : vL = fun x : Plane => M⁻¹ * v (S • x) := by
      funext x; rw [hvLapp, div_eq_inv_mul]
    refine ext_inner_right ℝ ?_
    intro w
    have hL : inner ℝ (gradient vL 0) w = fderiv ℝ vL 0 w := by
      rw [← toDual_gradient]; rfl
    have hvw : inner ℝ (gradient v 0) w = fderiv ℝ v 0 w := by
      rw [← toDual_gradient]; rfl
    rw [hL, hvLeq, hfull.fderiv, real_inner_smul_left, hvw]
    show M⁻¹ * ((fderiv ℝ v 0) (S • w)) = _
    rw [map_smul, smul_eq_mul]
    ring
  have hMS : M⁻¹ * S = S ^ (1 - ((k : ℝ) + β)) := by
    have h1 : (1 : ℝ) - ((k : ℝ) + β) = 1 + (-((k : ℝ) + β)) := by ring
    rw [h1, Real.rpow_add hS0, Real.rpow_one, Real.rpow_neg (le_of_lt hS0), hMdef]
    ring
  have hbigL : δ < ‖gradient vL 0‖ := by
    rw [hgradL, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < M⁻¹ * S), hMS]
    rw [hSdef]
    exact hbig
  obtain ⟨hvLCk1, hvLbnd⟩ := hNC vL _ hphL hvLbd hbigL
  have hτmem : (0 : Plane) ∈ Metric.ball (0 : Plane) τ := Metric.mem_ball_self hτ0
  -- STEP 2:  the coefficient bound, in the sharp form the far regime needs.
  have hjetbd : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
      |iteratedFDeriv ℝ j v 0 (fun _ => w)|
        ≤ Cδ * S ^ (((k : ℝ) + β) - (j : ℝ)) * ‖w‖ ^ j := by
    intro j hj1 hjk w
    have hop : |iteratedFDeriv ℝ j vL 0 (fun _ => w)| ≤ Cδ * ‖w‖ ^ j := by
      have h1 := (iteratedFDeriv ℝ j vL 0).le_opNorm (fun _ : Fin j => w)
      have h2 : ∏ _i : Fin j, ‖w‖ = ‖w‖ ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [h2] at h1
      have h3 : ‖iteratedFDeriv ℝ j vL 0‖ ≤ Cδ := hvLbnd j (by omega) 0 hτmem
      calc |iteratedFDeriv ℝ j vL 0 (fun _ => w)|
          = ‖iteratedFDeriv ℝ j vL 0 (fun _ => w)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖iteratedFDeriv ℝ j vL 0‖ * ‖w‖ ^ j := h1
        _ ≤ Cδ * ‖w‖ ^ j := mul_le_mul_of_nonneg_right h3 (by positivity)
    have hSp : 0 < S ^ (((k : ℝ) + β) - (j : ℝ)) := Real.rpow_pos_of_pos hS0 _
    rw [hjetid j hjk w, abs_mul, abs_of_pos hSp]
    calc S ^ (((k : ℝ) + β) - (j : ℝ)) * |iteratedFDeriv ℝ j vL 0 (fun _ => w)|
        ≤ S ^ (((k : ℝ) + β) - (j : ℝ)) * (Cδ * ‖w‖ ^ j) :=
          mul_le_mul_of_nonneg_left hop (le_of_lt hSp)
      _ = Cδ * S ^ (((k : ℝ) + β) - (j : ℝ)) * ‖w‖ ^ j := by ring
  refine ⟨?_, ?_⟩
  · -- conclusion (1):  weaken `S ^ (σ - j) ≤ 1`
    intro j hj1 hjk w
    have hjle : (j : ℝ) ≤ (k : ℝ) + β := by
      have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      linarith
    have hSle1 : S ^ (((k : ℝ) + β) - (j : ℝ)) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hS0) hS1 (by linarith)
    refine le_trans (hjetbd j hj1 hjk w) ?_
    calc Cδ * S ^ (((k : ℝ) + β) - (j : ℝ)) * ‖w‖ ^ j
        ≤ Cδ * 1 * ‖w‖ ^ j := by
          have := mul_le_mul_of_nonneg_left hSle1 (le_of_lt hCδ)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = Cδ * ‖w‖ ^ j := by ring
      _ ≤ C * ‖w‖ ^ j := mul_le_mul_of_nonneg_right hCδC (by positivity)
  · -- STEP 3:  conclusion (2), the error bound.
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · have hP0 : TaylorPoly k v 0 (0 : Plane) = v 0 := (TaylorPolyDeriv k v 0).2.2.2.2
      rw [hP0, sub_self, abs_zero, norm_zero, Real.zero_rpow (ne_of_gt hs0), mul_zero]
    · have ht0 : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have htpow : (0 : ℝ) ≤ ‖y‖ ^ ((k : ℝ) + β) :=
        le_of_lt (Real.rpow_pos_of_pos ht0 _)
      have htri : |v y - TaylorPoly k v 0 y| ≤ |v y| + |TaylorPoly k v 0 y| := by
        calc |v y - TaylorPoly k v 0 y| = |v y + -TaylorPoly k v 0 y| := by rw [sub_eq_add_neg]
          _ ≤ |v y| + |-TaylorPoly k v 0 y| := abs_add_le _ _
          _ = |v y| + |TaylorPoly k v 0 y| := by rw [abs_neg]
      rcases lt_or_ge ‖y‖ (τ * S) with hnear | hfarreg
      · -- (3a) the near regime, via the Taylor remainder for `vL`
        have hrem := TaylorRemainder vL 0 τ hτ0 k Cδ (le_of_lt hCδ) hvLCk1
          (fun x hx => hvLbnd (k + 1) (le_refl _) x hx)
        obtain ⟨x, hxdef⟩ : ∃ z : Plane, z = S⁻¹ • y := ⟨_, rfl⟩
        have hSx : S • x = y := by
          rw [hxdef, smul_smul, mul_inv_cancel₀ hSne, one_smul]
        have hxn : ‖x‖ = ‖y‖ / S := by
          rw [hxdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS0),
            inv_mul_eq_div]
        have hu0 : 0 < ‖y‖ / S := div_pos ht0 hS0
        have huτ : ‖y‖ / S < τ := by
          rw [div_lt_iff₀ hS0]
          linarith
        have hxmem : x ∈ Metric.ball (0 : Plane) τ := by
          have hb : ‖x‖ < τ := by rw [hxn]; exact huτ
          simpa [Metric.mem_ball, dist_zero_right] using hb
        have hrem' := hrem x hxmem
        rw [sub_zero, hxn] at hrem'
        have hvLx : vL x = v y / M := by rw [hvLapp, hSx]
        have hPy : TaylorPoly k v 0 y = M * TaylorPoly k vL 0 x := by
          rw [hpolyid y, ← hMdef, hxdef]
        have hdiff : v y - TaylorPoly k v 0 y = M * (vL x - TaylorPoly k vL 0 x) := by
          rw [hvLx, hPy]
          field_simp
        have hnat : (‖y‖ / S) ^ (k + 1) = (‖y‖ / S) ^ ((k : ℝ) + 1) := by
          rw [← Real.rpow_natCast (‖y‖ / S) (k + 1)]
          norm_num
        have e2 : S ^ ((k : ℝ) + β) * (‖y‖ / S) ^ ((k : ℝ) + β) = ‖y‖ ^ ((k : ℝ) + β) := by
          rw [← Real.mul_rpow (le_of_lt hS0) (le_of_lt hu0)]
          congr 1
          field_simp
        have hcomb : M * (‖y‖ / S) ^ (k + 1)
            = ‖y‖ ^ ((k : ℝ) + β)
              * (‖y‖ / S) ^ (((k : ℝ) + 1) - ((k : ℝ) + β)) := by
          have hexp : ((k : ℝ) + 1) = ((k : ℝ) + β) + (((k : ℝ) + 1) - ((k : ℝ) + β)) := by
            ring
          rw [hnat, hMdef, ← e2, mul_assoc, ← Real.rpow_add hu0, ← hexp]
        have hsmall : (‖y‖ / S) ^ (((k : ℝ) + 1) - ((k : ℝ) + β)) ≤ 1 := by
          refine Real.rpow_le_one (le_of_lt hu0) ?_ (by linarith)
          exact le_trans (le_of_lt huτ) hτ1
        rw [hdiff, abs_mul, abs_of_pos hM0]
        calc M * |vL x - TaylorPoly k vL 0 x|
            ≤ M * (Cδ / (Nat.factorial (k + 1) : ℝ) * (‖y‖ / S) ^ (k + 1)) :=
              mul_le_mul_of_nonneg_left hrem' (le_of_lt hM0)
          _ = Cδ / (Nat.factorial (k + 1) : ℝ) * (M * (‖y‖ / S) ^ (k + 1)) := by ring
          _ = Cδ / (Nat.factorial (k + 1) : ℝ)
                * (‖y‖ ^ ((k : ℝ) + β)
                    * (‖y‖ / S) ^ (((k : ℝ) + 1) - ((k : ℝ) + β))) := by rw [hcomb]
          _ ≤ Cδ / (Nat.factorial (k + 1) : ℝ) * (‖y‖ ^ ((k : ℝ) + β) * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hsmall htpow
          _ = Cδ / (Nat.factorial (k + 1) : ℝ) * ‖y‖ ^ ((k : ℝ) + β) := by ring
          _ ≤ C * ‖y‖ ^ ((k : ℝ) + β) := mul_le_mul_of_nonneg_right hCfC htpow
      · -- (3b) the far regime
        have hfar0 : ∀ ϱ η : ℝ, 0 < ϱ → 0 < η → η ≤ 1 → η * ϱ ≤ ‖y‖ →
            ϱ ^ ((k : ℝ) + β) ≤ η ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) := by
          intro ϱ η hϱ hη0 hη1 hle
          have hϱle : ϱ ≤ η⁻¹ * ‖y‖ := by
            rw [← div_eq_inv_mul, le_div_iff₀ hη0]
            linarith
          calc ϱ ^ ((k : ℝ) + β) ≤ (η⁻¹ * ‖y‖) ^ ((k : ℝ) + β) :=
                Real.rpow_le_rpow (le_of_lt hϱ) hϱle (le_of_lt hs0)
            _ = η ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) := by
                rw [Real.mul_rpow (le_of_lt (inv_pos.mpr hη0)) (le_of_lt ht0),
                  Real.inv_rpow (le_of_lt hη0), ← Real.rpow_neg (le_of_lt hη0)]
        have hτp : (0 : ℝ) < τ ^ (-((k : ℝ) + β)) := Real.rpow_pos_of_pos hτ0 _
        have hθp : (0 : ℝ) < θ ^ (-((k : ℝ) + β)) := Real.rpow_pos_of_pos hθ0 _
        have hsol : |v y| ≤ (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β)))
            * ‖y‖ ^ ((k : ℝ) + β) := by
          rcases lt_or_ge ‖y‖ S with hlt | hge
          · have h := hGood L y (by rw [← hSdef]; exact hlt)
            rw [← hSdef] at h
            calc |v y| ≤ S ^ ((k : ℝ) + β) := h
              _ ≤ τ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) :=
                  hfar0 S τ hS0 hτ0 hτ1 hfarreg
              _ ≤ (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β)))
                    * ‖y‖ ^ ((k : ℝ) + β) :=
                  mul_le_mul_of_nonneg_right (by linarith) htpow
          · obtain ⟨ℓ, hℓdef⟩ : ∃ m : ℕ, m = Nat.findGreatest (fun l => ‖y‖ < R l) L :=
              ⟨_, rfl⟩
            have hP0' : ‖y‖ < R 0 := by rw [hR0]; exact hy
            have hℓP : ‖y‖ < R ℓ := by
              rw [hℓdef]
              exact Nat.findGreatest_spec (P := fun l => ‖y‖ < R l) (Nat.zero_le L) hP0'
            have hℓle : ℓ ≤ L := by rw [hℓdef]; exact Nat.findGreatest_le L
            have hℓne : ℓ ≠ L := by
              intro hc
              rw [hc, ← hSdef] at hℓP
              linarith
            have hℓL : ℓ < L := by omega
            have hnext : R (ℓ + 1) ≤ ‖y‖ := by
              have hgr := Nat.findGreatest_is_greatest (k := ℓ + 1)
                (P := fun l => ‖y‖ < R l) (n := L) (by rw [← hℓdef]; omega) (by omega)
              exact not_lt.mp hgr
            have hθR : θ * R ℓ ≤ ‖y‖ := le_trans (hsand ℓ hℓL).1 hnext
            calc |v y| ≤ R ℓ ^ ((k : ℝ) + β) := hGood ℓ y hℓP
              _ ≤ θ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) :=
                  hfar0 (R ℓ) θ (hRpos ℓ) hθ0 hθ1 hθR
              _ ≤ (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β)))
                    * ‖y‖ ^ ((k : ℝ) + β) :=
                  mul_le_mul_of_nonneg_right (by linarith) htpow
        have hpol : |TaylorPoly k v 0 y|
            ≤ (k : ℝ) * Cδ * τ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) :=
          TaylorPolyFarBound k ((k : ℝ) + β) hsk Cδ hCδ τ hτ0 hτ1 v S hS0 hv0 hjetbd y hfarreg
        calc |v y - TaylorPoly k v 0 y| ≤ |v y| + |TaylorPoly k v 0 y| := htri
          _ ≤ (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β))) * ‖y‖ ^ ((k : ℝ) + β)
                + (k : ℝ) * Cδ * τ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) := by
              linarith [hsol, hpol]
          _ = (τ ^ (-((k : ℝ) + β)) + θ ^ (-((k : ℝ) + β))
                + (k : ℝ) * Cδ * τ ^ (-((k : ℝ) + β))) * ‖y‖ ^ ((k : ℝ) + β) := by ring
          _ ≤ C * ‖y‖ ^ ((k : ℝ) + β) := mul_le_mul_of_nonneg_right hCfarC htpow
