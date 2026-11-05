-- Prove2me | solution 1 for AggGameNet.Sync.vi_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:24:34.20988+00:00
-- url     : https://prove2.me/submissions/a22c74b4-9820-4b44-9aff-c3d49b69da1b

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AGT_brouwer_fixed_point

namespace AggGameNet.Sync.VIEx

open ChanPangGQVI.Shared

lemma isProj_inner_le {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {z p : E n}
    (hp : IsProj S z p) : ∀ q ∈ S, inner ℝ (z - p) (q - p) ≤ 0 := by
  have hne : Nonempty S := ⟨⟨p, hp.1⟩⟩
  have heq : ‖z - p‖ = ⨅ w : S, ‖z - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      rw [norm_sub_rev z p, norm_sub_rev z w]
      exact hp.2 w w.2
    · have hb : BddBelow (Set.range (fun w : S => ‖z - (w : E n)‖)) :=
        ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
      exact ciInf_le (f := fun w : S => ‖z - (w : E n)‖) hb ⟨p, hp.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hS hp.1).1 heq

lemma isProj_proj {n : ℕ} {S : Set (E n)} (hne : S.Nonempty) (hcl : IsClosed S)
    (hS : Convex ℝ S) (z : E n) : IsProj S z (proj S z) := by
  obtain ⟨v, hv, hveq⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hS z
  have hex : ∃ p, IsProj S z p := by
    refine ⟨v, hv, fun q hq => ?_⟩
    have hb : BddBelow (Set.range (fun w : S => ‖z - (w : E n)‖)) :=
      ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
    have := ciInf_le (f := fun w : S => ‖z - (w : E n)‖) hb ⟨q, hq⟩
    rw [norm_sub_rev v z, norm_sub_rev q z, hveq]
    exact this
  unfold proj
  simp only [dif_pos hex]
  exact hex.choose_spec

lemma proj_lipschitz {n : ℕ} {S : Set (E n)} (hne : S.Nonempty) (hcl : IsClosed S)
    (hS : Convex ℝ S) (z z' : E n) : ‖proj S z - proj S z'‖ ≤ ‖z - z'‖ := by
  have hp := isProj_proj hne hcl hS z
  have hp' := isProj_proj hne hcl hS z'
  set p := proj S z
  set p' := proj S z'
  have h1 := isProj_inner_le hS hp p' hp'.1
  have h2 := isProj_inner_le hS hp' p hp.1
  -- ‖p - p'‖² ≤ ⟨z - z', p - p'⟩
  have key : ‖p - p'‖ ^ 2 ≤ inner ℝ (z - z') (p - p') := by
    have e1 : inner ℝ (z - p) (p' - p) = -(inner ℝ (z - p) (p - p')) := by
      rw [← inner_neg_right, neg_sub]
    have e2 : inner ℝ (z - z') (p - p') =
        inner ℝ (z - p) (p - p') + inner ℝ (z' - p') (p' - p) + ‖p - p'‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : z - z' = (z - p) + (-(z' - p')) + (p - p') := by abel
      rw [this, inner_add_left, inner_add_left, inner_neg_left]
      have : p' - p = -(p - p') := by abel
      rw [this, inner_neg_right]
    have e3 : inner ℝ (z' - p') (p' - p) = -(inner ℝ (z' - p') (p - p')) := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have hcs := real_inner_le_norm (z - z') (p - p')
  by_cases h0 : ‖p - p'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - p'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end AggGameNet.Sync.VIEx

open AggGameNet.Sync AggGameNet.Sync.VIEx ChanPangGQVI.Shared

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (h2 : Assumption2 K F) :
    ∃ xs, IsVISol K F xs ∧ ∀ y, IsVISol K F y → y = xs := by
  have hne : ∀ i, (K i).Nonempty := fun i => (h1.1 i).1
  have hcl : ∀ i, IsClosed (K i) := fun i => (h1.1 i).2.1.isClosed
  have hcv : ∀ i, Convex ℝ (K i) := fun i => (h1.1 i).2.2
  set P : Set (Fin N → E n) := Set.univ.pi K with hPdef
  have hPc : IsCompact P := isCompact_univ_pi (fun i => (h1.1 i).2.1)
  have hPv : Convex ℝ P := convex_pi (fun i _ => hcv i)
  have hPn : P.Nonempty := Set.univ_pi_nonempty_iff.2 hne
  set f : (Fin N → E n) → (Fin N → E n) :=
    fun y i => proj (K i) (y i - phi F y i) with hfdef
  have hphi : ∀ i, ContinuousOn (fun y : Fin N → E n => phi F y i) P := by
    intro i
    have hm : Set.MapsTo (fun y : Fin N → E n => (y i, ∑ j, y j)) P (K i ×ˢ Kbar K) := by
      intro y hy
      exact ⟨hy i (Set.mem_univ i), y, fun j => hy j (Set.mem_univ j), rfl⟩
    exact (h1.2 i).comp
      (((continuous_apply i).prodMk
        (continuous_finsetSum _ (fun j _ => continuous_apply j))).continuousOn) hm
  have hfc : ContinuousOn f P := by
    apply continuousOn_pi.2
    intro i
    have hproj : Continuous (proj (K i)) :=
      LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
        simp only [NNReal.coe_one, one_mul, dist_eq_norm]
        exact proj_lipschitz (hne i) (hcl i) (hcv i) a b)
    exact hproj.comp_continuousOn (((continuous_apply i).continuousOn).sub (hphi i))
  have hfm : Set.MapsTo f P P := by
    intro y _ i _
    exact (isProj_proj (hne i) (hcl i) (hcv i) _).1
  obtain ⟨xs, hxsP, hfix⟩ := AGT.brouwer_fixed_point hPv hPc hPn f hfc hfm
  have hxsK : ∀ i, xs i ∈ K i := fun i => hxsP i (Set.mem_univ i)
  have hsol : IsVISol K F xs := by
    refine ⟨hxsK, fun y hy => Finset.sum_nonneg (fun i _ => ?_)⟩
    have hp := isProj_proj (hne i) (hcl i) (hcv i) (xs i - phi F xs i)
    have hfi : proj (K i) (xs i - phi F xs i) = xs i := congrFun hfix i
    rw [hfi] at hp
    have := isProj_inner_le (hcv i) hp (y i) (hy i)
    have e : xs i - phi F xs i - xs i = -(phi F xs i) := by abel
    rw [e, inner_neg_left, real_inner_comm] at this
    linarith
  refine ⟨xs, hsol, fun y hy => ?_⟩
  by_contra hne'
  have hpos := h2 y xs hy.1 hxsK hne'
  have a1 := hy.2 xs hxsK
  have a2 := hsol.2 y hy.1
  have : ∑ i, inner ℝ (phi F y i - phi F xs i) (y i - xs i) =
      -(∑ i, inner ℝ (xs i - y i) (phi F y i)) - ∑ i, inner ℝ (y i - xs i) (phi F xs i) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sub_left, real_inner_comm (y i - xs i), real_inner_comm (y i - xs i)]
    have : xs i - y i = -(y i - xs i) := by abel
    rw [this, inner_neg_left]
    ring
  unfold IsVISol IsVI at *
  linarith
