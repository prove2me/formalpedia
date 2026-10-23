-- Prove2me | solution 1 for AstromPOMDP.Bounds.equation_5_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T22:32:56.818508+00:00
-- url     : https://prove2.me/submissions/8374ea79-07ae-4965-8d53-f48511e818d2

import Mathlib
import Definitions.Def_AstromPOMDP_Bounds_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false

namespace AstromPOMDP.Bounds.Pf

open AstromPOMDP.Bounds

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

/-! ## Basic facts -/

lemma l1_nonneg (w : Belief St) : 0 ≤ l1 w := by
  unfold l1
  exact Finset.sum_nonneg fun i _ => abs_nonneg (w i)

lemma eq_zero_of_l1_eq_zero {w : Belief St} (h : l1 w = 0) : w = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (w i))).mp h i (Finset.mem_univ i)
  simpa using this

lemma z_nonneg (m : Model St Obs d N) {t : ℕ} {u : Control d} {w : Belief St} (hu : u ∈ m.U)
    (hw : ∀ s, 0 ≤ w s) (j : Obs) (i : St) : 0 ≤ z m t u w j i :=
  Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (m.q_nonneg _ _) (m.P_nonneg u hu _ _ _)) (hw s)

lemma z_smul (m : Model St Obs d N) (t : ℕ) (u : Control d) (c : ℝ) (w : Belief St) (j : Obs) :
    z m t u (c • w) j = c • z m t u w j := by
  funext i
  simp only [z, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma z_add (m : Model St Obs d N) (t : ℕ) (u : Control d) (a b : Belief St) (j : Obs) :
    z m t u (a + b) j = z m t u a j + z m t u b j := by
  funext i
  simp only [z, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma sum_z (m : Model St Obs d N) (t : ℕ) (u : Control d) (w : Belief St) :
    ∑ j, z m t u w j = predict m t u w := by
  funext i
  simp only [Finset.sum_apply, z, predict]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, m.q_sum]
  ring

lemma predict_nonneg (m : Model St Obs d N) {t : ℕ} {u : Control d} {w : Belief St} (hu : u ∈ m.U)
    (hw : ∀ s, 0 ≤ w s) (i : St) : 0 ≤ predict m t u w i :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (m.P_nonneg u hu _ _ _)

lemma posterior_eq (m : Model St Obs d N) (t : ℕ) (u : Control d) (w : Belief St) (j : Obs) :
    posterior m t u w j = (l1 (z m t u w j))⁻¹ • z m t u w j := by
  funext i
  simp only [posterior, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

/-! ## Homogeneous value recursion -/

noncomputable def Fh (m : Model St Obs d N) (k : ℕ) (W : Belief St → ℝ) (u : Control d)
    (w : Belief St) : ℝ :=
  ∑ i, m.g u i k * w i + ∑ j, W (z m k u w j)

noncomputable def Wr (m : Model St Obs d N) : ℕ → Belief St → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun w => ⨅ u : m.U, Fh m (N - n) (Wr m n) u.1 w

lemma cont_z (m : Model St Obs d N) (k : ℕ) (j : Obs) :
    Continuous fun p : Belief St × m.U => z m k p.2.1 p.1 j := by
  have hP : ∀ s i, Continuous fun p : Belief St × m.U => m.P p.2.1 (k + 1) s i := fun s i =>
    ((m.P_cont (k + 1) s i).comp_continuous continuous_subtype_val (fun x => x.2)).comp
      continuous_snd
  refine continuous_pi fun i => ?_
  simp only [z]
  exact continuous_finset_sum _ fun s _ =>
    (continuous_const.mul (hP s i)).mul ((continuous_apply s).comp continuous_fst)

lemma cont_Fh (m : Model St Obs d N) (k : ℕ) (W : Belief St → ℝ) (hW : Continuous W) :
    Continuous fun p : Belief St × m.U => Fh m k W p.2.1 p.1 := by
  have hg : ∀ i, Continuous fun p : Belief St × m.U => m.g p.2.1 i k := fun i =>
    ((m.g_cont i k).comp_continuous continuous_subtype_val (fun x => x.2)).comp continuous_snd
  simp only [Fh]
  exact (continuous_finset_sum _ fun i _ => (hg i).mul ((continuous_apply i).comp continuous_fst)).add
    (continuous_finset_sum _ fun j _ => hW.comp (cont_z m k j))

lemma Wr_cont (m : Model St Obs d N) : ∀ n, Continuous (Wr m n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    haveI : CompactSpace m.U := isCompact_iff_compactSpace.mp m.U_compact
    have := (isCompact_univ (X := m.U)).continuous_sInf
      (f := fun w (u : m.U) => Fh m (N - n) (Wr m n) u.1 w) (cont_Fh m _ _ ih)
    have h2 : Wr m (n + 1) =
        fun w => sInf ((fun u : m.U => Fh m (N - n) (Wr m n) u.1 w) '' Set.univ) := by
      funext w
      rw [Set.image_univ]
      rfl
    rw [h2]
    exact this

lemma Wr_smul (m : Model St Obs d N) : ∀ n, ∀ c : ℝ, 0 ≤ c → ∀ w, Wr m n (c • w) = c * Wr m n w := by
  intro n
  induction n with
  | zero => intro c _ w; simp [Wr]
  | succ n ih =>
    intro c hc w
    simp only [Wr]
    rw [Real.mul_iInf_of_nonneg hc]
    congr 1
    funext u
    simp only [Fh, z_smul, ih c hc, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

lemma Wr_zero_vec (m : Model St Obs d N) (n : ℕ) : Wr m n 0 = 0 := by
  have := Wr_smul m n 0 le_rfl 0
  simpa using this

lemma exists_min (m : Model St Obs d N) (k n : ℕ) (w : Belief St) :
    ∃ u ∈ m.U, IsMinOn (fun u => Fh m k (Wr m n) u w) m.U u := by
  refine m.U_compact.exists_isMinOn m.U_nonempty ?_
  rw [continuousOn_iff_continuous_restrict]
  exact (cont_Fh m k _ (Wr_cont m n)).comp (continuous_const.prodMk continuous_id)

lemma Wr_succ_le (m : Model St Obs d N) (n : ℕ) (w : Belief St) (u : Control d) (hu : u ∈ m.U) :
    Wr m (n + 1) w ≤ Fh m (N - n) (Wr m n) u w := by
  obtain ⟨u0, _, hmin⟩ := exists_min m (N - n) n w
  have hbdd : BddBelow (Set.range fun v : m.U => Fh m (N - n) (Wr m n) v.1 w) :=
    ⟨Fh m (N - n) (Wr m n) u0 w, by rintro _ ⟨v, rfl⟩; exact hmin v.2⟩
  show (⨅ v : m.U, Fh m (N - n) (Wr m n) v.1 w) ≤ _
  exact ciInf_le hbdd ⟨u, hu⟩

lemma Wr_succ_eq_of_min (m : Model St Obs d N) (n : ℕ) (w : Belief St) (u0 : Control d)
    (hu0 : u0 ∈ m.U) (hmin : IsMinOn (fun u => Fh m (N - n) (Wr m n) u w) m.U u0) :
    Wr m (n + 1) w = Fh m (N - n) (Wr m n) u0 w := by
  haveI : Nonempty m.U := m.U_nonempty.to_subtype
  refine le_antisymm (Wr_succ_le m n w u0 hu0) ?_
  show _ ≤ ⨅ v : m.U, Fh m (N - n) (Wr m n) v.1 w
  exact le_ciInf fun v => hmin v.2

/-- Selector of a minimizer at time `t`. -/
noncomputable def sel (m : Model St Obs d N) (t : ℕ) (w : Belief St) : Control d :=
  (exists_min m t (N - t) w).choose

lemma sel_mem (m : Model St Obs d N) (t : ℕ) (w : Belief St) : sel m t w ∈ m.U :=
  (exists_min m t (N - t) w).choose_spec.1

lemma Wr_at_le (m : Model St Obs d N) (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) (w : Belief St)
    (u : Control d) (hu : u ∈ m.U) :
    Wr m (N + 1 - t) w ≤ Fh m t (Wr m (N + 1 - (t + 1))) u w := by
  have h1 : N + 1 - t = (N - t) + 1 := by omega
  have h2 : N - (N - t) = t := by omega
  have h3 : N + 1 - (t + 1) = N - t := by omega
  rw [h1, h3]
  have := Wr_succ_le m (N - t) w u hu
  rwa [h2] at this

lemma Wr_at_eq (m : Model St Obs d N) (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) (w : Belief St) :
    Wr m (N + 1 - t) w = Fh m t (Wr m (N + 1 - (t + 1))) (sel m t w) w := by
  have h1 : N + 1 - t = (N - t) + 1 := by omega
  have h2 : N - (N - t) = t := by omega
  have h3 : N + 1 - (t + 1) = N - t := by omega
  rw [h1, h3]
  have hspec := (exists_min m t (N - t) w).choose_spec
  have hmin : IsMinOn (fun u => Fh m (N - (N - t)) (Wr m (N - t)) u w) m.U (sel m t w) := by
    rw [h2]; exact hspec.2
  have := Wr_succ_eq_of_min m (N - t) w (sel m t w) hspec.1 hmin
  rwa [h2] at this

/-! ## Link with `beliefStages` -/

lemma bellman_eq (m : Model St Obs d N) (k n : ℕ) (w : Belief St) (hw : ∀ s, 0 ≤ w s)
    (u : Control d) (hu : u ∈ m.U)
    (hB : ∀ v : Belief St, (∀ s, 0 ≤ v s) → beliefStages m n v = Wr m n v) :
    bellmanRHS m k (beliefStages m n) w u = Fh m k (Wr m n) u w := by
  unfold bellmanRHS Fh
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hz : l1 (z m k u w j) = 0
  · rw [hz, eq_zero_of_l1_eq_zero hz, Wr_zero_vec]
    simp
  · have hpn : ∀ i, 0 ≤ ((l1 (z m k u w j))⁻¹ • z m k u w j) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (l1_nonneg _)) (z_nonneg m hu hw j i)
    rw [posterior_eq, hB _ hpn, Wr_smul m n _ (inv_nonneg.mpr (l1_nonneg _)), ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

lemma beliefStages_eq (m : Model St Obs d N) :
    ∀ n (w : Belief St), (∀ s, 0 ≤ w s) → beliefStages m n w = Wr m n w := by
  intro n
  induction n with
  | zero => intro w _; rfl
  | succ n ih =>
    intro w hw
    show (⨅ u : m.U, bellmanRHS m (N - n) (beliefStages m n) w u.val) =
      ⨅ u : m.U, Fh m (N - n) (Wr m n) u.1 w
    congr 1
    funext u
    exact bellman_eq m (N - n) n w hw u.1 u.2 ih

/-! ## Path law -/

noncomputable def pathProb (m : Model St Obs d N) (c : Policy Obs d) :
    (n : ℕ) → (Fin n → St) → (Fin n → Obs) → ℝ
  | 0, _, _ => 1
  | 1, x, y => m.p1 (x 0) * m.q (x 0) (y 0)
  | n + 2, x, y =>
      pathProb m c (n + 1) (Fin.init x) (Fin.init y) *
        m.P (c (n + 1) (Fin.init y)) (n + 2) (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) *
        m.q (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))

noncomputable def JW (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) (X : ℕ → St)
    (Y : ℕ → Obs) : ℝ :=
  m.p1 (X 0) * m.q (X 0) (Y 0) *
    ∏ t ∈ Finset.Icc 1 (n - 1),
      m.P (c t (fun i : Fin t => Y i.val)) (t + 1) (X (t - 1)) (X t) * m.q (X t) (Y t)

lemma JW_congr (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) (hn : 1 ≤ n) (X X' : ℕ → St)
    (Y Y' : ℕ → Obs) (hX : ∀ k < n, X k = X' k) (hY : ∀ k < n, Y k = Y' k) :
    JW m c n X Y = JW m c n X' Y' := by
  unfold JW
  rw [hX 0 hn, hY 0 hn]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Finset.mem_Icc] at ht
  have h1 : t < n := by omega
  have hfun : (fun i : Fin t => Y i.val) = (fun i : Fin t => Y' i.val) :=
    funext fun i => hY _ (by have := i.isLt; omega)
  rw [hfun, hX t h1, hX (t - 1) (by omega), hY t h1]

lemma JW_succ (m : Model St Obs d N) (c : Policy Obs d) (k : ℕ) (X : ℕ → St) (Y : ℕ → Obs) :
    JW m c (k + 1 + 1) X Y = JW m c (k + 1) X Y *
      (m.P (c (k + 1) (fun i : Fin (k + 1) => Y i.val)) (k + 1 + 1) (X k) (X (k + 1)) *
        m.q (X (k + 1)) (Y (k + 1))) := by
  unfold JW
  rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  simp only [Nat.add_sub_cancel]
  ring

lemma ofNat_eq {M : ℕ} [NeZero M] (k : ℕ) (h : k < M) : Fin.ofNat M k = ⟨k, h⟩ :=
  Fin.ext (by simp [Nat.mod_eq_of_lt h])

lemma pathProb_eq (m : Model St Obs d N) (c : Policy Obs d) :
    ∀ n (x : Fin (n + 1) → St) (y : Fin (n + 1) → Obs),
      pathProb m c (n + 1) x y =
        JW m c (n + 1) (fun k => x (Fin.ofNat (n + 1) k)) (fun k => y (Fin.ofNat (n + 1) k)) := by
  intro n
  induction n with
  | zero =>
    intro x y
    show m.p1 (x 0) * m.q (x 0) (y 0) = m.p1 (x (Fin.ofNat 1 0)) * m.q (x (Fin.ofNat 1 0))
      (y (Fin.ofNat 1 0)) * ∏ t ∈ Finset.Icc 1 0, _
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, mul_one]
    rfl
  | succ n ih =>
    intro x y
    rw [JW_succ]
    show pathProb m c (n + 1) (Fin.init x) (Fin.init y) *
        m.P (c (n + 1) (Fin.init y)) (n + 2) (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) *
        m.q (x (Fin.last (n + 1))) (y (Fin.last (n + 1))) = _
    rw [ih, JW_congr m c (n + 1) (by omega) _ (fun k => x (Fin.ofNat (n + 1 + 1) k)) _
      (fun k => y (Fin.ofNat (n + 1 + 1) k))]
    · have hy : (fun i : Fin (n + 1) => y (Fin.ofNat (n + 1 + 1) i.val)) = Fin.init y := by
        funext i
        rw [ofNat_eq (M := n + 1 + 1) i.val (by have := i.isLt; omega)]
        rfl
      rw [hy, ofNat_eq (M := n + 1 + 1) n (by omega), ofNat_eq (M := n + 1 + 1) (n + 1) (by omega),
        mul_assoc]
      rfl
    · intro k hk
      show x (Fin.castSucc (Fin.ofNat (n + 1) k)) = x (Fin.ofNat (n + 1 + 1) k)
      rw [ofNat_eq (M := n + 1) k hk, ofNat_eq (M := n + 1 + 1) k (by omega)]
      rfl
    · intro k hk
      show y (Fin.castSucc (Fin.ofNat (n + 1) k)) = y (Fin.ofNat (n + 1 + 1) k)
      rw [ofNat_eq (M := n + 1) k hk, ofNat_eq (M := n + 1 + 1) k (by omega)]
      rfl

lemma jw_eq (m : Model St Obs d N) (c : Policy Obs d) (x : Fin N → St) (y : Fin N → Obs) :
    jointWeight m c x y = pathProb m c N x y := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := NeZero.ne N; omega⟩
  rw [pathProb_eq]
  rfl

lemma sum_Icc_one (f : ℕ → ℝ) : ∀ n, ∑ t ∈ Finset.Icc 1 n, f t = ∑ i ∈ Finset.range n, f (i + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_one f n, Finset.sum_range_succ]

noncomputable def costN (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) : ℝ :=
  ∑ x : Fin n → St, ∑ y : Fin n → Obs, pathProb m c n x y *
    ∑ i : Fin n, m.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y)) (x i) (i.val + 1)

lemma pathCost_eq (m : Model St Obs d N) (c : Policy Obs d) (x : Fin N → St) (y : Fin N → Obs) :
    pathCost m c x y =
      ∑ i : Fin N, m.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y)) (x i) (i.val + 1) := by
  unfold pathCost
  rw [sum_Icc_one, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : historyPrefix y (i.val + 1) = Fin.take (i.val + 1) i.isLt y := by
    funext j
    show y (Fin.ofNat N j.val) = y (Fin.castLE i.isLt j)
    rw [ofNat_eq (M := N) j.val (by have := j.isLt; have := i.isLt; omega)]
    rfl
  have h2 : x (Fin.ofNat N (i.val + 1 - 1)) = x i := by
    rw [Nat.add_sub_cancel, ofNat_eq (M := N) i.val i.isLt]
  rw [h1, h2]

lemma expectedCost_eq (m : Model St Obs d N) (c : Policy Obs d) :
    expectedCost m c = costN m c N := by
  unfold expectedCost costN
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [jw_eq, pathCost_eq]

/-! ## Forward vectors and marginals -/

noncomputable def alpha (m : Model St Obs d N) (c : Policy Obs d) :
    (t : ℕ) → (Fin t → Obs) → Belief St
  | 0, _ => fun _ => 0
  | 1, η => fun i => m.p1 i * m.q i (η 0)
  | t + 2, η => z m (t + 1) (c (t + 1) (Fin.init η)) (alpha m c (t + 1) (Fin.init η))
      (η (Fin.last (t + 1)))

lemma alpha_two (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) (y : Fin (n + 1 + 1) → Obs) :
    alpha m c (n + 1 + 1) y = z m (n + 1) (c (n + 1) (Fin.init y)) (alpha m c (n + 1) (Fin.init y))
      (y (Fin.last (n + 1))) := rfl

lemma alpha_snoc (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) (y : Fin (n + 1) → Obs) (b : Obs) :
    alpha m c (n + 1 + 1) (Fin.snoc y b) = z m (n + 1) (c (n + 1) y) (alpha m c (n + 1) y) b := by
  rw [alpha_two, Fin.init_snoc, Fin.snoc_last]

lemma alpha_nonneg (m : Model St Obs d N) (c : Policy Obs d) (hc : Admissible m c) :
    ∀ n, n ≤ N → ∀ (y : Fin (n + 1) → Obs) (s : St), 0 ≤ alpha m c (n + 1) y s := by
  intro n
  induction n with
  | zero => intro _ y s; exact mul_nonneg (m.p1_nonneg s) (m.q_nonneg s _)
  | succ n ih =>
    intro hn y s
    rw [alpha_two]
    exact z_nonneg m (hc (n + 1) (by omega) (by omega) _) (ih (by omega) _) _ s

lemma sum_snoc' {α : Type*} [Fintype α] {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ x' : Fin n → α, ∑ a : α, f (Fin.snoc x' a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma pathProb_snoc (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) (x : Fin (n + 1) → St) (a : St)
    (y : Fin (n + 1 + 1) → Obs) :
    pathProb m c (n + 1 + 1) (Fin.snoc x a) y = pathProb m c (n + 1) x (Fin.init y) *
      m.P (c (n + 1) (Fin.init y)) (n + 1 + 1) (x (Fin.last n)) a * m.q a (y (Fin.last (n + 1))) := by
  show pathProb m c (n + 1) (Fin.init (Fin.snoc x a : Fin (n + 2) → St)) (Fin.init y) *
      m.P (c (n + 1) (Fin.init y)) (n + 2) ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last n).castSucc)
        ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last (n + 1))) *
      m.q ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last (n + 1))) (y (Fin.last (n + 1))) = _
  rw [Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

lemma marg_last (m : Model St Obs d N) (c : Policy Obs d) :
    ∀ n (y : Fin (n + 1) → Obs) (s : St),
      ∑ x : Fin (n + 1) → St, (if x (Fin.last n) = s then pathProb m c (n + 1) x y else 0) =
        alpha m c (n + 1) y s := by
  intro n
  induction n with
  | zero =>
    intro y s
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) St)
      (fun x : Fin (0 + 1) → St => if x (Fin.last 0) = s then pathProb m c (0 + 1) x y else 0)
      (fun a => if a = s then m.p1 a * m.q a (y 0) else 0) (fun x => rfl)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  | succ n ih =>
    intro y s
    rw [alpha_two]
    simp only [z, ← ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [sum_snoc']
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [Fin.snoc_last, pathProb_snoc, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring

lemma marg (m : Model St Obs d N) (c : Policy Obs d) (k : ℕ) (hU : ∀ y' : Fin (k + 1) → Obs, c (k + 1) y' ∈ m.U)
    (G : (Fin (k + 1) → St) → (Fin (k + 1) → Obs) → ℝ) :
    ∑ x : Fin (k + 1 + 1) → St, ∑ y : Fin (k + 1 + 1) → Obs,
        pathProb m c (k + 1 + 1) x y * G (Fin.init x) (Fin.init y) =
      ∑ x' : Fin (k + 1) → St, ∑ y' : Fin (k + 1) → Obs, pathProb m c (k + 1) x' y' * G x' y' := by
  simp only [sum_snoc' (n := k + 1) (α := St), sum_snoc' (n := k + 1) (α := Obs), pathProb_snoc,
    Fin.init_snoc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have hP := m.P_sum _ (hU y') (k + 1 + 1) (x' (Fin.last k))
  rw [show pathProb m c (k + 1) x' y' * G x' y' = ∑ a, ∑ b, pathProb m c (k + 1) x' y' * G x' y' *
      (m.P (c (k + 1) y') (k + 1 + 1) (x' (Fin.last k)) a * m.q a b) by
    simp only [← Finset.mul_sum, m.q_sum, mul_one, hP]]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def stepCost (m : Model St Obs d N) (c : Policy Obs d) (t : ℕ) : ℝ :=
  ∑ y : Fin t → Obs, ∑ s, m.g (c t y) s t * alpha m c t y s

lemma costN_succ (m : Model St Obs d N) (c : Policy Obs d) (hc : Admissible m c) (n : ℕ)
    (hn : n + 1 ≤ N) : costN m c (n + 1) = costN m c n + stepCost m c (n + 1) := by
  have part2 : ∑ x : Fin (n + 1) → St, ∑ y : Fin (n + 1) → Obs, pathProb m c (n + 1) x y *
      m.g (c ((Fin.last n).val + 1) (Fin.take ((Fin.last n).val + 1) (Fin.last n).isLt y))
        (x (Fin.last n)) ((Fin.last n).val + 1) = stepCost m c (n + 1) := by
    unfold stepCost
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [← marg_last, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact mul_comm _ _
  have part1 : ∑ x : Fin (n + 1) → St, ∑ y : Fin (n + 1) → Obs, pathProb m c (n + 1) x y *
      ∑ i : Fin n, m.g (c ((Fin.castSucc i).val + 1)
        (Fin.take ((Fin.castSucc i).val + 1) (Fin.castSucc i).isLt y))
          (x (Fin.castSucc i)) ((Fin.castSucc i).val + 1) = costN m c n := by
    cases n with
    | zero => simp [costN]
    | succ k =>
      exact marg m c k (fun y' => hc (k + 1) (by omega) (by omega) y')
        (fun x' y' => ∑ i : Fin (k + 1),
          m.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y')) (x' i) (i.val + 1))
  rw [← part1, ← part2]
  unfold costN
  simp only [Fin.sum_univ_castSucc, mul_add, Finset.sum_add_distrib]

/-! ## Telescoping -/

noncomputable def Φ (m : Model St Obs d N) (c : Policy Obs d) (t : ℕ) : ℝ :=
  ∑ y : Fin t → Obs, Wr m (N + 1 - t) (alpha m c t y)

lemma Phi_succ (m : Model St Obs d N) (c : Policy Obs d) (n : ℕ) :
    Φ m c (n + 1 + 1) = ∑ y' : Fin (n + 1) → Obs, ∑ b,
      Wr m (N + 1 - (n + 1 + 1)) (z m (n + 1) (c (n + 1) y') (alpha m c (n + 1) y') b) := by
  unfold Φ
  rw [sum_snoc']
  simp only [alpha_snoc]

lemma Phi_step (m : Model St Obs d N) (c : Policy Obs d) (hc : Admissible m c) (n : ℕ)
    (hn : n + 1 ≤ N) : Φ m c (n + 1) ≤ stepCost m c (n + 1) + Φ m c (n + 1 + 1) := by
  rw [Phi_succ]
  unfold Φ stepCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y' _ => ?_
  exact Wr_at_le m (n + 1) (by omega) hn (alpha m c (n + 1) y') (c (n + 1) y')
    (hc (n + 1) (by omega) hn y')

/-- Forward vectors of the optimal feedback policy. -/
noncomputable def alphaS (m : Model St Obs d N) : (t : ℕ) → (Fin t → Obs) → Belief St
  | 0, _ => fun _ => 0
  | 1, η => fun i => m.p1 i * m.q i (η 0)
  | t + 2, η => z m (t + 1) (sel m (t + 1) (alphaS m (t + 1) (Fin.init η)))
      (alphaS m (t + 1) (Fin.init η)) (η (Fin.last (t + 1)))

noncomputable def cS (m : Model St Obs d N) : Policy Obs d := fun t h => sel m t (alphaS m t h)

lemma cS_adm (m : Model St Obs d N) : Admissible m (cS m) := fun t _ _ h => sel_mem m t _

lemma alpha_cS (m : Model St Obs d N) : ∀ (t : ℕ) (η : Fin t → Obs), alpha m (cS m) t η = alphaS m t η
  | 0, _ => rfl
  | 1, _ => rfl
  | t + 2, η => by
    show z m (t + 1) (cS m (t + 1) (Fin.init η)) (alpha m (cS m) (t + 1) (Fin.init η))
        (η (Fin.last (t + 1))) =
      z m (t + 1) (sel m (t + 1) (alphaS m (t + 1) (Fin.init η))) (alphaS m (t + 1) (Fin.init η))
        (η (Fin.last (t + 1)))
    rw [alpha_cS m (t + 1) (Fin.init η)]
    rfl

lemma Phi_step_eq (m : Model St Obs d N) (n : ℕ) (hn : n + 1 ≤ N) :
    Φ m (cS m) (n + 1) = stepCost m (cS m) (n + 1) + Φ m (cS m) (n + 1 + 1) := by
  rw [Phi_succ]
  unfold Φ stepCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have h := Wr_at_eq m (n + 1) (by omega) hn (alpha m (cS m) (n + 1) y')
  have hc : cS m (n + 1) y' = sel m (n + 1) (alpha m (cS m) (n + 1) y') := by
    show sel m (n + 1) (alphaS m (n + 1) y') = _
    rw [alpha_cS]
  rw [hc]
  exact h

lemma Phi_last (m : Model St Obs d N) (c : Policy Obs d) : Φ m c (N + 1) = 0 := by
  unfold Φ
  simp [Wr]

lemma Phi_one (m : Model St Obs d N) (c : Policy Obs d) :
    Φ m c 1 = ∑ j, Wr m N (fun i => m.p1 i * m.q i j) := by
  unfold Φ
  rw [show N + 1 - 1 = N by omega]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) Obs) _ _ fun y => rfl

lemma tele_le (m : Model St Obs d N) (c : Policy Obs d) (hc : Admissible m c) :
    ∀ n, n ≤ N → Φ m c 1 ≤ costN m c n + Φ m c (n + 1) := by
  intro n
  induction n with
  | zero => intro _; simp [costN]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := Phi_step m c hc n hn
    rw [costN_succ m c hc n hn]
    linarith

lemma tele_eq (m : Model St Obs d N) :
    ∀ n, n ≤ N → Φ m (cS m) 1 = costN m (cS m) n + Φ m (cS m) (n + 1) := by
  intro n
  induction n with
  | zero => intro _; simp [costN]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := Phi_step_eq m n hn
    rw [costN_succ m _ (cS_adm m) n hn]
    linarith

theorem opt_eq (m : Model St Obs d N) :
    optimalCost m = ∑ j, Wr m N (fun i => m.p1 i * m.q i j) := by
  have hlow : ∀ c, Admissible m c → ∑ j, Wr m N (fun i => m.p1 i * m.q i j) ≤ expectedCost m c := by
    intro c hc
    have := tele_le m c hc N le_rfl
    rw [Phi_last, Phi_one, add_zero] at this
    rw [expectedCost_eq]
    exact this
  have heq : expectedCost m (cS m) = ∑ j, Wr m N (fun i => m.p1 i * m.q i j) := by
    have := tele_eq m N le_rfl
    rw [Phi_last, Phi_one, add_zero] at this
    rw [expectedCost_eq]
    exact this.symm
  have hL : IsLeast {v : ℝ | ∃ c : Policy Obs d, Admissible m c ∧ v = expectedCost m c}
      (∑ j, Wr m N (fun i => m.p1 i * m.q i j)) :=
    ⟨⟨cS m, cS_adm m, heq.symm⟩, by rintro v ⟨c, hc, rfl⟩; exact hlow c hc⟩
  unfold optimalCost
  exact hL.csInf_eq

/-! ## The value `V` at the first output -/

lemma fop_nonneg (m : Model St Obs d N) (j : Obs) : 0 ≤ firstOutputProb m j :=
  Finset.sum_nonneg fun s _ => mul_nonneg (m.p1_nonneg s) (m.q_nonneg s j)

lemma fb_nonneg (m : Model St Obs d N) (j : Obs) (i : St) : 0 ≤ firstBelief m j i :=
  div_nonneg (mul_nonneg (m.p1_nonneg i) (m.q_nonneg i j)) (fop_nonneg m j)

lemma firstExp_V (m : Model St Obs d N) :
    firstExpectation m (V m 1) = ∑ j, Wr m N (fun i => m.p1 i * m.q i j) := by
  unfold firstExpectation V
  rw [show N + 1 - 1 = N by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [beliefStages_eq m N _ (fb_nonneg m j),
    ← Wr_smul m N (firstOutputProb m j) (fop_nonneg m j) (firstBelief m j)]
  by_cases hp : firstOutputProb m j = 0
  · have h0 : (fun i => m.p1 i * m.q i j) = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (m.p1_nonneg i) (m.q_nonneg i j))).mp hp i (Finset.mem_univ i)
      simpa using this
    rw [hp, h0, zero_smul]
  · congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, firstBelief]
    field_simp

/-! ## Complete-information lower bound -/

lemma complete_bdd (m : Model St Obs d N) (t : ℕ) (Sn : St → ℝ) (i : St) :
    BddBelow (Set.range fun v : m.U => completeRHS m t Sn i v.1) := by
  have hg : Continuous fun v : m.U => m.g v.1 i t :=
    (m.g_cont i t).comp_continuous continuous_subtype_val (fun x => x.2)
  have hP : ∀ j, Continuous fun v : m.U => m.P v.1 (t + 1) i j := fun j =>
    (m.P_cont (t + 1) i j).comp_continuous continuous_subtype_val (fun x => x.2)
  have hc : Continuous fun v : m.U => completeRHS m t Sn i v.1 := by
    unfold completeRHS
    exact hg.add (continuous_finset_sum _ fun j _ => (hP j).mul continuous_const)
  haveI : CompactSpace m.U := isCompact_iff_compactSpace.mp m.U_compact
  exact (isCompact_range hc).bddBelow

lemma lowS (m : Model St Obs d N) :
    ∀ n (w : Belief St), (∀ s, 0 ≤ w s) → ∑ i, completeStages m n i * w i ≤ Wr m n w := by
  intro n
  induction n with
  | zero => intro w _; simp [completeStages, Wr]
  | succ n ih =>
    intro w hw
    haveI : Nonempty m.U := m.U_nonempty.to_subtype
    show _ ≤ ⨅ u : m.U, Fh m (N - n) (Wr m n) u.1 w
    refine le_ciInf fun u => ?_
    have h1 : ∑ i, completeStages m (n + 1) i * w i ≤
        ∑ i, completeRHS m (N - n) (completeStages m n) i u.1 * w i := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hw i)
      exact ciInf_le (complete_bdd m (N - n) _ i) u
    have h2 : ∑ j, ∑ i, completeStages m n i * z m (N - n) u.1 w j i ≤
        ∑ j, Wr m n (z m (N - n) u.1 w j) :=
      Finset.sum_le_sum fun j _ => ih _ (z_nonneg m u.2 hw j)
    have h3 : ∑ j, ∑ i, completeStages m n i * z m (N - n) u.1 w j i =
        ∑ i, (∑ j, m.P u.1 (N - n + 1) i j * completeStages m n j) * w i := by
      rw [Finset.sum_comm]
      have : ∀ i, ∑ j, completeStages m n i * z m (N - n) u.1 w j i =
          completeStages m n i * predict m (N - n) u.1 w i := by
        intro i
        rw [← Finset.mul_sum, ← sum_z]
        simp [Finset.sum_apply]
      simp only [this, predict, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    unfold Fh
    unfold completeRHS at h1
    simp only [add_mul, Finset.sum_add_distrib] at h1
    linarith

lemma prime_le (m : Model St Obs d N) :
    firstExpectation m (Vprime m 1) ≤ firstExpectation m (V m 1) := by
  unfold firstExpectation Vprime S V
  rw [show N + 1 - 1 = N by omega]
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (fop_nonneg m j)
  rw [beliefStages_eq m N _ (fb_nonneg m j)]
  exact lowS m N _ (fb_nonneg m j)

/-! ## Open-loop upper bound -/

lemma Wr_superadd (m : Model St Obs d N) :
    ∀ n (a b : Belief St), (∀ s, 0 ≤ a s) → (∀ s, 0 ≤ b s) →
      Wr m n a + Wr m n b ≤ Wr m n (a + b) := by
  intro n
  induction n with
  | zero => intro a b _ _; simp [Wr]
  | succ n ih =>
    intro a b ha hb
    haveI : Nonempty m.U := m.U_nonempty.to_subtype
    show _ ≤ ⨅ u : m.U, Fh m (N - n) (Wr m n) u.1 (a + b)
    refine le_ciInf fun u => ?_
    have h1 := Wr_succ_le m n a u.1 u.2
    have h2 := Wr_succ_le m n b u.1 u.2
    have h3 : Fh m (N - n) (Wr m n) u.1 a + Fh m (N - n) (Wr m n) u.1 b ≤
        Fh m (N - n) (Wr m n) u.1 (a + b) := by
      unfold Fh
      have h4 : ∑ j, Wr m n (z m (N - n) u.1 a j) + ∑ j, Wr m n (z m (N - n) u.1 b j) ≤
          ∑ j, Wr m n (z m (N - n) u.1 (a + b) j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [z_add]
        exact ih _ _ (z_nonneg m u.2 ha j) (z_nonneg m u.2 hb j)
      have h5 : ∑ i, m.g u.1 i (N - n) * (a + b) i =
          ∑ i, m.g u.1 i (N - n) * a i + ∑ i, m.g u.1 i (N - n) * b i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
      linarith
    linarith

lemma Wr_sum_le (m : Model St Obs d N) (n : ℕ) (f : Obs → Belief St) (hf : ∀ j s, 0 ≤ f j s) :
    ∀ s : Finset Obs, ∑ j ∈ s, Wr m n (f j) ≤ Wr m n (∑ j ∈ s, f j) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp [Wr_zero_vec]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ x, 0 ≤ (∑ j ∈ s, f j) x := fun x => by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun j _ => hf j x
    linarith [Wr_superadd m n (f a) (∑ j ∈ s, f j) (hf a) hs]

lemma lowO (m : Model St Obs d N) :
    ∀ n (w : Belief St), (∀ s, 0 ≤ w s) → Wr m n w ≤ openStages m n w := by
  intro n
  induction n with
  | zero => intro w _; simp [Wr, openStages]
  | succ n ih =>
    intro w hw
    haveI : Nonempty m.U := m.U_nonempty.to_subtype
    show _ ≤ ⨅ u : m.U, openRHS m (N - n) (openStages m n) w u.1
    refine le_ciInf fun u => ?_
    have h1 := Wr_succ_le m n w u.1 u.2
    have h2 := Wr_sum_le m n (fun j => z m (N - n) u.1 w j) (fun j s => z_nonneg m u.2 hw j s)
      Finset.univ
    have h2' : ∑ j, Wr m n (z m (N - n) u.1 w j) ≤ Wr m n (predict m (N - n) u.1 w) := by
      rw [← sum_z]
      exact h2
    have h3 := ih (predict m (N - n) u.1 w) (predict_nonneg m u.2 hw)
    unfold Fh at h1
    unfold openRHS
    linarith

lemma double_ge (m : Model St Obs d N) :
    firstExpectation m (V m 1) ≤ firstExpectation m (Vdouble m 1) := by
  unfold firstExpectation V Vdouble
  rw [show N + 1 - 1 = N by omega]
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (fop_nonneg m j)
  rw [beliefStages_eq m N _ (fb_nonneg m j)]
  exact lowO m N _ (fb_nonneg m j)

end AstromPOMDP.Bounds.Pf

open AstromPOMDP.Bounds in
theorem solution {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
    {d N : ℕ} [NeZero N] (m : Model St Obs d N) :
    optimalCost m = firstExpectation m (V m 1) ∧
    firstExpectation m (Vprime m 1) ≤ optimalCost m ∧
    optimalCost m ≤ firstExpectation m (Vdouble m 1) := by
  have e : optimalCost m = firstExpectation m (V m 1) :=
    (AstromPOMDP.Bounds.Pf.opt_eq m).trans (AstromPOMDP.Bounds.Pf.firstExp_V m).symm
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    exact AstromPOMDP.Bounds.Pf.prime_le m
  · rw [e]
    exact AstromPOMDP.Bounds.Pf.double_ge m
