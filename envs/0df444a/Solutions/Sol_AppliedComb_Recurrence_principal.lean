-- Prove2me | solution 1 for AppliedComb.Recurrence.principal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:05:39.909067+00:00
-- url     : https://prove2.me/submissions/1864a308-1666-41a2-9057-a77fccddf9f1

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance



namespace AppliedComb.Recurrence

lemma adv_pow_apply (p : ℕ) (f : ℤ → ℝ) (n : ℤ) : (advance ^ p) f n = f (n + p) := by
  induction p generalizing n with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply]
    show (advance ^ p) f (n + 1) = _
    rw [ih]
    congr 1; push_cast; ring

lemma opPoly_apply (k : ℕ) (c : Fin (k + 1) → ℝ) (f : ℤ → ℝ) (n : ℤ) :
    opPoly k c f n = ∑ i : Fin (k + 1), c i * f (n + ((k - (i : ℕ) : ℕ) : ℤ)) := by
  unfold opPoly
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, adv_pow_apply, smul_eq_mul]

/-- companion map, for k = m+1 -/
noncomputable def compT (m : ℕ) (c : Fin (m + 2) → ℝ) :
    (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun w j := if h : (j : ℕ) < m then w ⟨j + 1, by omega⟩
    else -(c 0)⁻¹ * ∑ i : Fin (m + 1), c i.succ * w i.rev
  map_add' w w' := by
    funext j; simp only [Pi.add_apply]
    split_ifs
    · rfl
    · simp only [mul_add, Finset.sum_add_distrib]
  map_smul' a w := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

lemma compT_inj (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) : Function.Injective (compT m c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h1 : ∀ j : ℕ, (hj : j < m) → w ⟨j + 1, by omega⟩ = 0 := by
    intro j hj
    have := congrFun hw ⟨j, by omega⟩
    simpa [compT, hj] using this
  have h2 := congrFun hw (Fin.last m)
  simp only [compT, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_last, lt_irrefl, dite_false,
    Pi.zero_apply] at h2
  have hs : ∑ i : Fin (m + 1), c i.succ * w i.rev = c (Fin.last (m + 1)) * w 0 := by
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp
    · intro i _ hi
      have : (i.rev : ℕ) ≠ 0 := by
        have := Fin.val_rev i
        have : (i : ℕ) ≠ m := fun h => hi (Fin.ext h)
        omega
      obtain ⟨j, hj⟩ : ∃ j, (i.rev : ℕ) = j + 1 := ⟨(i.rev : ℕ) - 1, by omega⟩
      have hjm : j < m := by have := i.rev.isLt; omega
      have : i.rev = ⟨j + 1, by omega⟩ := Fin.ext hj
      rw [this, h1 j hjm, mul_zero]
    · simp
  rw [hs] at h2
  have hw0 : w 0 = 0 := by
    have : (c 0)⁻¹ ≠ 0 := inv_ne_zero hc0
    have := mul_eq_zero.mp (neg_eq_zero.mp (by simpa [neg_mul] using h2) : (c 0)⁻¹ * (c (Fin.last (m + 1)) * w 0) = 0)
    rcases this with h | h
    · exact absurd h (inv_ne_zero hc0)
    · exact (mul_eq_zero.mp h).resolve_left hck
  funext i
  by_cases hi : (i : ℕ) = 0
  · have : i = 0 := Fin.ext hi
    rw [this, hw0]; rfl
  · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = j + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hjm : j < m := by have := i.isLt; omega
    have : i = ⟨j + 1, by omega⟩ := Fin.ext hj
    rw [this, h1 j hjm]; rfl


lemma opPoly_split (m : ℕ) (c : Fin (m + 2) → ℝ) (f : ℤ → ℝ) (n : ℤ) :
    opPoly (m + 1) c f n = c 0 * f (n + (m + 1 : ℕ)) +
      ∑ i : Fin (m + 1), c i.succ * f (n + (i.rev : ℕ)) := by
  rw [opPoly_apply, Fin.sum_univ_succ]
  congr 1

noncomputable def compG (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  LinearEquiv.ofInjectiveEndo (compT m c) (compT_inj m c hck hc0)

lemma compG_apply (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) (w : Fin (m + 1) → ℝ) : compG m c hck hc0 w = compT m c w := by
  simp [compG]

lemma zpow_succ_apply (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) (n : ℤ) (v : Fin (m + 1) → ℝ) :
    (compG m c hck hc0 ^ (n + 1)) v = compT m c ((compG m c hck hc0 ^ n) v) := by
  rw [show n + 1 = 1 + n from add_comm _ _, zpow_one_add, LinearEquiv.mul_apply, compG_apply]

lemma state_lemma (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) (v : Fin (m + 1) → ℝ) :
    ∀ j : ℕ, ∀ hj : j < m + 1, ∀ n : ℤ,
      (compG m c hck hc0 ^ n) v ⟨j, hj⟩ = (compG m c hck hc0 ^ (n + j)) v 0 := by
  intro j
  induction j with
  | zero => intro hj n; simp
  | succ j ih =>
    intro hj n
    have hjm : j < m := by omega
    have e1 : (compG m c hck hc0 ^ n) v ⟨j + 1, hj⟩ = (compG m c hck hc0 ^ (n + 1)) v ⟨j, by omega⟩ := by
      rw [zpow_succ_apply]
      simp [compT, hjm]
    rw [e1, ih (by omega) (n + 1)]
    rw [show n + 1 + (j : ℤ) = n + ((j + 1 : ℕ) : ℤ) by push_cast; ring]

lemma fv_mem (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) (v : Fin (m + 1) → ℝ) :
    (fun n : ℤ => (compG m c hck hc0 ^ n) v 0) ∈ solutionSpace (m + 1) c := by
  unfold solutionSpace
  rw [LinearMap.mem_ker]
  funext n
  rw [opPoly_split, Pi.zero_apply]
  have hS : ∀ i : Fin (m + 1), (compG m c hck hc0 ^ (n + ((i : ℕ) : ℤ))) v 0
      = (compG m c hck hc0 ^ n) v i := by
    intro i
    have := state_lemma m c hck hc0 v i i.isLt n
    simpa using this.symm
  have hL : (compG m c hck hc0 ^ (n + ((m + 1 : ℕ) : ℤ))) v 0
      = -(c 0)⁻¹ * ∑ i : Fin (m + 1), c i.succ * (compG m c hck hc0 ^ n) v i.rev := by
    have h1 := state_lemma m c hck hc0 v m (by omega) (n + 1)
    have e : n + 1 + (m : ℤ) = n + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at h1
    rw [← h1, zpow_succ_apply]
    simp [compT]
  rw [hL]
  simp_rw [hS]
  field_simp
  ring

noncomputable def solEquiv (m : ℕ) (c : Fin (m + 2) → ℝ) (hck : c (Fin.last (m + 1)) ≠ 0)
    (hc0 : c 0 ≠ 0) : solutionSpace (m + 1) c ≃ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun f := fun j => f.1 (j : ℕ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨_, fv_mem m c hck hc0 v⟩
  left_inv f := by
    obtain ⟨f, hf⟩ := f
    have hf' : ∀ n, opPoly (m + 1) c f n = 0 := fun n => by
      unfold solutionSpace at hf; rw [LinearMap.mem_ker] at hf; rw [hf]; rfl
    set G := compG m c hck hc0 with hG
    let s : ℤ → (Fin (m + 1) → ℝ) := fun n j => f (n + (j : ℕ))
    have step : ∀ n, s (n + 1) = G (s n) := by
      intro n
      rw [hG, compG_apply]
      funext j
      simp only [compT, LinearMap.coe_mk, AddHom.coe_mk, s]
      split_ifs with hj
      · congr 1; push_cast; ring
      · have hjm : (j : ℕ) = m := by have := j.isLt; omega
        have := hf' n
        rw [opPoly_split] at this
        rw [hjm]
        have e : n + 1 + (m : ℤ) = n + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
        push_cast at e this ⊢
        rw [e]
        field_simp
        linarith
    have hs : ∀ n : ℤ, s n = (G ^ n) (s 0) := by
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => rw [step, ih, show (n : ℤ) + 1 = 1 + n from add_comm _ _, zpow_one_add, LinearEquiv.mul_apply]
      | pred n ih =>
        apply G.injective
        rw [← step, show -(n : ℤ) - 1 + 1 = -n by ring, ih, ← LinearEquiv.mul_apply, ← zpow_one_add]
        congr 2; ring
    apply Subtype.ext
    funext n
    have := congrFun (hs n) 0
    simp only [s] at this
    have h0 : f n = f (n + (((0 : Fin (m + 1)) : ℕ) : ℤ)) := by simp
    show (compG m c hck hc0 ^ n) (fun j => f (j : ℕ)) 0 = f n
    rw [h0, this]
    simp [hG]
  right_inv v := by
    funext j
    simp only
    have := state_lemma m c hck hc0 v j j.isLt 0
    simp only [zero_add, zpow_zero] at this
    rw [← this]; rfl

theorem principal_core (k : ℕ) (hk : 0 < k) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) :
    Module.rank ℝ (solutionSpace k c) = k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [(solEquiv m c hck hc0).rank_eq, rank_fin_fun]

end AppliedComb.Recurrence

open AppliedComb.Recurrence


theorem solution (k : ℕ) (hk : 0 < k) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) :
    Module.rank ℝ (solutionSpace k c) = k := by
  exact principal_core k hk c hc0 hck
