-- Prove2me | solution 1 for AppliedComb.Recurrence.repeated_root
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:08:16.809867+00:00
-- url     : https://prove2.me/submissions/87a894a8-6e0c-48ac-9747-9c190c7ed2a7

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


lemma finrank_sol (m : ℕ) (c : Fin (m + 2) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last (m + 1)) ≠ 0) :
    FiniteDimensional ℝ (solutionSpace (m + 1) c) ∧
      Module.finrank ℝ (solutionSpace (m + 1) c) = m + 1 := by
  have e := solEquiv m c hck hc0
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_fin_fun]

lemma binom_eq (k : ℕ) (r : ℝ) :
    (advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k =
      opPoly k (fun i => (k.choose i : ℝ) * (-r) ^ (i : ℕ)) := by
  have hc : Commute advance (-(r • (1 : Module.End ℝ (ℤ → ℝ)))) :=
    ((Commute.one_right advance).smul_right r).neg_right
  rw [sub_eq_add_neg, hc.add_pow, opPoly,
    Fin.sum_univ_eq_sum_range (fun i => ((k.choose i : ℝ) * (-r) ^ i) • advance ^ (k - i)),
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ k := by simp at hj; omega
  simp only [add_tsub_cancel_right]
  rw [Nat.sub_sub_self hj, Nat.choose_symm hj]
  rw [show -(r • (1 : Module.End ℝ (ℤ → ℝ))) = (-r) • 1 by module]
  rw [smul_pow, one_pow, mul_smul_comm, mul_one]
  have hN : ((k.choose j : ℕ) : Module.End ℝ (ℤ → ℝ)) = (k.choose j : ℝ) • 1 := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_one]
  rw [hN, mul_smul_comm, mul_one, smul_smul, mul_comm]

lemma Lpow_e (r : ℝ) (hr : r ≠ 0) : ∀ d l : ℕ, l < d →
    ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ d) (fun n : ℤ => (n : ℝ) ^ l * r ^ n) = 0 := by
  have hL : ∀ l : ℕ, (advance - r • (1 : Module.End ℝ (ℤ → ℝ))) (fun n : ℤ => (n : ℝ) ^ l * r ^ n)
      = ∑ j ∈ Finset.range l, (r * (l.choose j : ℝ)) • (fun n : ℤ => (n : ℝ) ^ j * r ^ n) := by
    intro l
    funext n
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    show ((n + 1 : ℤ) : ℝ) ^ l * r ^ (n + 1) - r * ((n : ℝ) ^ l * r ^ n) = _
    rw [zpow_add_one₀ hr]
    push_cast
    rw [add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    rw [add_mul, Finset.sum_mul]
    have : ∀ j ∈ Finset.range l, (n : ℝ) ^ j * (l.choose j : ℝ) * (r ^ n * r)
        = r * (l.choose j : ℝ) * ((n : ℝ) ^ j * r ^ n) := fun j _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  intro d
  induction d with
  | zero => intro l hl; omega
  | succ d ih =>
    intro l hl
    rw [pow_succ, Module.End.mul_apply, hL, map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [map_smul, ih j (by simp at hj; omega), smul_zero]

lemma e_linindep (k : ℕ) (r : ℝ) (hr : r ≠ 0) :
    LinearIndependent ℝ (fun i : Fin k => (fun n : ℤ => (n : ℝ) ^ (i : ℕ) * r ^ n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let p : Polynomial ℝ := ∑ i : Fin k, Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)
  have hroot : ∀ t : ℕ, p.IsRoot (t : ℝ) := by
    intro t
    have := congrFun hg (t : ℤ)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hrt : r ^ (t : ℤ) ≠ 0 := zpow_ne_zero _ hr
    simp only [Polynomial.IsRoot, p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have h2 : (∑ i : Fin k, g i * (t : ℝ) ^ (i : ℕ)) * r ^ (t : ℤ) = 0 := by
      rw [Finset.sum_mul]; rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    exact (mul_eq_zero.mp h2).resolve_right hrt
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : ℝ)) Nat.cast_injective
    intro t; exact hroot t
  intro i
  have := congrArg (fun q => Polynomial.coeff q (i : ℕ)) hp
  simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [if_neg]
    intro h; exact hj (Fin.ext h.symm)
  · simp

theorem repeated_root_core (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ) :
    ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k) f = 0 ↔
      ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * (n : ℝ) ^ (i : ℕ) * r ^ n := by
  set e : Fin k → (ℤ → ℝ) := fun i => (fun n : ℤ => (n : ℝ) ^ (i : ℕ) * r ^ n) with he
  have hspan_le : Submodule.span ℝ (Set.range e) ≤
      LinearMap.ker ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Lpow_e r hr k i i.isLt
  have hsum : ∀ c : Fin k → ℝ, (∑ i, c i • e i) = fun n : ℤ => ∑ i : Fin k, c i * (n : ℝ) ^ (i : ℕ) * r ^ n := by
    intro c; funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, he]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  constructor
  · intro hf
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hker : LinearMap.ker ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ (m + 1)) =
        solutionSpace (m + 1) (fun i => ((m + 1).choose i : ℝ) * (-r) ^ (i : ℕ)) := by
      rw [binom_eq]; rfl
    obtain ⟨hfd, hfr⟩ := finrank_sol m (fun i => ((m + 1).choose i : ℝ) * (-r) ^ (i : ℕ))
      (by simp) (by simp [hr])
    rw [← hker] at hfd hfr
    have heq : Submodule.span ℝ (Set.range e) =
        LinearMap.ker ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ (m + 1)) := by
      apply Submodule.eq_of_le_of_finrank_eq hspan_le
      rw [hfr, finrank_span_eq_card (e_linindep (m + 1) r hr), Fintype.card_fin]
    have : f ∈ Submodule.span ℝ (Set.range e) := by rw [heq]; exact hf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp this
    refine ⟨c, fun n => ?_⟩
    rw [← hc, hsum]
  · rintro ⟨c, hc⟩
    have hf : f = ∑ i, c i • e i := by rw [hsum]; funext n; exact hc n
    have : f ∈ Submodule.span ℝ (Set.range e) := by
      rw [hf]; exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩
    exact hspan_le this

end AppliedComb.Recurrence

open AppliedComb.Recurrence


theorem solution (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ) :
    ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k) f = 0 ↔
      ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * (n : ℝ) ^ (i : ℕ) * r ^ n := by
  exact repeated_root_core k hk r hr f
