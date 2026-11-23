-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
-- name    : GroupTheoreticShannonCapacity_FractionGraphs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:36.246087+00:00
-- url     : https://prove2.me/theorems/3a8261cf-dfe0-48c6-afc0-a5a3a425feb1
-- title:
--   Fraction Graphs
-- statement:
--   Definitions and structural lemmas for Fraction Graphs, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity
open Matrix
def fractionGraph_scalingMap (a c : ℕ) [NeZero a] [NeZero c] : ZMod a → ZMod c :=
  fun x => (x.val * c / a : ℕ)
def finEquivZMod (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun := fun i => i.val
  invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
  left_inv := fun i => by simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv := fun z => by simp
lemma distMod_eq_one_iff (p : ℕ) [hp : NeZero p] (hp3 : 3 ≤ p) (u v : ZMod p) (hne : u ≠ v) :
    distMod p u v = 1 ↔ (u - v = 1 ∨ u - v = -1) := by
  have hp1 : p ≠ 1 := by omega
  have hone : (1 : ZMod p).val = 1 := ZMod.val_one'' hp1
  have hone_ne : (1 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.val_eq_zero _).mpr h
    rw [hone] at this
    omega
  have hneg_one : (-(1 : ZMod p)).val = p - 1 := by
    rw [ZMod.neg_val (1 : ZMod p)]
    simp [hone_ne, hone]
  simp only [distMod]
  have hd_pos : 0 < (u - v).val := by
    by_contra h
    push_neg at h
    have hzero : (u - v).val = 0 := Nat.le_zero.mp h
    have := (ZMod.val_eq_zero _).mp hzero
    exact hne (sub_eq_zero.mp this)
  have hd_lt : (u - v).val < p := (u - v).val_lt
  constructor
  · intro h
    have hmin : min (u - v).val (p - (u - v).val) = 1 := h
    -- Case split: either (u-v).val = 1 or (p - (u-v).val) = 1
    by_cases hcase : (u - v).val ≤ p - (u - v).val
    · -- min is (u - v).val
      have heq : (u - v).val = 1 := by
        rw [min_eq_left hcase] at hmin
        exact hmin
      left
      exact ZMod.val_injective p (heq.trans hone.symm)
    · -- min is (p - (u - v).val)
      push_neg at hcase
      have heq : p - (u - v).val = 1 := by
        rw [min_eq_right (le_of_lt hcase)] at hmin
        exact hmin
      right
      have hval : (u - v).val = p - 1 := by omega
      exact ZMod.val_injective p (hval.trans hneg_one.symm)
  · intro h
    cases h with
    | inl h1 =>
      rw [h1, hone]; omega
    | inr h1 =>
      rw [h1, hneg_one]; omega
theorem fractionGraph_two_eq_circulant (p : ℕ) [hp : NeZero p] (hp3 : 3 ≤ p) :
    fractionGraph p 2 = SimpleGraph.circulantGraph {(1 : ZMod p)} := by
  ext u v
  simp only [fractionGraph, distMod, SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff]
  constructor
  · intro ⟨hne, hdist⟩
    constructor
    · exact hne
    · have hd_pos : 0 < (u - v).val := by
        by_contra h; push_neg at h
        have hzero : (u - v).val = 0 := Nat.le_zero.mp h
        have := (ZMod.val_eq_zero _).mp hzero
        exact hne (sub_eq_zero.mp this)
      have hd_lt : (u - v).val < p := (u - v).val_lt
      have hmin_pos : 0 < min (u - v).val (p - (u - v).val) := by
        simp only [lt_min_iff]; exact ⟨hd_pos, by omega⟩
      have hmin_eq_one : min (u - v).val (p - (u - v).val) = 1 := by omega
      have hdist' : distMod p u v = 1 := hmin_eq_one
      rw [distMod_eq_one_iff p hp3 u v hne] at hdist'
      cases hdist' with
      | inl h1 => left; exact h1
      | inr h1 =>
        right
        have : v - u = -(u - v) := by ring
        rw [this, h1]; ring
  · intro ⟨hne, h⟩
    constructor
    · exact hne
    · have hdist' : distMod p u v = 1 := by
        rw [distMod_eq_one_iff p hp3 u v hne]
        cases h with
        | inl h1 => left; exact h1
        | inr h1 =>
          right
          calc u - v = -(v - u) := by ring
            _ = -1 := by rw [h1]
      simp only [distMod] at hdist'; omega
lemma fin_sub_val_eq_zmod_sub_val (p : ℕ) [NeZero p] (a b : Fin p) :
    (a - b).val = ((a.val : ZMod p) - (b.val : ZMod p)).val := by
  have hp : 0 < p := NeZero.pos p
  have ha_lt : a.val < p := a.isLt
  have hb_lt : b.val < p := b.isLt
  simp only [Fin.sub_def, Fin.val_mk]
  by_cases hle : b.val ≤ a.val
  · -- Case: a.val ≥ b.val, so (p - b + a) % p = a - b
    have heq : (p - b.val + a.val) % p = a.val - b.val := by
      have h1 : p - b.val + a.val = a.val - b.val + p := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.val - b.val < p)]
    rw [heq]
    have hsub : (a.val : ZMod p) - (b.val : ZMod p) = ((a.val - b.val : ℕ) : ZMod p) := by
      rw [← Nat.cast_sub hle]
    rw [hsub, ZMod.val_natCast_of_lt (by omega : a.val - b.val < p)]
  · -- Case: a.val < b.val, so (p - b + a) % p = p - (b - a)
    push_neg at hle
    have heq : (p - b.val + a.val) % p = p - (b.val - a.val) := by
      have h1 : p - b.val + a.val = p - (b.val - a.val) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : p - (b.val - a.val) < p)]
    rw [heq]
    -- Need: (a.val : ZMod p) - (b.val : ZMod p) has value p - (b.val - a.val)
    have hlt' : b.val - a.val < p := by omega
    have hne_zmod : ((b.val - a.val : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have := (ZMod.val_eq_zero _).mpr h
      rw [ZMod.val_natCast_of_lt hlt'] at this
      omega
    have hsub : (a.val : ZMod p) - (b.val : ZMod p) = -((b.val - a.val : ℕ) : ZMod p) := by
      have h1 : ((b.val - a.val : ℕ) : ZMod p) = (b.val : ZMod p) - (a.val : ZMod p) := by
        rw [Nat.cast_sub (le_of_lt hle)]
      rw [h1]; ring
    rw [hsub, ZMod.neg_val, if_neg hne_zmod, ZMod.val_natCast_of_lt hlt']
lemma fin_sub_eq_one_of_zmod_sub_eq_one (p : ℕ) [NeZero p] (hp1 : 1 < p) (a b : Fin p)
    (h : (a.val : ZMod p) - (b.val : ZMod p) = 1) : a - b = 1 := by
  have hzmod_val : ((a.val : ZMod p) - (b.val : ZMod p)).val = 1 := by
    rw [h, ZMod.val_one'' (by omega : p ≠ 1)]
  rw [← fin_sub_val_eq_zmod_sub_val] at hzmod_val
  have h1 : (1 : Fin p).val = 1 := Nat.mod_eq_of_lt hp1
  exact Fin.ext (hzmod_val.trans h1.symm)
lemma zmod_sub_eq_one_of_fin_sub_eq_one (p : ℕ) [NeZero p] (hp1 : 1 < p) (a b : Fin p)
    (h : a - b = 1) : (a.val : ZMod p) - (b.val : ZMod p) = 1 := by
  have hfin_val : (a - b).val = 1 := by rw [h]; exact Nat.mod_eq_of_lt hp1
  rw [fin_sub_val_eq_zmod_sub_val] at hfin_val
  exact (ZMod.val_eq_one hp1 _).mp hfin_val
def cycleGraph_iso_fractionGraph_two (p : ℕ) [hp : NeZero p] (hp2 : 2 ≤ p) :
    SimpleGraph.cycleGraph p ≃g fractionGraph p 2 := by
  -- Case split: p = 2 vs p ≥ 3
  by_cases heq : p = 2
  · -- p = 2: both graphs are complete on 2 vertices
    subst heq
    refine ⟨finEquivZMod 2, ?_⟩
    intro a b
    -- Both graphs on 2 vertices: adjacency iff distinct
    simp only [SimpleGraph.cycleGraph_adj, finEquivZMod, Equiv.coe_fn_mk, fractionGraph, distMod]
    revert a b
    decide
  · -- p ≥ 3: use circulant characterization
    have hp3 : 2 < p := Nat.lt_of_le_of_ne hp2 (Ne.symm heq)
    have hp3' : 3 ≤ p := hp3
    have hcycle : SimpleGraph.cycleGraph p = SimpleGraph.circulantGraph {(1 : Fin p)} := by
      obtain _ | n := p
      · exact (NeZero.ne 0 rfl).elim
      · exact SimpleGraph.cycleGraph_eq_circulantGraph n
    have hfrac : fractionGraph p 2 = SimpleGraph.circulantGraph {(1 : ZMod p)} :=
      fractionGraph_two_eq_circulant p hp3'
    rw [hcycle, hfrac]
    refine ⟨finEquivZMod p, ?_⟩
    intro a b
    simp only [SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff, finEquivZMod, Equiv.coe_fn_mk]
    have hp1 : 1 < p := by omega
    have ha_lt : a.val < p := a.isLt
    have hb_lt : b.val < p := b.isLt
    constructor
    · intro ⟨hne_zmod, h_zmod⟩
      constructor
      · intro heq_fin; rw [heq_fin] at hne_zmod; exact hne_zmod rfl
      · cases h_zmod with
        | inl hab_zmod => exact Or.inl (fin_sub_eq_one_of_zmod_sub_eq_one p hp1 a b hab_zmod)
        | inr hba_zmod => exact Or.inr (fin_sub_eq_one_of_zmod_sub_eq_one p hp1 b a hba_zmod)
    · intro ⟨hne_fin, h_fin⟩
      constructor
      · intro heq_zmod
        have ha_eq : (a.val : ZMod p).val = a.val := ZMod.val_natCast_of_lt ha_lt
        have hb_eq : (b.val : ZMod p).val = b.val := ZMod.val_natCast_of_lt hb_lt
        exact hne_fin (Fin.ext (by rw [← ha_eq, ← hb_eq, heq_zmod]))
      · cases h_fin with
        | inl hab_fin => exact Or.inl (zmod_sub_eq_one_of_fin_sub_eq_one p hp1 a b hab_fin)
        | inr hba_fin => exact Or.inr (zmod_sub_eq_one_of_fin_sub_eq_one p hp1 b a hba_fin)
lemma p_pos_of_neZero_prod (p' p : ℕ) [NeZero (p' * p)] : 0 < p := by
  by_contra h; push_neg at h
  have : p' * p = 0 := by simp [Nat.le_zero.mp h]
  exact NeZero.ne (p' * p) this
def fractionGraph_scalarMulMap (p' p : ℕ) [NeZero p'] [NeZero (p' * p)] :
    ZMod p' →+ ZMod (p' * p) where
  toFun x := (p * x.val : ℕ)
  map_zero' := by simp
  map_add' x y := by
    have hp'_pos : 0 < p' := NeZero.pos p'
    have hp_pos := p_pos_of_neZero_prod p' p
    have hxval_lt : p * x.val < p' * p := by
      calc p * x.val < p * p' := Nat.mul_lt_mul_of_pos_left x.val_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    have hyval_lt : p * y.val < p' * p := by
      calc p * y.val < p * p' := Nat.mul_lt_mul_of_pos_left y.val_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    have hsum_val_lt : p * (x + y).val < p' * p := by
      calc p * (x + y).val < p * p' := Nat.mul_lt_mul_of_pos_left (x + y).val_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    apply ZMod.val_injective (p' * p)
    rw [ZMod.val_cast_of_lt hsum_val_lt, ZMod.val_add x y]
    rw [ZMod.val_add, ZMod.val_cast_of_lt hxval_lt, ZMod.val_cast_of_lt hyval_lt]
    rw [← Nat.mul_add]
    -- Key: p * ((x.val + y.val) % p') = (p * (x.val + y.val)) % (p' * p)
    set a := x.val + y.val
    have hr_lt : a % p' < p' := Nat.mod_lt a hp'_pos
    have hpr_lt : p * (a % p') < p' * p := by
      calc p * (a % p') < p * p' := Nat.mul_lt_mul_of_pos_left hr_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    have hdiv : a = (a / p') * p' + a % p' := (Nat.div_add_mod' a p').symm
    have hcalc : p * a % (p' * p) = p * (a % p') := by
      conv_lhs => rw [hdiv]
      calc p * ((a / p') * p' + a % p') % (p' * p)
          = (p * ((a / p') * p') + p * (a % p')) % (p' * p) := by rw [Nat.mul_add]
        _ = ((a / p') * (p * p') + p * (a % p')) % (p' * p) := by ring_nf
        _ = ((a / p') * (p' * p) + p * (a % p')) % (p' * p) := by rw [Nat.mul_comm p p']
        _ = (p * (a % p') + (a / p') * (p' * p)) % (p' * p) := by ring_nf
        _ = p * (a % p') % (p' * p) := Nat.add_mul_mod_self_right _ _ _
        _ = p * (a % p') := Nat.mod_eq_of_lt hpr_lt
    exact hcalc.symm
end GroupTheoreticShannonCapacity


