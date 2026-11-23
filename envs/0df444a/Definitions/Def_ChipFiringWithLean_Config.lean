-- Prove2me | Definitions.Def_ChipFiringWithLean_Config
-- name    : ChipFiringWithLean_Config
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:44:47.659565+00:00
-- url     : https://prove2.me/theorems/16ba1fb6-f981-4b55-826e-f3c3a5e51e4c
-- title:
--   Config
-- statement:
--   Definitions and structural lemmas for Config, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
abbrev Vtilde {G : CFGraph} (q : G.V) : Finset G.V :=
  univ.filter (λ v => v ≠ q)
structure Config (G : CFGraph) (q : G.V) where
  /-- The divisor recording the chip count at each vertex. -/
  (chips : CFDiv G)
  /-- The distinguished vertex $q$ has no chips. -/
  (q_zero : chips q = 0)
  /-- All chip counts are nonnegative. -/
  (non_negative : ∀ v : G.V, chips v ≥ 0)
def config_degree {G : CFGraph} {q : G.V} (c : Config G q) : ℤ :=
  deg (c.chips)
def toDiv {G : CFGraph} {q : G.V} (d : ℤ) (c : Config G q) : CFDiv G :=
  c.chips + (d - config_degree c) • (one_chip q)
@[ext] lemma Config.ext {q : G.V} {c₁ c₂ : Config G q}
    (h : ∀ v : G.V, c₁.chips v = c₂.chips v) : c₁ = c₂ := by
  obtain ⟨vd₁, _, _⟩ := c₁
  obtain ⟨vd₂, _, _⟩ := c₂
  simp only [mk.injEq]
  exact funext h
lemma eq_config_iff_eq_chips {q : G.V} (c₁ c₂ : Config G q) :
  c₁ = c₂ ↔ c₁.chips = c₂.chips :=
  ⟨fun h => by rw [h], fun h => Config.ext (congrFun h)⟩
def to_qed {q : G.V} (d : ℤ) (c : Config G q) : q_eff_div G q :=
  {
    D := toDiv d c,
    h_eff := by
      intro v h_v
      dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
      simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero,
          ge_iff_le]
      exact c.non_negative v
  }
def toConfig {q : G.V} (D : q_eff_div G q) : Config G q := {
  chips := D.D - (D.D q) • (one_chip q)
  q_zero := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [one_chip]
    simp only [↓reduceIte, mul_one, sub_self]
  non_negative := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      simp only [zsmul_eq_mul, h_v, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq,
          one_chip_apply_v, mul_one, sub_self, ge_iff_le, Std.le_refl]
    . -- Case v ≠ q
      simp only [zsmul_eq_mul, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq, ne_eq,
          h_v, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero, ge_iff_le]
      exact D.h_eff v h_v
}
lemma config_degree_div_degree {q : G.V} (D : q_eff_div G q) : deg D.D = D.D q + config_degree (toConfig D) := by
  simp only [config_degree, toConfig, map_sub, map_zsmul, deg_one_chip, smul_eq_mul, mul_one]
  ring
@[simp] lemma toDiv_config_degree_add {q : G.V} (c : Config G q) (k : ℤ) :
  toDiv (config_degree c + k) c = c.chips + k • one_chip q := by
  dsimp only [toDiv]
  rw [show config_degree c + k - config_degree c = k by ring]
@[simp] lemma toDiv_config_degree_sub_one {q : G.V} (c : Config G q) :
  toDiv (config_degree c - 1) c = c.chips - one_chip q := by
  rw [show config_degree c - 1 = config_degree c + (-1) by ring]
  rw [toDiv_config_degree_add]
  simp only [Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]
@[simp] lemma deg_chips_sub_one_chip {q : G.V} (c : Config G q) :
  deg (c.chips - one_chip q) = config_degree c - 1 := by
  rw [map_sub, config_degree, deg_one_chip]
lemma div_of_config_of_div (D : q_eff_div G q) :
  toDiv (deg D.D) (toConfig D) = D.D := by
  funext v
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  by_cases h: v ∈ Vtilde q
  . -- Case v ∈ Vtilde q
    dsimp only [toConfig, Pi.sub_apply, Pi.smul_apply, Int.zsmul_eq_mul]
    have : v ≠ q := by
      intro h_eq_q
      rw [h_eq_q] at h
      simp only [Finset.mem_filter, mem_univ, ne_eq, not_true_eq_false, and_false] at h
    simp only [ne_eq, this, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero,
        zsmul_eq_mul, add_zero]
  . -- Case v ∉ Vtilde q
    have : v = q := by
      contrapose! h
      simp only [Finset.mem_filter, mem_univ, ne_eq, h, not_false_eq_true, and_self]
    rw [this]
    simp only [(toConfig D).q_zero, one_chip, ite_true, mul_one, zero_add]
    linarith [config_degree_div_degree D]
@[simp] lemma q_reduced_toDiv_toConfig (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) :
    toDiv (deg D) (toConfig ⟨D, h_qred.1⟩) = D :=
  div_of_config_of_div ⟨D, h_qred.1⟩
@[simp] lemma eval_toDiv_q {q : G.V} (d : ℤ) (c : Config G q) :
  toDiv d c q = d - config_degree c := by
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [c.q_zero, one_chip_apply_v, mul_one, zero_add]
@[simp] lemma eval_toDiv_ne_q {q v : G.V} (d : ℤ) (c : Config G q) (h_v : v ≠ q) :
  toDiv d c v = c.chips v := by
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero]
instance : PartialOrder (Config G q) := {
  le := λ c₁ c₂ => c₁.chips ≤ c₂.chips,
  le_refl := by
    intro _
    simp only [Std.le_refl],
  le_trans := by
    intro _ _ _ c1_le_c2 c2_le_c3
    exact le_trans c1_le_c2 c2_le_c3,
  le_antisymm := by
    intro c1 c2 h_le h_ge
    have h_eq := le_antisymm h_le h_ge
    exact (eq_config_iff_eq_chips c1 c2).mpr h_eq
}
def superstable (G : CFGraph) (q : G.V) (c : Config G q) : Prop :=
  ∀ S ⊆  Vtilde q, S.Nonempty →
    ∃ v ∈ S, c.chips v < outdeg_S G S v
def maximal_superstable (G : CFGraph) {q : G.V} (c : Config G q) : Prop :=
  superstable G q c ∧ ∀ c' : Config G q, superstable G q c' → c ≤ c' → c' = c
def is_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) : Prop :=
  match L with
  | [] => False
  | [x] => (x = q)
  | v :: w :: rest =>
      outdeg_S G (univ \ (w :: rest).toFinset) v > c.chips v
      -- v isn't in the set made out of w :: rest
      ∧ ¬ (w :: rest).contains v
      ∧ is_burn_list G c (w :: rest)
structure burn_list (G : CFGraph) {q : G.V} (c : Config G q) where
  (list : List G.V)
  (h_burn_list : is_burn_list G c list)
def burn_flow {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) : (G.V × G.V) → ℕ :=
  λ e => if (e.1 ∈ L.list) ∧ (L.list.idxOf e.2 < L.list.idxOf e.1) then num_edges G e.1 e.2 else 0


