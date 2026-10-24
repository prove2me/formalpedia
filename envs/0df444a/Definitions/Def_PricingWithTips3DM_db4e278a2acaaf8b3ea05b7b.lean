-- Prove2me | Definitions.Def_PricingWithTips3DM_db4e278a2acaaf8b3ea05b7b
-- name    : PricingWithTips3DM_db4e278a2acaaf8b3ea05b7b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:56:59.86999+00:00
-- url     : https://prove2.me/theorems/acf41412-8ece-4d34-b247-6274ec7fd56e
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeOrdinal
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_b062d0f04915c2cc3bdb50d7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Decoding facts for the row-major address used by the fixed-shape table. -/

namespace PricingWithTips.FixedShapeOrdinal

open PricingWithTips.FixedShape3DM PricingWithTips.FixedShapeCell
open Hardness Hardness.Cert SatToMatching3DCode

abbrev Triple := PricingWithTips.FixedShapeCell.Triple

private theorem pairCode_injective_of_lt (n x₁ y₁ x₂ y₂ : Nat)
    (hy₁ : y₁ < n) (hy₂ : y₂ < n)
    (h : x₁ * n + y₁ = x₂ * n + y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le y₁) hy₁
  have hmod := congrArg (fun z => z % n) h
  have hy : y₁ = y₂ := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hy₁, Nat.mod_eq_of_lt hy₂] using hmod
  subst y₂
  have hdiv := congrArg (fun z => z / n) h
  rw [Nat.mul_comm x₁ n, Nat.mul_comm x₂ n] at hdiv
  have hx : x₁ = x₂ := by
    simpa [Nat.mul_add_div hn, Nat.div_eq_of_lt hy₁] using hdiv
  exact ⟨hx, rfl⟩

theorem ordinal_injective_of_lt (n : Nat) (t₁ t₂ : Triple)
    (h₁s : t₁.2.1 < n) (h₁d : t₁.2.2 < n)
    (h₂s : t₂.2.1 < n) (h₂d : t₂.2.2 < n)
    (h : FixedShapeSparseCells.ordinal n t₁ =
      FixedShapeSparseCells.ordinal n t₂) : t₁ = t₂ := by
  rcases t₁ with ⟨b₁, s₁, d₁⟩
  rcases t₂ with ⟨b₂, s₂, d₂⟩
  simp only at h₁s h₁d h₂s h₂d h ⊢
  rcases pairCode_injective_of_lt n (b₁ * n + s₁) d₁
      (b₂ * n + s₂) d₂ h₁d h₂d h with ⟨hbs, hd⟩
  rcases pairCode_injective_of_lt n b₁ s₁ b₂ s₂ h₁s h₂s hbs with
    ⟨hb, hs⟩
  simp [hb, hs, hd]

theorem ordinal_lt_cube (n : Nat) (t : Triple)
    (hb : t.1 < n) (hs : t.2.1 < n) (hd : t.2.2 < n) :
    FixedShapeSparseCells.ordinal n t < n ^ 3 := by
  unfold FixedShapeSparseCells.ordinal
  have hpair : t.1 * n + t.2.1 < n * n := by
    nlinarith
  have hfull : (t.1 * n + t.2.1) * n + t.2.2 < (n * n) * n := by
    nlinarith
  simpa [pow_succ, Nat.mul_assoc] using hfull

theorem cell_true_bounds (input : List CLRS.Chapter34.CNFSym) (t : Triple)
    (h : cell input t = true) :
    t.1 < dimension input ∧ t.2.1 < dimension input ∧
      t.2.2 < dimension input := by
  have hm : t ∈ numericTriples input := (cell_iff_numeric input t).mp h
  obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp hm
  subst t
  constructor
  · simpa [dimension, variableList, paddedCNF_length,
      SatToMatching3DCode.tripIdx] using SatToMatching3DCode.extIdx_lt u.1
  constructor
  · have hs := SatToMatching3DCode.slotIdx_lt u.2.1
    simp only [dimension, variableList, List.length_range, paddedCNF_length,
      SatToMatching3DCode.tripIdx] at hs ⊢
    convert hs using 1 <;> ring
  · have hd := SatToMatching3DCode.slotIdx_lt u.2.2
    simp only [dimension, variableList, List.length_range, paddedCNF_length,
      SatToMatching3DCode.tripIdx] at hd ⊢
    convert hd using 1 <;> ring

theorem ordinal_injective_on_true_cells
    (input : List CLRS.Chapter34.CNFSym) (t₁ t₂ : Triple)
    (h₁ : cell input t₁ = true) (h₂ : cell input t₂ = true)
    (hord : FixedShapeSparseCells.ordinal (dimension input) t₁ =
      FixedShapeSparseCells.ordinal (dimension input) t₂) : t₁ = t₂ := by
  rcases cell_true_bounds input t₁ h₁ with ⟨h₁b, h₁s, h₁d⟩
  rcases cell_true_bounds input t₂ h₂ with ⟨h₂b, h₂s, h₂d⟩
  exact ordinal_injective_of_lt (dimension input) t₁ t₂
    h₁s h₁d h₂s h₂d hord

theorem query_mem_edges_iff_cell
    (input : List CLRS.Chapter34.CNFSym) (t : Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, FixedShapeSparseCells.ordinal (dimension input) t) ∈
        FixedShapeSparseCells.edges input ↔
      cell input t = true := by
  constructor
  · intro he
    obtain ⟨u, hu, hedge⟩ := List.mem_map.mp he
    have hcu : cell input u = true :=
      (FixedShapeSparseCells.mem_triples_iff input u).mp hu
    rcases cell_true_bounds input u hcu with ⟨hub, hus, hud⟩
    have hord : FixedShapeSparseCells.ordinal (dimension input) u =
        FixedShapeSparseCells.ordinal (dimension input) t := by
      exact congrArg Prod.snd hedge
    have hut := ordinal_injective_of_lt (dimension input) u t
      hus hud hs hd hord
    simpa [hut] using hcu
  · intro hc
    apply List.mem_map.mpr
    exact ⟨t, (FixedShapeSparseCells.mem_triples_iff input t).mpr hc, rfl⟩

end PricingWithTips.FixedShapeOrdinal


