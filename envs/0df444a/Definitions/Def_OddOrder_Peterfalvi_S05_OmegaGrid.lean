-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_OmegaGrid
-- name    : OddOrder_Peterfalvi_S05_OmegaGrid
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:01:08.073079+00:00
-- url     : https://prove2.me/theorems/67f29a97-9ad2-408e-a3e0-30e6e5240ef4
-- title:
--   Peterfalvi §5: the (3.3) $\omega$-grid indexed by $\mathrm{Fin}\,|W_1| \times \mathrm{Fin}\,|W_2|$
-- statement:
--   Formalizes the $\omega$-grid of Peterfalvi (3.3) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §3), indexed by $\mathrm{Fin}\,|W_1| \times \mathrm{Fin}\,|W_2|$. The file is a bridge leaf on the Feit–Thompson critical path.
--
--   Main declarations: `charBaseEquiv` (An arbitrary reindexing Fin |H| ≃ Ĥ of a subgroup-dual, from the cardinality match |Ĥ| =…); `charEquiv` (The reindexing `Fin |H| ≃ Ĥ` pinned at `0 ↦ 1` (trivial character), by composing…); `omegaGrid` (Peterfalvi (3.3) ω-grid).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_OmegaGrid.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_OmegaGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G)

/-- An arbitrary reindexing `Fin |H| ≃ Ĥ` of a subgroup-dual, from the cardinality
match `|Ĥ| = |H|` (`card_charGroup_subgroupOf`, Pontryagin self-duality). -/
noncomputable def charBaseEquiv {H : Subgroup G} (hHW : H ≤ hyp.W) :
    Fin (Nat.card H) ≃ ((H.subgroupOf hyp.W) →* ℂˣ) :=
  haveI : Fintype ((H.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  (Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact hyp.card_charGroup_subgroupOf hHW)).symm

/-- The reindexing `Fin |H| ≃ Ĥ` pinned at `0 ↦ 1` (trivial character), by composing
`charBaseEquiv` with the transposition moving the trivial character to index `0`.
Generalizes `S06.…w1CharEquiv` to any subgroup `H ≤ W`. -/
noncomputable def charEquiv {H : Subgroup G} (hHW : H ≤ hyp.W) [NeZero (Nat.card H)] :
    Fin (Nat.card H) ≃ ((H.subgroupOf hyp.W) →* ℂˣ) :=
  (Equiv.swap (0 : Fin (Nat.card H)) ((hyp.charBaseEquiv hHW).symm 1)).trans
    (hyp.charBaseEquiv hHW)

@[simp] theorem charEquiv_zero {H : Subgroup G} (hHW : H ≤ hyp.W) [NeZero (Nat.card H)] :
    hyp.charEquiv hHW 0 = 1 := by
  rw [charEquiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- **Peterfalvi (3.3) ω-grid**, indexed by `Fin |W₁| × Fin |W₂|` with the
distinguished `0`-indices = trivial duals.  This is the family
`S15.Hypothesis.omega` is pinned to. -/
noncomputable def omegaGrid [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)] :
    Fin (Nat.card hyp.W1) → Fin (Nat.card hyp.W2) → ClassFunction hyp.W ℂ :=
  fun i j =>
    (hyp.omega (hyp.omegaProdChar
      (hyp.charEquiv hyp.W1_le_W i) (hyp.charEquiv hyp.W2_le_W j)) :
        ClassFunction hyp.W ℂ)

/-- **Peterfalvi (3.3) anchor**: `ω_{00} = 1_W` (the trivial class function). -/
@[simp] theorem omegaGrid_zero_zero [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)] :
    hyp.omegaGrid 0 0 = trivialClassFunction hyp.W := by
  rw [omegaGrid, hyp.charEquiv_zero hyp.W1_le_W, hyp.charEquiv_zero hyp.W2_le_W,
    hyp.omegaProdChar_one_one]
  ext w
  simp

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


