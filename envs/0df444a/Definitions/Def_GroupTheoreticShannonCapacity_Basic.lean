-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_Basic
-- name    : GroupTheoreticShannonCapacity_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:19.835705+00:00
-- url     : https://prove2.me/theorems/c2ddf839-dbf9-4407-a47f-6693a0b08275
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity
def strongPower_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (n : ℕ) : strongPower G n ≃g strongPower H n where
  toEquiv := Equiv.piCongrRight (fun _ => f.toEquiv)
  map_rel_iff' := by
    intro x y
    simp only [strongPower, Equiv.piCongrRight_apply, Pi.map_apply]
    constructor
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq; exact hne (by simp only [heq])
      · cases h i with
        | inl heq => left; exact f.toEquiv.injective heq
        | inr hadj => right; exact f.map_rel_iff'.mp hadj
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq
        apply hne
        have : ∀ i, f.toEquiv (x i) = f.toEquiv (y i) := congr_fun heq
        funext i
        exact f.toEquiv.injective (this i)
      · cases h i with
        | inl heq => left; exact congr_arg f.toEquiv heq
        | inr hadj => right; exact f.map_rel_iff'.mpr hadj
noncomputable def shannonCapacity (G : SimpleGraph V) [Fintype V] : ℝ :=
  ⨆ n : ℕ, ((strongPower G (n + 1)).indepNum : ℝ) ^ (1 / (n + 1 : ℝ))
@[to_additive /-- The additive subgroup independence number α_g(Γ): the maximum cardinality of
    an AddSubgroup that is an independent set in Γ -/]
noncomputable def subgroupIndependenceNumber {G : Type*} [Group G] [Fintype G]
    (Γ : SimpleGraph G) : ℕ := by
  classical
  exact sSup { n : ℕ | ∃ H : Subgroup G, Γ.IsIndepSet (H : Set G) ∧ Nat.card H = n }
@[to_additive /-- The additive subgroup Shannon capacity Θ_g(Γ) = sup_{n≥1} α_g(Γ^⊠n)^(1/n)
    for Cayley graphs over additive groups -/]
noncomputable def subgroupShannonCapacity {G : Type*} [Group G] [Fintype G]
    (Γ : SimpleGraph G) : ℝ :=
  ⨆ n : ℕ, (subgroupIndependenceNumber (strongPower Γ (n + 1)) : ℝ) ^ (1 / (n + 1 : ℝ))
end GroupTheoreticShannonCapacity


