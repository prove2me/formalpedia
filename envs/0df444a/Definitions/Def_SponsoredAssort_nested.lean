-- Prove2me | Definitions.Def_SponsoredAssort_nested
-- name    : SponsoredAssort_nested
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:02.903493+00:00
-- url     : https://prove2.me/theorems/29752f53-47cf-4c7d-bc4f-2894363e11fb
-- title:
--   Nested partitions $P_k=\{\{1,\dots,k\},\{k+1\},\dots,\{n\}\}$
-- statement:
--   For $k\in[n]$, the nested partition
--
--   $$
--   P_k=\big\{\{1,\dots,k\},\{k+1\},\dots,\{n\}\big\}
--   $$
--
--   groups the $k$ sellers of highest revenue in one block and leaves every other seller alone. $P_1$ is the partition into singletons used for $m^{\downarrow}$ (§5.3), and the family $(P_k)_{k\in[n]}$ underlies the prior-dependent mechanism of §5.4.
--
--   **Formalization Note** With 0-based sellers the block is $\{j:\ j<k\}$; two sellers share a part iff they are equal or both lie in the block.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §5.4, p.28

import Mathlib

namespace SponsoredAssort

/-- The **nested partition** `P_k = {{1, …, k}, {k+1}, …, {n}}` of `[n]` (Balseiro, Désir,
SSRN 3821382 (Feb. 21, 2022), §5.4, p.28): one block of the `k` sellers with the highest revenues
and singletons for the others. `P₁` is the partition into singletons used for `m↓` (§5.3, p.28).

**Formalization Note.** Sellers are `Fin n` (0-based), so the block `{1, …, k}` is
`{j : (j : ℕ) < k}`. Two sellers are in the same part iff they are equal or both lie in that
block; the partition is built with `Finpartition.ofSetoid`. The paper takes `k ∈ [n]`. -/
noncomputable def nested (n k : ℕ) : Finpartition (Finset.univ : Finset (Fin n)) := by
  classical
  exact Finpartition.ofSetoid
    { r := fun a b => a = b ∨ ((a : ℕ) < k ∧ (b : ℕ) < k)
      iseqv :=
        { refl := fun _ => Or.inl rfl
          symm := fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩)
          trans := fun h₁ h₂ => by
            rcases h₁ with rfl | ⟨h₁, _⟩
            · exact h₂
            · rcases h₂ with rfl | ⟨_, h₂⟩
              · exact Or.inr ⟨h₁, by assumption⟩
              · exact Or.inr ⟨h₁, h₂⟩ } }

end SponsoredAssort


