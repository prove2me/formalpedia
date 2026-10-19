-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
-- name    : OAI_Combinatorics_SharpThreshold_BlockOrbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:02:38.776084+00:00
-- url     : https://prove2.me/theorems/0871c8a2-df75-4234-b309-3f39b871f5f2
-- title:
--   Extending a permutation of a block by the identity
-- statement:
--   Let $B$ be a finite subset of a type $\alpha$ and $\sigma$ a permutation of $B$. Its extension is the permutation $\hat\sigma$ of $\alpha$ with
--   $$
--   \hat\sigma(x)=\begin{cases}\sigma(x),&x\in B,\\x,&x\notin B.\end{cases}
--   $$
--
--   The extension preserves membership in $B$, maps $B$ onto itself, and $\widehat{\sigma}^{-1}=\widehat{\sigma^{-1}}$. Such permutations generate the symmetries used to average over vertex blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbit.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- A permutation of a block, extended by the identity away from the block. -/
def extendBlockPerm {α : Type u} [DecidableEq α] (B : Finset α)
    (σ : Equiv.Perm B) : Equiv.Perm α :=
  σ.extendDomain (Equiv.refl B)

@[simp]
theorem extendBlockPerm_apply_mem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : B) :
    extendBlockPerm B σ x = (σ x : α) := by
  exact Equiv.Perm.extendDomain_apply_image σ (Equiv.refl B) x

@[simp]
theorem extendBlockPerm_apply_notMem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) (hx : x ∉ B) :
    extendBlockPerm B σ x = x := by
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl B) hx

@[simp]
theorem extendBlockPerm_mem_iff {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) :
    extendBlockPerm B σ x ∈ B ↔ x ∈ B := by
  by_cases hx : x ∈ B
  · have h := extendBlockPerm_apply_mem B σ ⟨x, hx⟩
    rw [h]
    exact iff_of_true (σ ⟨x, hx⟩).2 hx
  · simp [extendBlockPerm_apply_notMem B σ x hx, hx]

@[simp]
theorem extendBlockPerm_map_block {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    B.map (extendBlockPerm B σ).toEmbedding = B := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (extendBlockPerm_mem_iff B σ y).mpr hy
  · simp

@[simp]
theorem extendBlockPerm_symm {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    (extendBlockPerm B σ).symm = extendBlockPerm B σ.symm := by
  exact Equiv.Perm.extendDomain_symm σ (Equiv.refl B)

end Problem313

end

end OAI


