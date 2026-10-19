-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
-- name    : OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:17:17.267339+00:00
-- url     : https://prove2.me/theorems/725eff42-97a4-4122-9639-810246d3f1e5
-- title:
--   Permutations supported on a vertex block
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$.
--
--   1. An edge touches $B$ if one of its endpoints lies in $B$.
--   2. A permutation $\pi$ is supported on $B$ if it fixes every vertex outside $B$:
--   $$
--   \pi(v)=v\quad\text{for all }v\notin B .
--   $$
--   3. Such permutations satisfy $\pi(v)\in B\iff v\in B$, their inverses and products are again supported on $B$, and they preserve the set of edges touching $B$. They form the subgroup of permutations supported on $B$.
--
--   When the edges outside $B$ are frozen, a vertex-invariant property restricted to the touching edges is invariant under this subgroup.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockRestrictionSymmetry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockRestrictionSymmetry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex

namespace OAI

noncomputable section
namespace Problem313

/-- An edge is free in a block restriction when it touches the block. -/
def EdgeTouches {n : ℕ} (B : Finset (Fin n)) (e : GraphEdge n) : Prop :=
  ∃ v, v ∈ e.val ∧ v ∈ B

/-- The vertex permutation is supported on the block. -/
def SupportedOnBlock {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ v, v ∉ B → π v = v

lemma supportedOnBlock_mem_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (v : Fin n) :
    π v ∈ B ↔ v ∈ B := by
  constructor
  · intro h
    by_contra hn
    exact hn (by simpa [hπ v hn] using h)
  · intro h
    by_contra hn
    have he := hπ (π v) hn
    have he' : π v = v := π.injective he
    exact hn (he'.symm ▸ h)

lemma supportedOnBlock_symm {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) :
    SupportedOnBlock B π.symm := by
  intro v hv
  apply π.injective
  simpa using (hπ v hv).symm

lemma block_mem_permEdge_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) (v : Fin n) :
    v ∈ (permEdge π e).val ↔ π.symm v ∈ e.val := by
  simp [permEdge]

lemma edgeTouches_permEdge_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (e : GraphEdge n) :
    EdgeTouches B (permEdge π e) ↔ EdgeTouches B e := by
  constructor
  · rintro ⟨v, hv, hB⟩
    refine ⟨π.symm v, (block_mem_permEdge_iff π e v).mp hv, ?_⟩
    exact (supportedOnBlock_mem_iff (supportedOnBlock_symm hπ) v).mpr hB
  · rintro ⟨v, hv, hB⟩
    refine ⟨π v, ?_, (supportedOnBlock_mem_iff hπ v).mpr hB⟩
    simpa [block_mem_permEdge_iff] using hv

lemma supportedOnBlock_one {n : ℕ} (B : Finset (Fin n)) :
    SupportedOnBlock B (1 : Equiv.Perm (Fin n)) := by
  intro v _
  rfl

lemma supportedOnBlock_mul {n : ℕ} {B : Finset (Fin n)}
    {π σ : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (hσ : SupportedOnBlock B σ) : SupportedOnBlock B (π * σ) := by
  intro v hv
  change π (σ v) = v
  rw [hσ v hv, hπ v hv]

/-- The subgroup of permutations supported on a given vertex block. -/
def blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | SupportedOnBlock B π}
  one_mem' := supportedOnBlock_one B
  mul_mem' := supportedOnBlock_mul
  inv_mem' := supportedOnBlock_symm

@[simp] lemma mem_blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : π ∈ blockPermutationSubgroup B ↔ SupportedOnBlock B π :=
  Iff.rfl

end Problem313

end

end OAI


