-- Prove2me | Definitions.Def_Mathlib_Topology_Bases
-- name    : Mathlib_Topology_Bases
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/1f80d393-bf72-5b0b-ae84-b2b25fd54d92
-- title:
--   Second countability from a countable cover by open embeddings
-- statement:
--   This module supplies a single lemma, [`TopologicalSpace.secondCountableTopology_of_countable_cover'`](../def/Mathlib_Topology_Bases.html#L5). The data are a topological space $\alpha$, an index type $\iota$ (possibly a `Sort`) assumed countable, and for each $i : \iota$ a topological space $U_i$ which is second countable. Given maps $f_i : U_i \to \alpha$ such that each $f_i$ is an open embedding (`Topology.IsOpenEmbedding`, i.e. an embedding whose image is open), and given that the images jointly exhaust $\alpha$ in the pointwise form: for every $a : \alpha$ there are $i$ and $u : U_i$ with $f_i(u) = a$, the conclusion is that $\alpha$ is second countable.
--
--   The proof passes to the sets $V_i = \operatorname{range} f_i$. Each $V_i$ is open because an open embedding has open range, each $V_i$ is second countable because it is homeomorphic to $U_i$, and the hypothesis on points says exactly that $\bigcup_i V_i = \alpha$; the Mathlib lemma `secondCountableTopology_of_countable_cover` for a countable cover by open second-countable subsets then applies. So this is the variant of that lemma in which the cover is presented by open embeddings from abstract second-countable spaces rather than by open subsets of $\alpha$, and in which the covering condition is stated in terms of existence of a preimage point rather than as an equality of unions.
--
--   **Relation to Mathlib.** A variant of Mathlib's `secondCountableTopology_of_countable_cover`, from which it is deduced; the cover is given by open embeddings instead of open subsets.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Bases.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Bases.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

lemma TopologicalSpace.secondCountableTopology_of_countable_cover' {α : Type*}
    [TopologicalSpace α] {ι : Sort*} [Countable ι] {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
    [∀ (i : ι), SecondCountableTopology (U i)]
    (f : ∀ i, U i → α) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hc : ∀ a, ∃ (i : ι) (u : U i), f i u = a) : SecondCountableTopology α :=
  let V i := Set.range (f i)
  have (i : ι) : SecondCountableTopology (V i) :=
    (hf i).toHomeomorph.symm.secondCountableTopology
  have Vo (i : ι) : IsOpen (V i) := (hf i).isOpen_range
  have hV : ⋃ i, V i = Set.univ := Set.eq_univ_of_forall fun a =>
    (hc a).elim fun i hi => Set.mem_iUnion_of_mem i (Set.mem_range.2 hi)
  secondCountableTopology_of_countable_cover Vo hV


