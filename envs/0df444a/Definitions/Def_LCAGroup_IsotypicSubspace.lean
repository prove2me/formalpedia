-- Prove2me | Definitions.Def_LCAGroup_IsotypicSubspace
-- name    : LCAGroup_IsotypicSubspace
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T18:48:39.08777+00:00
-- url     : https://prove2.me/theorems/8c439005-44a1-4b35-b0d2-f712dc44334f
-- title:
--   Isotypic subspace $V(\omega)=\{v:\pi(k)v=\omega(k)v\ \forall k\}$ of a family of continuous linear operators indexed by a set $K$ (in applications a group)
-- statement:
--   This is the **isotypic subspace** (space of homogeneous vectors) of a representation attached to a character.
--
--   Let $K$ be a set (in applications a compact abelian group), let $V$ be a complex vector space carrying a topology (in applications a topological vector space), and let $\pi\colon K\to\mathcal L(V)$ be a family of continuous linear operators on $V$ (in applications a representation, $\pi(k_1k_2)=\pi(k_1)\pi(k_2)$). For a function $\omega\colon K\to\mathbb C$ (in applications a continuous unitary character $\omega\in\widehat K$), the **$\omega$-isotypic subspace** of $V$ is
--   $$V(\omega)=\{v\in V:\ \pi(k)v=\omega(k)\,v\ \text{ for all }k\in K\}=\bigcap_{k\in K}\ker\bigl(\pi(k)-\omega(k)\bigr).$$
--   It is a linear subspace of $V$, the joint eigenspace of the operators $\pi(k)$ for the eigenvalues $\omega(k)$; when $V$ is a Hausdorff topological vector space it is closed.
--
--   In the source, $R(G)(\omega)$ is the $\omega$-isotype of the left-regular representation $R(G)=L^2(G,\nu)$ restricted to the compact subgroup $G^1$ (§4.3.1 and Terminology 4.3.2.1), and $\mathrm H^0(\omega,E)$ is the space of $\omega$-homogeneous elements of a locally convex space $E$ with a continuous action of a compact abelian group (Corollary 4.3.3.3(2)). These spaces are the building blocks of the isotypic decompositions used throughout Chapter 4.
--
--   **Formalization Note.** `LCAGroup.isotypicSubspace π ω : Submodule ℂ V` for `π : K → V →L[ℂ] V` and `ω : K → ℂ`; a Pontryagin-dual character `ω : PontryaginDual K` is passed as `fun k => (ω k : ℂ)`. The definition equals `⨅ k, Module.End.eigenspace (π k) (ω k)`. Mathlib's `isotypicComponent` (sum of submodules isomorphic to a given simple module) is a different, purely algebraic notion. The unfolding lemma `mem_isotypicSubspace` is proved by `Iff.rfl`. The definition uses no group structure on $K$ and no compatibility between the topology and the linear structure of $V$; the topology only serves to form continuous linear maps.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 174 (definition of $R(G)(\omega)$), p. 180, Terminology 4.3.2.1; p. 183, Corollary 4.3.3.3(2) ($\mathrm H^0(\omega,E)$)

import Mathlib

/-!
# Isotypic subspaces of a representation by continuous linear operators

For a family `π : K → V →L[ℂ] V` of continuous linear endomorphisms of a complex
topological vector space `V` (typically a representation of a group `K`) and a function
`ω : K → ℂ` (typically a continuous unitary character of `K`), the `ω`-isotypic subspace
is the subspace of `ω`-homogeneous vectors
`{v ∈ V | π k v = ω k • v for all k ∈ K}`.
-/

namespace LCAGroup

/-- The `ω`-isotypic subspace (subspace of `ω`-homogeneous vectors) of a family
`π : K → V →L[ℂ] V` of continuous linear endomorphisms of a complex topological vector
space `V`: the vectors `v` with `π k v = ω k • v` for every `k : K`. -/
def isotypicSubspace {K V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : K → V →L[ℂ] V) (ω : K → ℂ) : Submodule ℂ V where
  carrier := {v | ∀ k, π k v = ω k • v}
  add_mem' := by
    intro a b ha hb k
    change ∀ k, π k a = ω k • a at ha
    change ∀ k, π k b = ω k • b at hb
    rw [map_add, ha k, hb k, smul_add]
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c v hv k
    change ∀ k, π k v = ω k • v at hv
    rw [map_smul, hv k, smul_comm]

@[simp]
theorem mem_isotypicSubspace {K V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : K → V →L[ℂ] V) (ω : K → ℂ) (v : V) :
    v ∈ isotypicSubspace π ω ↔ ∀ k, π k v = ω k • v :=
  Iff.rfl

end LCAGroup


