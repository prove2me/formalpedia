-- Prove2me | Definitions.Def_DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted
-- name    : DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a0658c75-34fb-5a84-91db-d77493dcecb1
-- title:
--   Restricted products as direct limits of coarser restricted products
-- statement:
--   For a family of types $R_i$ ($i \in \iota$) with distinguished subobjects $C_i$ and a filter $\mathcal{F}$ on $\iota$, write $\Pi^{r}_i [R_i, C_i]_{[\mathcal{F}]}$ for the restricted product: the functions $x$ with $x_i \in C_i$ for $\mathcal{F}$-eventually all $i$. Coarsening the filter enlarges the restricted product, and this module records the resulting direct-system and direct-limit structure.
--
--   First, for a filter $\mathcal{F}$ the collection $\mathcal{F}.\mathrm{sets}$ of its members, ordered by reverse inclusion, is nonempty (it contains the whole index set) and directed ([`RestrictedProduct.directed`](../def/DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted.html#L41), by intersection of two members); [`RestrictedProduct.instDirectedSystem`](../def/DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted.html#L19) makes $S \mapsto \Pi^{r}_i [R_i, C_i]_{[\mathcal{P}S]}$, with transition maps the inclusions coming from monotonicity of the principal-filter operation, a directed system, and the same system is registered with the $A$-linear inclusion maps `inclusionLinearMap` when the $R_i$ are $A$-modules and the $C_i$ are $A$-submodules. More generally, any antitone family of filters $\mathcal{G} : I \to \mathrm{Filter}\,\iota$ gives such a directed system of restricted products with linear inclusion transitions.
--
--   The main instance `instIsDirectLimit` asserts, for $I$ a nonempty directed preorder, $\mathcal{G}$ antitone and $\mathcal{F} = \inf_i \mathcal{G}_i$, that $\Pi^{r}_i [R_i, C_i]_{[\mathcal{F}]}$ together with the inclusions from each level is a direct limit of this system in the sense of the predicate [`IsDirectLimit`](../def/Mathlib_Algebra_IsDirectLimit.html#L8): the level maps are jointly surjective, two elements with the same image already agree after transport to a common level, and the maps are compatible with the transitions. `instIsDirectLimit'` specialises this to the principal filters of the members of $\mathcal{F}$, using that $\mathcal{F}$ is the infimum of the principal filters of its members.
--
--   **Relation to Mathlib.** Mathlib supplies `RestrictedProduct`, `DirectedSystem` and the concrete `Module.DirectLimit` construction; the predicate [`IsDirectLimit`](../def/Mathlib_Algebra_IsDirectLimit.html#L8) on a family of maps into a fixed target, and the linear inclusion maps between restricted products along comparable filters, come from the project's own definition modules. The point of the instances here is that the restricted product along $\inf_i \mathcal{G}_i$ is itself recognised as a direct limit, with no transport along an isomorphism to a quotient model.
--
--   **Where it is used.** The intended application is the finite adèle ring of a Dedekind domain, a restricted product over the height-one primes with respect to the cofinite filter, which is thereby exhibited as the direct limit of the finite-level subrings $\prod_{v \in S} K_v \times \prod_{v \notin S} \mathcal{O}_v$ over finite sets $S$ of primes.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/DedekindDomain/FiniteAdeleRing/IsDirectLimitRestricted.lean` — © 2025 Madison Crim; authors: Madison Crim). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace RestrictedProduct

open Set Filter

section directedSystem

variable {ι : Type*} {𝓕 : Filter ι}

instance : Nonempty 𝓕.setsᵒᵈ := ⟨⊤, by simp⟩

variable {R : ι → Type*} {A : ι → Type*} [Π i, SetLike (A i) (R i)] {C : Π i, A i}

instance instDirectedSystem :
    DirectedSystem (fun (S : 𝓕.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
      (fun _ _ h ↦ RestrictedProduct.inclusion _ _ <| monotone_principal h) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

end directedSystem

section inclusion

open scoped RestrictedProduct TensorProduct IsDirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} {M : Type*}
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : ℱ.setsᵒᵈ)

open Set Filter RestrictedProduct

instance : DirectedSystem (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    fun _ _ h ↦ (inclusionLinearMap A R C <| monotone_principal h) :=
  RestrictedProduct.instDirectedSystem

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) where
    directed Si Sj := by
      obtain ⟨Si, hi⟩ := Si
      obtain ⟨Sj, hj⟩ := Sj
      use ⟨Si ∩ Sj, ℱ.inter_sets hi hj⟩, inter_subset_left, inter_subset_right

end inclusion

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]
variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}

instance {I : Type*} [Preorder I] (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) :
    DirectedSystem (fun x ↦ Πʳ (i : ι), [R i, ↑(C i)]_[𝓖 x])
      (inclusionLinearMap A R C <| @h𝓖 · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

instance instIsDirectLimit {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) (hℱ : ℱ = iInf 𝓖) :
    IsDirectLimit (inclusionLinearMap A R C <| @h𝓖 · · ·)
    (inclusionLinearMap A R C <| hℱ.trans_le <| iInf_le 𝓖 ·) where
  inj Sᵢ Sⱼ mi mj hmij := by
    obtain ⟨Sₖ, hik, hjk⟩ := @directed_of _ (· ≤ ·) _ Sᵢ Sⱼ
    refine ⟨Sₖ, hik, hjk, ?_⟩
    apply Subtype.ext
    injection hmij
  surj r := by
    dsimp [inclusionLinearMap]
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) } ∈ (iInf 𝓖) := hℱ ▸ r.property
    obtain ⟨j, hj⟩ := (Filter.mem_iInf_of_directed h𝓖.directed_ge _).mp this
    use j
    apply RestrictedProduct.exists_inclusion_eq_of_eventually _ _ _ hj
    rw [hℱ]
    exact iInf_le_iff.mpr fun b a ↦ a j
  compatibility i j hij x := by
    dsimp [inclusionLinearMap, RestrictedProduct.inclusion, RestrictedProduct.inclusion]
    exact Subtype.ext rfl

instance instIsDirectLimit' : IsDirectLimit (M := fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    ((fun _ _ h ↦ inclusionLinearMap A R C <| monotone_principal h))
    (fun S ↦ inclusionLinearMap A R C <| Filter.le_principal_iff.2 S.2) := by
  apply instIsDirectLimit
  exact eq_iInf_of_mem_iff_exists_mem (fun {s} ↦ ⟨fun h ↦ ⟨⟨s, h⟩, subset_refl s⟩,
    fun ⟨i, hi⟩ ↦ Filter.mem_of_superset i.2 hi⟩)

end RestrictedProduct


