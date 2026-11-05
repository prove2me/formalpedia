-- Prove2me | Definitions.Def_BundleGerbeStable_Admissible
-- name    : BundleGerbeStable_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:09.825765+00:00
-- url     : https://prove2.me/theorems/0171f8a7-cbe8-4e8f-84a1-9df2ccb8443f
-- title:
--   Open covers, nerves and admissible classes of locally split maps
-- statement:
--   An **open cover** of $M$ is a set of open sets covering $M$. Its **nerve** $Y_{\mathcal U}$ is the disjoint union of its members, that is, the pairs $(\alpha,x)$ with $x\in U_\alpha$, with the discrete diffeology on the index set; the projection to $M$ is locally split.
--
--   An **admissible class** $\mathcal A$ is a class of locally split maps to $M$ that is closed under fibre products over $M$ and in which every open cover has a refinement whose nerve lies in $\mathcal A$. `AdmissibleClass.all` is the class of all locally split maps.
--
--   The paper leaves the category of $Y$'s to context. A bijection for all diffeological $Y$ would not by itself give the bijection for manifold $Y$, because the trivial gerbes in the definition of stable isomorphism would range over more spaces; so the results are parametrized by $\mathcal A$. Surjective submersions from finite-dimensional, Banach or Fréchet manifolds form an admissible class.
--
--   **Formalization Note.** Covers are sets of open sets, so that all covers form a set in the universe of $M$. The closure properties are what the paper's constructions use: $P\otimes Q$ lives on $Y\times_\pi Z$ and the realization of a class lives on a nerve.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.2 (nerve of an open cover; category of spaces)

import Mathlib
import Definitions.Def_BundleGerbeStable_LocallySplit

open Diffeology TopologicalSpace

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M]

/-- An **open cover** of `M`, as a set of open sets (so that the type of all covers lies in `Type u`). -/
abbrev Cover (M : Type u) [TopologicalSpace M] : Type u :=
  {𝒰 : Set (Opens M) // ∀ x : M, ∃ U ∈ 𝒰, x ∈ U}

/-- `𝒱` refines `𝒰`: every member of `𝒱` lies in a member of `𝒰`. -/
def Refines (𝒱 𝒰 : Cover M) : Prop := ∀ V ∈ 𝒱.1, ∃ U ∈ 𝒰.1, V ≤ U

variable [DiffeologicalSpace M]

/-- The **nerve** `Y_𝒰` of an open cover (Murray, Stevenson, *Bundle gerbes: stable isomorphism and
local theory*, arXiv:math/9908135v1, §2, p.2): "the disjoint union of all the elements in the open
cover", the pairs `(α, x)` with `x ∈ U_α`. The index set carries the discrete diffeology. -/
def nerve (𝒰 : Cover M) : LocallySplit M :=
  letI : DiffeologicalSpace 𝒰.1 := discreteDiffeology _
  { Y := {q : 𝒰.1 × M // q.2 ∈ q.1.1}
    π := fun q ↦ q.1.2
    π_smooth := dSmooth_snd.comp dSmooth_subtype_val
    split := fun x ↦ by
      obtain ⟨U, hU, hxU⟩ := 𝒰.2 x
      refine ⟨U, hxU, fun u ↦ ⟨(⟨U, hU⟩, u.1), u.2⟩, ?_, fun _ ↦ rfl⟩
      exact DSmooth.subtype_mk' (DSmooth.prodMk' dSmooth_const dSmooth_subtype_val) _ }

/-- An **admissible class** of locally split maps: a class closed under fibre products over `M`, and
such that every open cover has a refinement whose nerve is in the class.

**Formalization Note.** The paper (p.2) leaves the category of `Y` to context. A bijection for all
diffeological `Y` would not by itself give the bijection for manifold `Y`, since the trivial gerbes
of Definition 3.1 would range over a larger class. So the statements are parametrized by the class.
`AdmissibleClass.all` is the diffeological statement; surjective submersions from
finite-dimensional, Banach or Fréchet manifolds give the paper's smooth statements. The closure
properties are exactly what the paper's constructions need: `P ⊗ Q` lives on `Y ×_π Z` and the
realization of a class lives on a nerve. The nerve clause rules out an empty class. -/
structure AdmissibleClass (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] where
  /-- Membership in the class. -/
  mem : LocallySplit.{u} M → Prop
  fibreProd_mem : ∀ {S T : LocallySplit M}, mem S → mem T → mem (fibreProd S T)
  nerve_mem : ∀ 𝒰 : Cover M, ∃ 𝒱 : Cover M, Refines 𝒱 𝒰 ∧ mem (nerve 𝒱)

/-- The class of all locally split maps is admissible. -/
def AdmissibleClass.all (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] :
    AdmissibleClass M where
  mem := fun _ ↦ True
  fibreProd_mem := fun _ _ ↦ trivial
  nerve_mem := fun 𝒰 ↦ ⟨𝒰, fun U hU ↦ ⟨U, hU, le_rfl⟩, trivial⟩

end BundleGerbeStable


