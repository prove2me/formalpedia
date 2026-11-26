-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
-- name    : ProEtale_Mathlib_Topology_Inseparable
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:04.796714+00:00
-- url     : https://prove2.me/theorems/fd10e911-ecdd-4d05-a7f4-84ba9d235955
-- title:
--   Generalization hull of a set; embeddings and injective generalizing maps reflect specialization
-- statement:
--   Let $X$ be a topological space and write $x \rightsquigarrow y$ if $x$ specializes to $y$, i.e. $y \in \overline{\{x\}}$.
--
--   **Definition.** The **generalization hull** of $s \subseteq X$ is the intersection of all subsets $t \supseteq s$ that are stable under generalization.
--
--   **Results.**
--
--   1. The generalization hull of $s$ is the set of points specializing to a point of $s$:
--   $$\mathrm{genHull}(s) = \{x \in X : \exists y \in s,\ x \rightsquigarrow y\},$$
--   together with the corresponding membership criterion.
--   2. If $f$ is a topological embedding, then $f(x) \rightsquigarrow f(y) \iff x \rightsquigarrow y$.
--   3. If $g$ is an injective generalizing map, then $g(x) \rightsquigarrow g(y)$ implies $x \rightsquigarrow y$.
--
--   These are used for spectral and w-local spaces.
--
--   **Formalization Note** Declarations: `generalizationHull`, `generalizationHull_eq`, `mem_generalizationHull_iff`, `Topology.IsEmbedding.specializes_iff` and `GeneralizingMap.specializes_of_map_specializes`. Generalizing maps are Mathlib's `GeneralizingMap`: every generalization of $g(x)$ comes from a generalization of $x$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Inseparable.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Inseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-- The generalization hull of `s` is the smallest set containing `s` that is stable
under generalization.
It is equal to the set of points specializing to a point in `s`, see `generalizationHull_eq`. -/
def generalizationHull {X : Type*} [TopologicalSpace X] (s : Set X) : Set X :=
  ⋂₀ {t : Set X | StableUnderGeneralization t ∧ s ⊆ t }

variable {X : Type*} [TopologicalSpace X]


lemma generalizationHull_eq (s : Set X) :
    generalizationHull s = { x | ∃ y ∈ s, x ⤳ y } := by
  rw [generalizationHull]
  refine subset_antisymm ?_ ?_
  · apply Set.sInter_subset_of_mem
    refine ⟨?_, ?_⟩
    · intro x y hyx ⟨z, hzs, hxz⟩
      use z, hzs, hyx.trans hxz
    · intro x hx
      use x
  · rw [Set.subset_sInter_iff]
    intro t ⟨ht, hs⟩ x ⟨y, hy, h⟩
    exact ht h (hs hy)

lemma mem_generalizationHull_iff {s : Set X} {x : X} :
    x ∈ generalizationHull s ↔ ∃ y ∈ s, x ⤳ y := by
  rw [generalizationHull_eq]
  rfl

lemma Topology.IsEmbedding.specializes_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {x y : X} :
    f x ⤳ f y ↔ x ⤳ y := by
  rw [specializes_iff_mem_closure, ← Set.mem_preimage, ← Set.image_singleton,
    ← hf.closure_eq_preimage_closure_image, specializes_iff_mem_closure]

/-- An injective generalizing map reflects specialization: if `g x ⤳ g y` then `x ⤳ y`. -/
lemma GeneralizingMap.specializes_of_map_specializes {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hg : GeneralizingMap g) (hinj : Function.Injective g)
    {x y : X} (h : g x ⤳ g y) : x ⤳ y := by
  obtain ⟨x', hx', hgx'⟩ := hg h
  exact hinj hgx' ▸ hx'


