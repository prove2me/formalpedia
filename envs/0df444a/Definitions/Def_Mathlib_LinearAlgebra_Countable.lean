-- Prove2me | Definitions.Def_Mathlib_LinearAlgebra_Countable
-- name    : Mathlib_LinearAlgebra_Countable
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/ddbc2647-2874-57df-a2ec-3f806b6d79f9
-- title:
--   Countability of finite modules; number fields are countable
-- statement:
--   Two general-purpose facts about countability are recorded. The first, [`Countable.of_module_finite`](../def/Mathlib_LinearAlgebra_Countable.html#L5), asserts that for a semiring $R$ with countable underlying type and an additive commutative monoid $M$ carrying an $R$-module structure which is module-finite over $R$ (i.e. finitely generated as an $R$-module), the type $M$ is countable. The argument takes a finite spanning family $s : \mathrm{Fin}\,n \to M$ whose $R$-span is all of $M$, observes that the span of the range of such a family is countable, and transports this along the equality of the span with the whole module; concretely, every element of $M$ is an $R$-linear combination of finitely many fixed generators, and there are only countably many such combinations when $R$ is countable.
--
--   The second declaration is an instance deducing from this that the underlying type of any number field $K$ is countable: a number field is by definition a field of characteristic zero which is finite-dimensional over $\mathbb{Q}$, so $K$ is a module-finite $\mathbb{Q}$-module and $\mathbb{Q}$ is countable. Being an instance, it makes countability of number fields available to typeclass inference throughout, for instance when a construction requires a countable index set or a countable coefficient field.
--
--   **Relation to Mathlib.** Both declarations are stated in Mathlib's namespaces and rely only on Mathlib notions (`Module.Finite`, `Countable`, `NumberField`); they are auxiliary lemmas of the kind intended for eventual inclusion in Mathlib rather than project-specific definitions.
--
--   **Where it is used.** The countability instance for number fields is used as ambient infrastructure by many later modules, where countability of a field or of a set of arithmetic data is needed for measure-theoretic, topological or cardinality side conditions.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/LinearAlgebra/Countable.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_LinearAlgebra_Countable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

lemma Countable.of_module_finite (R M : Type*) [Semiring R] [Countable R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  Countable.of_module_finite ℚ K

end


