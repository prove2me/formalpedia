-- Prove2me | Definitions.Def_InvariantSubspaceProblem_Defs
-- name    : InvariantSubspaceProblem_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T17:19:23.540301+00:00
-- url     : https://prove2.me/theorems/3057d82a-c629-4532-be97-f65e95777d90
-- title:
--   Closed invariant and hyperinvariant subspaces of a bounded operator
-- statement:
--   Let $\mathbb{K}$ be a non-trivially normed field (in this mission always $\mathbb{R}$ or $\mathbb{C}$), let $E$ be a normed space over $\mathbb{K}$, and let $T\colon E\to E$ be a bounded (continuous) linear operator.
--
--   1. A linear subspace $S\subseteq E$ is **invariant** under $T$ if $T(S)\subseteq S$, i.e. $Tx\in S$ for every $x\in S$.
--   2. $S$ is a **non-trivial closed invariant subspace** of $T$ if $S$ is closed in the norm topology, $S\neq\{0\}$, $S\neq E$, and $S$ is invariant under $T$.
--   3. $T$ **has a non-trivial closed invariant subspace** if at least one such $S$ exists.
--   4. $T$ **has a non-trivial closed hyperinvariant subspace** if there is a closed subspace $S$ with $\{0\}\neq S\neq E$ that is invariant under every bounded operator $A$ commuting with $T$ ($AT=TA$).
--
--   These four notions are the vocabulary in which the invariant subspace problem and all milestone results of this mission are stated.
--
--   **Formalization Note** Subspaces are Mathlib `Submodule`s of $E$; closedness is required explicitly. Without the closedness requirement the problem becomes trivial in infinite dimensions (the algebraic span of an orbit $\{T^n x\}$ is always a proper invariant subspace), so closedness is essential.
-- source:
--   Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem (problem statement: 'non-trivial closed invariant subspace'); Radjavi & Rosenthal, Invariant Subspaces, Springer 1973 (definitions of invariant and hyperinvariant subspaces).

import Mathlib

namespace InvariantSubspaceProblem

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `S` is invariant under the bounded operator `T`: `T x ∈ S` for every `x ∈ S`. -/
def IsInvariantSubspace (T : E →L[𝕜] E) (S : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ S, T x ∈ S

/-- `S` is a non-trivial closed invariant subspace of `T`: `S` is topologically closed,
`S ≠ {0}`, `S ≠ E`, and `T` maps `S` into itself. -/
def IsNontrivialClosedInvariantSubspace (T : E →L[𝕜] E) (S : Submodule 𝕜 E) : Prop :=
  IsClosed (S : Set E) ∧ S ≠ ⊥ ∧ S ≠ ⊤ ∧ IsInvariantSubspace T S

/-- The bounded operator `T` has at least one non-trivial closed invariant subspace. -/
def HasNontrivialClosedInvariantSubspace (T : E →L[𝕜] E) : Prop :=
  ∃ S : Submodule 𝕜 E, IsNontrivialClosedInvariantSubspace T S

/-- The bounded operator `T` has a non-trivial closed *hyperinvariant* subspace: a closed
subspace `S` with `S ≠ {0}`, `S ≠ E`, which is invariant under every bounded operator `A`
commuting with `T` (`A * T = T * A`, i.e. `A ∘ T = T ∘ A`). -/
def HasNontrivialClosedHyperinvariantSubspace (T : E →L[𝕜] E) : Prop :=
  ∃ S : Submodule 𝕜 E, IsClosed (S : Set E) ∧ S ≠ ⊥ ∧ S ≠ ⊤ ∧
    ∀ A : E →L[𝕜] E, A * T = T * A → IsInvariantSubspace A S

end InvariantSubspaceProblem


