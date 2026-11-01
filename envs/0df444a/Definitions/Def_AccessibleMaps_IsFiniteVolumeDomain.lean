-- Prove2me | Definitions.Def_AccessibleMaps_IsFiniteVolumeDomain
-- name    : AccessibleMaps_IsFiniteVolumeDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:28.301442+00:00
-- url     : https://prove2.me/theorems/1d3c1f7b-c22d-4226-86a1-b1bbe7050a49
-- title:
--   Admissible domain $\mathcal V$: a set of states with positive volume in $\mathcal M_A$
-- statement:
--   Let $\mathcal M_A$ be the set of density matrices on $\mathbb C^{a}$ (positive semidefinite, trace one). A set $\mathcal V\subseteq\mathcal M_A$ is an **admissible domain** of an assignment if
--
--   1. every $\rho\in\mathcal V$ is a density matrix,
--   2. $\mathcal V$ is nonempty, and
--   3. every traceless Hermitian $a\times a$ matrix is a real linear combination of differences $\rho-\rho'$ with $\rho,\rho'\in\mathcal V$.
--
--   Condition 3 says that the affine hull of $\mathcal V$ is the whole affine space of unit-trace Hermitian matrices, i.e. that the convex hull of $\mathcal V$ has positive volume in $\mathcal M_A$. The paper requires the domain of an accessible map to be "a finite volume (i.e., non-empty) subset" of $\mathcal M_A$, because "convex combinations of a tomographically complete set of states must span a finite-volume region of $\mathcal M_A$".
--
--   **Formalization Note** Every subset of $\mathcal M_A$ of positive volume satisfies the definition, and so does a finite tomographically complete set of states. The set of all qubit density matrices satisfies it (checked in the mission's sanity file).
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §III, p.2 ("The domain V of Φ should be a finite volume (i.e., non-empty) subset of the set of all states of A")

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open PeresTerno

namespace AccessibleMaps

variable {a : Type*} [Fintype a]

/-- The admissible domains `𝒱` of an assignment: a nonempty set of density matrices whose convex
combinations span a finite-volume region of the set `ℳ_A` of all states. Equivalently, the
differences of elements of `𝒱` span all traceless Hermitian matrices over `ℝ`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §III, p.2 (PDF p.2): "The domain 𝒱 of Φ
should be a finite volume (i.e., non-empty) subset of the set of all states of A, which we will
call ℳ_A. This is the first non-trivial requirement: physically relevant maps should be
identifiable by process tomography, and convex combinations of a tomographically complete set of
states must span a finite-volume region of ℳ_A."

**Formalization Note.** "Finite volume" is read as positive volume in `ℳ_A`, through the convex
hull, as the quoted sentence states it: the convex hull of `𝒱` has positive volume in the affine
space of unit-trace Hermitian matrices exactly when the affine hull of `𝒱` is that whole space,
which is the third clause (`vectorSpan ℝ V` is the real span of the differences of elements of
`𝒱`). Every set of positive volume satisfies it, and so does a finite tomographically complete set
of states. -/
def IsFiniteVolumeDomain (V : Set (Matrix a a ℂ)) : Prop :=
  (∀ ρ ∈ V, IsDensityMatrix ρ) ∧ V.Nonempty ∧
    ∀ T : Matrix a a ℂ, T.IsHermitian → T.trace = 0 → T ∈ vectorSpan ℝ V

end AccessibleMaps


