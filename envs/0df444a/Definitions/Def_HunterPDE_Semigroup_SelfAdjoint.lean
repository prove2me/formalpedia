-- Prove2me | Definitions.Def_HunterPDE_Semigroup_SelfAdjoint
-- name    : HunterPDE_Semigroup_SelfAdjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:06:27.646987+00:00
-- url     : https://prove2.me/theorems/da30369f-88a3-4a4c-bf13-267d4017b983
-- title:
--   Unbounded self-adjoint operators on a complex Hilbert space (Definition 5.41)
-- statement:
--   Let $\mathcal{H}$ be a complex Hilbert space with inner product $(\cdot,\cdot)$. An operator $A : \mathcal{D}(A) \subset \mathcal{H} \to \mathcal{H}$ is **self-adjoint** if
--
--   1. the domain $\mathcal{D}(A)$ is dense in $\mathcal{H}$;
--   2. $x \in \mathcal{D}(A)$ if and only if there exists $z \in \mathcal{H}$ such that $(x, Ay) = (z, y)$ for every $y \in \mathcal{D}(A)$;
--   3. $(x, Ay) = (Ax, y)$ for all $x, y \in \mathcal{D}(A)$.
--
--   Condition (2) says $\mathcal{D}(A) = \mathcal{D}(A^*)$ and (3) that $A$ is symmetric; together, $A = A^*$. Self-adjoint operators are the generators (up to the factor $i$) of unitary groups, by Stone's theorem.
--
--   **Formalization Note.** The inner product is Mathlib's `⟪·, ·⟫_ℂ`, conjugate-linear in its first argument; conditions (2) and (3) are unchanged under the opposite convention.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 149, Definition 5.41

import Mathlib

open scoped InnerProductSpace

namespace HunterPDE.Semigroup

/-- Definition 5.41 of Hunter, *Notes on PDEs* (p. 149): an operator `A : D(A) ⊂ H → H` on a
complex Hilbert space `H` is **self-adjoint** if

1. the domain `D(A)` is dense in `H`;
2. `x ∈ D(A)` if and only if there exists `z ∈ H` with `(x, Ay) = (z, y)` for every `y ∈ D(A)`;
3. `(x, Ay) = (Ax, y)` for all `x, y ∈ D(A)`.

The inner product is Mathlib's `⟪·, ·⟫_ℂ` (conjugate-linear in the first slot); conditions (2)
and (3) are unchanged under the other convention, since swapping it conjugates both sides. -/
def IsSelfAdjointOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧
  (∀ x : H, x ∈ A.domain ↔ ∃ z : H, ∀ y : A.domain, ⟪x, A y⟫_ℂ = ⟪z, (y : H)⟫_ℂ) ∧
  (∀ x y : A.domain, ⟪(x : H), A y⟫_ℂ = ⟪A x, (y : H)⟫_ℂ)

end HunterPDE.Semigroup


