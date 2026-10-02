-- Prove2me | Definitions.Def_TeschlQM_Scattering_Reduces
-- name    : TeschlQM_Scattering_Reduces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:18:42.549054+00:00
-- url     : https://prove2.me/theorems/43a65880-a082-43f9-973a-99cb8c101d41
-- title:
--   A closed subspace reduces an operator (P₁A ⊆ AP₁)
-- statement:
--   Let $\mathfrak H_1 \subseteq \mathfrak H$ be a closed subspace with orthogonal projection $P_1$. $\mathfrak H_1$ **reduces** the operator $A$ if $P_1 A \subseteq A P_1$, that is,
--   $$P_1\mathfrak D(A) \subseteq \mathfrak D(A) \quad\text{and}\quad P_1 A\psi = A P_1\psi, \qquad \psi \in \mathfrak D(A).$$
--   Then $A$ splits as an orthogonal sum of its parts in $\mathfrak H_1$ and $\mathfrak H_1^\perp$.
--
--   **Formalization Note.** The set $S$ must be closed and be the carrier of a submodule $K$; $P_1$ is `K.topologicalClosure.starProjection`, which is the projection onto $K = S$ since $S$ is closed.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 80, Section 2.5

import Mathlib

namespace TeschlQM.Scattering

/-- Teschl, p. 80: a closed subspace `ℌ₁ ⊆ ℌ` with orthogonal projector `P₁` **reduces** the
operator `A` if `P₁ A ⊆ A P₁`, i.e. `P₁ 𝔇(A) ⊆ 𝔇(A)` and `P₁ A ψ = A P₁ ψ` for `ψ ∈ 𝔇(A)`.
Here `ℌ₁ = S` is required to be a closed linear subspace (the carrier of a submodule `K`, closed
in `ℌ`), and `P₁` is the orthogonal projection onto `K`, taken as the projection onto the
topological closure of `K` (which is `K` itself since `S` is closed). -/
def Reduces {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set H) (A : H →ₗ.[ℂ] H) : Prop :=
  IsClosed S ∧ ∃ K : Submodule ℂ H, (K : Set H) = S ∧
    ∀ ψ : A.domain, ∃ h : K.topologicalClosure.starProjection (ψ : H) ∈ A.domain,
      A ⟨K.topologicalClosure.starProjection (ψ : H), h⟩ =
        K.topologicalClosure.starProjection (A ψ)

end TeschlQM.Scattering


