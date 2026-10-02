-- Prove2me | Definitions.Def_TeschlQM_Shared_IsSymmetric
-- name    : TeschlQM_Shared_IsSymmetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:14.271287+00:00
-- url     : https://prove2.me/theorems/c0b8c7bd-fbeb-41f2-8da0-88657a552679
-- title:
--   Symmetric operator, Eq. (2.17)
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and let $A : \mathfrak{D}(A) \to \mathfrak{H}$ be a linear operator defined on a linear subspace $\mathfrak{D}(A) \subseteq \mathfrak{H}$. The operator $A$ is **symmetric** (or hermitian) if it is densely defined and
--   $$\langle \varphi, A\psi \rangle = \langle A\varphi, \psi \rangle, \qquad \psi, \varphi \in \mathfrak{D}(A).$$
--
--   Symmetric operators are the candidates for quantum-mechanical observables; every result of this mission is about them.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `01-self-adjoint`: p. 60, Corollary 2.2; p. 63, Lemma 2.3; p. 66, Lemma 2.7; p. 77, Theorem 2.18; p. 81, Theorem 2.25; p. 83, Lemma 2.27; p. 83, Theorem 2.28; p. 82, Theorem 2.26, Eqs. (2.103)–(2.104); p. 82, Theorem 2.26
--   - chunk `06-kato-rellich`: p. 135, Theorem 6.4, Eq. (6.3)
--   - chunk `08-weyl`: p. 147, Theorem 6.20; p. 148, Lemma 6.23
--   - chunk `10-algebraic`: p. 174, Theorem 8.2
--
--   **Formalization Note.** An operator is a `LinearPMap` `H →ₗ.[ℂ] H` with domain `A.domain`. Density of the domain is part of the definition, exactly as in the book (2.17). Mathlib's inner product is conjugate-linear in the first argument, matching the book's convention.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 58, Section 2.2, Eq. (2.17)

import Mathlib

namespace TeschlQM.Shared

open scoped InnerProductSpace

/-- Teschl (2.17), p. 58: a linear operator `A : 𝔇(A) → ℌ` (a `LinearPMap`) is *symmetric* if it is
densely defined and `⟨φ, Aψ⟩ = ⟨Aφ, ψ⟩` for all `ψ, φ ∈ 𝔇(A)`. Density is part of the book's
definition. -/
def IsSymmetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧ ∀ φ ψ : A.domain, ⟪(φ : H), A ψ⟫_ℂ = ⟪A φ, (ψ : H)⟫_ℂ

end TeschlQM.Shared


