-- Prove2me | Definitions.Def_TeschlQM_Spectral_IsNormalOperator
-- name    : TeschlQM_Spectral_IsNormalOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:27:05.906486+00:00
-- url     : https://prove2.me/theorems/589c7ca3-54b9-4152-9b5d-69ecb8dbfa68
-- title:
--   Normal (unbounded) operator
-- statement:
--   A densely defined linear operator $T$ in a complex Hilbert space $\mathfrak H$ is **normal** if
--   $$\mathfrak D(T) = \mathfrak D(T^*) \quad\text{and}\quad \|T\psi\| = \|T^*\psi\| \ \text{ for all } \psi \in \mathfrak D(T).$$
--   Here $T^*$ is the adjoint, defined for densely defined operators.
--
--   **Formalization Note.** $T$ is a `LinearPMap` and $T^*$ is `LinearPMap.adjoint`, which is Teschl's adjoint only when $\mathfrak D(T)$ is dense (otherwise Mathlib returns a junk value); density of $\mathfrak D(T)$ is therefore written into the definition, in line with the book, where $T^*$ is only defined for densely defined $T$. The norm condition is stated for pairs of vectors of $\mathfrak D(T)$ and $\mathfrak D(T^*)$ that are equal as elements of $\mathfrak H$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 91, Section 3.1

import Mathlib

namespace TeschlQM.Spectral

/-- Teschl, p. 91: an unbounded operator `T` is **normal** if `𝔇(T) = 𝔇(T*)` and
`‖Tψ‖ = ‖T*ψ‖` for all `ψ ∈ 𝔇(T)`. The adjoint `T*` is only defined for densely defined `T`
(Teschl, Sec. 2.1), so density of `𝔇(T)` is part of the notion; Mathlib's `LinearPMap.adjoint`
is a junk value otherwise. -/
def IsNormalOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) : Prop :=
  Dense (T.domain : Set H) ∧ T.adjoint.domain = T.domain ∧
  ∀ (ψ : T.domain) (ψ' : T.adjoint.domain), (ψ : H) = ψ' → ‖T ψ‖ = ‖T.adjoint ψ'‖

end TeschlQM.Spectral


