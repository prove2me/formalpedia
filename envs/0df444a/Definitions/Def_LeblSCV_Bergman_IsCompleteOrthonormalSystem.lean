-- Prove2me | Definitions.Def_LeblSCV_Bergman_IsCompleteOrthonormalSystem
-- name    : LeblSCV_Bergman_IsCompleteOrthonormalSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:49:15.987981+00:00
-- url     : https://prove2.me/theorems/bbb42ff2-9608-411e-b9c6-3dd25716d029
-- title:
--   Complete orthonormal system of $A^2(U)$
-- statement:
--   A family $\{\varphi_\ell\}_{\ell \in I}$ of elements of $A^2(U)$, indexed by an arbitrary set $I$, is a **complete orthonormal system** if it is orthonormal,
--   $$\langle \varphi_\ell, \varphi_m \rangle = \int_U \varphi_\ell \, \overline{\varphi_m}\, dV = \begin{cases} 1 & \ell = m, \\ 0 & \ell \neq m, \end{cases}$$
--   and complete: the linear span of $\{\varphi_\ell\}$ is dense in $A^2(U)$ for the $L^2(U)$ norm.
--
--   This is the hypothesis of Proposition 5.2.5. Since $A^2(U)$ is a Hilbert space (Lemma 5.2.1), the complete orthonormal systems are exactly its Hilbert bases.
--
--   **Formalization Note.** Orthonormality is Mathlib's `Orthonormal ℂ φ` in the inner product space `bergmanSpace U`; completeness is `(Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤`. The index type is arbitrary (finite, countable or larger), as in the book.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 163 (hypothesis of Proposition 5.2.5)

import Mathlib
import Definitions.Def_LeblSCV_Bergman_bergmanSpace

open MeasureTheory

namespace LeblSCV.Bergman

/-- A complete orthonormal system `{φ_ℓ}_{ℓ ∈ I}` of `A²(U)` (Lebl, p. 163): the family is
orthonormal for the `L²(U)` inner product, and its linear span is dense in `A²(U)`. -/
def IsCompleteOrthonormalSystem {n : ℕ} (U : Set (Fin n → ℂ)) {I : Type*}
    (φ : I → bergmanSpace U) : Prop :=
  Orthonormal ℂ φ ∧ (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤

end LeblSCV.Bergman


