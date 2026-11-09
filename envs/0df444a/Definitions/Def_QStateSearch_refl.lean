-- Prove2me | Definitions.Def_QStateSearch_refl
-- name    : QStateSearch_refl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:32.383743+00:00
-- url     : https://prove2.me/theorems/93d1c666-2db3-458e-9f64-b09fbba0bbfb
-- title:
--   Reflection oracle $R_\psi=I-2|\psi\rangle\langle\psi|$
-- statement:
--   For a vector $\psi\in\mathbb C^D$ the **marked-state reflection** is the $D\times D$ matrix
--   $$
--   R_\psi=I-2\,|\psi\rangle\langle\psi| .
--   $$
--   When $\psi$ is a unit vector, $R_\psi$ is the unitary that fixes the orthogonal complement of $\psi$ and maps $\psi$ to $-\psi$. The promise problem of the paper asks to distinguish the marked oracle $R_\psi$ for a hidden state $\psi$ from the unmarked oracle $I$.
--
--   **Formalization Note** The matrix is defined for every vector; the Haar measure used with it lives on the unit sphere, where $R_\psi$ is unitary.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.1, p.8

import Mathlib
open Matrix

namespace QStateSearch

/-- The marked-state reflection `R_ψ = I − 2|ψ⟩⟨ψ|` on `ℂ^D`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.1, p.8: "For every unit vector |ψ⟩ ∈ C^D, define R_ψ = I − 2|ψ⟩⟨ψ|."

**Formalization Note.** `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)` (entry `(i, j)` is `ψ i * conj (ψ j)`).
The matrix is defined for every vector; it is unitary when `‖ψ‖ = 1`, and the Haar measure
used with it lives on the unit sphere. -/
noncomputable def refl {D : ℕ} (ψ : EuclideanSpace ℂ (Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  1 - (2 : ℂ) • vecMulVec (⇑ψ) (star ⇑ψ)

end QStateSearch


