-- Prove2me | Definitions.Def_CompNonlocal_bloch
-- name    : CompNonlocal_bloch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:35.615276+00:00
-- url     : https://prove2.me/theorems/f6be459d-7830-4288-8cc3-7f9391bfd1a1
-- title:
--   The qubit operator $\nu(r)=\tfrac12(I+r\cdot\sigma)$
-- statement:
--   For $r\in\mathbb R^3$,
--   $$\nu(r):=\tfrac12\big(I+r\cdot\sigma\big),\qquad r\cdot\sigma=r_1\sigma_x+r_2\sigma_y+r_3\sigma_z .$$
--   It is a qubit density matrix exactly when $\|r\|_2\le1$, and a pure state when $\|r\|_2=1$; $r$ is its Bloch vector.
--
--   **Formalization Note** Defined for every $r\in\mathbb R^3$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18

import Mathlib
import Definitions.Def_CompNonlocal_pauli

set_option autoImplicit false

namespace CompNonlocal

/-- The qubit operator with Bloch vector `r`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18: "For a Bloch vector r ∈ R³ with
∥r∥₂ ≤ 1, we write ν(r) := ½(I + r · σ) ∈ S(C²)", with "r · σ := rxσx + ryσy + rzσz".

**Formalization Note** Defined for every `r ∈ ℝ³`; it is a density matrix exactly when `‖r‖ ≤ 1`. -/
noncomputable def bloch (r : EuclideanSpace ℝ (Fin 3)) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + ∑ j : Fin 3, ((r j : ℝ) : ℂ) • pauli j)

end CompNonlocal


