-- Prove2me | Definitions.Def_LeblSCV_Levi_unitPolydiscProd
-- name    : LeblSCV_Levi_unitPolydiscProd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:46:18.064472+00:00
-- url     : https://prove2.me/theorems/c8c66553-5689-4bac-a1cf-d8b48068d3e9
-- title:
--   Unit polydisc $\mathbb{D}^{m+k}$ in coordinates $(z,w) \in \mathbb{C}^m \times \mathbb{C}^k$
-- statement:
--   With coordinates $(z, w) = (z_1, \dots, z_m, w_1, \dots, w_k) \in \mathbb{C}^m \times \mathbb{C}^k$, the **unit polydisc** is
--   $$\mathbb{D}^{m+k} = \{ (z,w) : |z_\ell| < 1 \text{ for } \ell = 1,\dots,m, \ |w_\ell| < 1 \text{ for } \ell = 1, \dots, k \}.$$
--
--   **Formalization Note.** The ambient space is the product `(Fin m → ℂ) × (Fin k → ℂ)`, matching the book's splitting of coordinates in Theorem 2.1.4.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 49, Theorem 2.1.4 (the polydisc 𝔻^{m+k})

import Mathlib

namespace LeblSCV.Levi

/-- The unit polydisc `𝔻^{m+k}` in the coordinates `(z, w) ∈ ℂ^m × ℂ^k` (Lebl, Theorem 2.1.4,
p. 49): every coordinate has modulus `< 1`. -/
def unitPolydiscProd (m k : ℕ) : Set ((Fin m → ℂ) × (Fin k → ℂ)) :=
  {x | (∀ l, ‖x.1 l‖ < 1) ∧ ∀ l, ‖x.2 l‖ < 1}

end LeblSCV.Levi


