-- Prove2me | Definitions.Def_LeblSCV_Levi_hartogsFigure
-- name    : LeblSCV_Levi_hartogsFigure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:51:37.464592+00:00
-- url     : https://prove2.me/theorems/ace0e1d1-ccbb-44b7-99a4-069e4b6b63dc
-- title:
--   The Hartogs figure $H$ of Theorem 2.1.4
-- statement:
--   For two numbers $a, b$ (in the theorem, $0 < a, b < 1$), the **Hartogs figure** in $\mathbb{C}^m \times \mathbb{C}^k$ is
--   $$H = \{ (z,w) \in \mathbb{D}^{m+k} : |z_\ell| > a \text{ for } \ell = 1, \dots, m \} \cup \{ (z,w) \in \mathbb{D}^{m+k} : |w_\ell| < b \text{ for } \ell = 1, \dots, k \}.$$
--
--   **Formalization Note.** `hartogsFigure m k a b` is defined for all real `a`, `b`; the restriction $0 < a, b < 1$ is a hypothesis of the theorem.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 49, Theorem 2.1.4

import Mathlib
import Definitions.Def_LeblSCV_Levi_unitPolydiscProd

namespace LeblSCV.Levi

/-- The Hartogs figure of Theorem 2.1.4 (Lebl, p. 49): for `a, b`,
`H = {(z,w) ∈ 𝔻^{m+k} : |z_ℓ| > a, ℓ = 1..m} ∪ {(z,w) ∈ 𝔻^{m+k} : |w_ℓ| < b, ℓ = 1..k}`. -/
def hartogsFigure (m k : ℕ) (a b : ℝ) : Set ((Fin m → ℂ) × (Fin k → ℂ)) :=
  {x | x ∈ unitPolydiscProd m k ∧ ∀ l, a < ‖x.1 l‖} ∪
    {x | x ∈ unitPolydiscProd m k ∧ ∀ l, ‖x.2 l‖ < b}

end LeblSCV.Levi


