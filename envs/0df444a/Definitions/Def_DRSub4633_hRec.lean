-- Prove2me | Definitions.Def_DRSub4633_hRec
-- name    : DRSub4633_hRec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:24.278676+00:00
-- url     : https://prove2.me/theorems/4d15b0e9-1850-4b96-b510-9518af6bfb8b
-- title:
--   The recovery map $h(x)$
-- statement:
--   The recovery map applies the scalar recovery coordinatewise:
--   $$h(x)=(h(x_1),\dots,h(x_n)).$$
--   It maps the cube into itself with $0\le h(x)\le x$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (9), p.9

import Mathlib
import Definitions.Def_DRSub4633_hScalar

namespace DRSub4633

/-- **The recovery map `h(x) = (h(x₁), …, h(xₙ))`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (9), p.9: "Its
coordinatewise extension is `h(x) = (h(x₁), . . . , h(xₙ))`."

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def hRec {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => hScalar (x j))

end DRSub4633


