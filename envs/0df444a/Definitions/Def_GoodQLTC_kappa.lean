-- Prove2me | Definitions.Def_GoodQLTC_kappa
-- name    : GoodQLTC_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:30.405953+00:00
-- url     : https://prove2.me/theorems/90f51cac-f601-484f-8cf3-5dd7bf84b319
-- title:
--   Local filling constants $\kappa_{r,u}$ (Equation (6.1))
-- statement:
--   For integers $r\ge1$ and $0\le u<r$,
--   $$
--   \kappa_{r,u}=\begin{cases}\rho,&u\in\{0,r-1\},\\[2pt] \dfrac{\kappa_{r-1,u}\,\kappa_{r-1,u-1}}{\tau+1},&1\le u\le r-2.\end{cases}\tag{6.1}
--   $$
--
--   **Formalization Note** Values at $r=0$ or $u\ge r$ are placeholders, never used.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §6, Equation (6.1), p.21 (PDF p.24)

import Mathlib

namespace GoodQLTC

/-- The filling constants `κ_{r,u}` of Equation (6.1), Gay–Jeronimo, arXiv:2609.20780 (held
version), p.21: for integers `r ≥ 1` and `0 ≤ u < r`,
`κ_{r,u} := ρ` if `u ∈ {0, r−1}`, and `κ_{r,u} := κ_{r−1,u} κ_{r−1,u−1}/(τ+1)` if
`1 ≤ u ≤ r − 2`.

**Formalization Note.** `kappa ρ τ r u`; the values at `r = 0` and at `u ≥ r` are placeholders
and are never used. -/
noncomputable def kappa (ρ τ : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => ρ
  | r + 1, u => if u = 0 ∨ u = r then ρ else kappa ρ τ r u * kappa ρ τ r (u - 1) / (τ + 1)

end GoodQLTC


