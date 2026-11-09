-- Prove2me | Definitions.Def_ResultantVNP_IsVNPHardPProj
-- name    : ResultantVNP_IsVNPHardPProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:53.580888+00:00
-- url     : https://prove2.me/theorems/7e6989ce-a4d6-4910-84e7-db4f776cbaa0
-- title:
--   VNP-hardness under p-projections
-- statement:
--   A family $(f_n)$ is a **p-projection** of $(g_m)$ if each $f_n$ is a projection of some $g_{t(n)}$ with $t(n)$ polynomially bounded. A family $\{G_m\}_{m\ge m_0}$ is **VNP-hard under p-projections** over $\mathbb C$ if every VNP family is a p-projection of it.
--
--   **Formalization Note** The index set $\{m\ge m_0\}$ is encoded by requiring $t(n)\ge m_0$ for the indices used.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib
import Definitions.Def_ResultantVNP_VNP
import Definitions.Def_ResultantVNP_IsProjection

namespace ResultantVNP

/-- The family `{G_m}_{m ≥ lo}` is **VNP-hard under p-projections** over `ℂ`: every VNP family `(f_n)`
is a p-projection of it, i.e. each `f_n` is a projection of some `G_{t(n)}` with `t(n) ≥ lo`
polynomially bounded.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14: "A family (f_n) is a p-projection of (g_n) if each f_n is a projection of
some g_{q(n)} with q(n) polynomially bounded. [...] A polynomial family is VNP-hard under a specified
reduction if every VNP family has such a reduction to it."

**Formalization Note** The index set `{m ≥ lo}` of the family is encoded by the requirement
`lo ≤ t n`; the family is given for every `m`, but only members with `m ≥ lo` are used. -/
def IsVNPHardPProj {τ : ℕ → Type} (G : ∀ m, MvPolynomial (τ m) ℂ) (lo : ℕ) : Prop :=
  ∀ f ∈ VNP, ∃ t : ℕ → ℕ, PolyBounded t ∧ ∀ n, lo ≤ t n ∧ IsProjection (f.p n) (G (t n))

end ResultantVNP


