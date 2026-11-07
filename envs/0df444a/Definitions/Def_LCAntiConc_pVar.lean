-- Prove2me | Definitions.Def_LCAntiConc_pVar
-- name    : LCAntiConc_pVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:01.35822+00:00
-- url     : https://prove2.me/theorems/6d56bc19-7ac5-4111-9968-714254fc7894
-- title:
--   Pseudo-variance $\mathrm{Var}_{\tilde{\mathbb E}}(f)$
-- statement:
--   For a pseudo-expectation $\tilde{\mathbb E}$ and a polynomial $f$, the **pseudo-variance** is
--
--   $$\mathrm{Var}_{\tilde{\mathbb E}}(f)=\tilde{\mathbb E}\,f^2-(\tilde{\mathbb E}\,f)^2 .$$
--
--   **Formalization Note** The page defines it for $\deg f\le D/2$, and every statement applies it only to such $f$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), below Definition 3.2, p.16 (PDF p.18)

import Mathlib

namespace LCAntiConc

/-- The pseudo-variance `Var_Ẽ(f) = Ẽ f² - (Ẽ f)²` of a polynomial `f`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), below Definition 3.2, p.16 (PDF p.18).

**Formalization Note** The page defines it for `deg f ≤ D/2`; every statement applies it only to
such `f`. -/
noncomputable def pVar {n : ℕ} (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  L (f ^ 2) - (L f) ^ 2

end LCAntiConc


