-- Prove2me | Definitions.Def_MaxWeightInstab_rRho
-- name    : MaxWeightInstab_rRho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:53.862852+00:00
-- url     : https://prove2.me/theorems/52a61c4d-7efd-4672-8a05-a6debb6bbc4b
-- title:
--   $r_{\boldsymbol\rho}=a(1+1/\nu)$ of display (4)
-- statement:
--   $r_{\boldsymbol\rho}:=a\left(1+\frac1\nu\right)$. Condition (4) is $r_{\boldsymbol\rho}<1$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (4), p.3

import Mathlib

namespace MaxWeightInstab

/-- `r_ρ := a(1 + 1/ν)`, display (4) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.3). Condition (4) is `r_ρ < 1`.

**Formalization Note.** Every statement using it assumes `ν ≥ 1`, so `1/ν` is the real reciprocal. -/
noncomputable def rRho (a : ℝ) (ν : ℕ) : ℝ :=
  a * (1 + 1 / (ν : ℝ))

end MaxWeightInstab


