-- Prove2me | Definitions.Def_RandTreeUniv_alpha
-- name    : RandTreeUniv_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:21.360799+00:00
-- url     : https://prove2.me/theorems/aef0785c-fb6e-4d44-a514-cfacc7f2be75
-- title:
--   $\alpha=n\psi\ln\ln n/(K^3\ln n)$
-- statement:
--   For a large absolute constant $K$, a value $\psi\ge1$ and $n$, set
--
--   $$
--   \alpha=\alpha(n)=\frac{n\,\psi\ln\ln n}{K^3\ln n}.
--   $$
--
--   For $\psi=1$ this is display (11), $\alpha=n\ln\ln n/(K^3\ln n)$, which is the value used throughout §6. The tree families are defined in terms of $\alpha$: $\mathcal T_1$ asks for $K\alpha$ bare paths of length $n/(K^2\alpha)=K\ln n/(\psi\ln\ln n)$, $\mathcal T_2$ for at most $e^{\Delta^5}\alpha$ leaves.
--
--   **Formalization Note** $\alpha$ is a real number; the paper ignores rounding.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), display (11), p.21 (PDF 22); §5, p.25 (PDF 26); §6, p.31 (PDF 32)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `α = α(n) := n ψ ln ln n / (K³ ln n)` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §5, p.25 (PDF 26); for `ψ = 1` this is display
(11), p.21 (PDF 22), the `α` used throughout §6, p.31 (PDF 32)). `K` is the large absolute
constant of §4.

**Formalization Note** `ln` is `Real.log`; `α` is a real number (the paper ignores rounding,
§2.1). -/
noncomputable def alpha (K ψ : ℝ) (n : ℕ) : ℝ :=
  n * ψ * Real.log (Real.log n) / (K ^ 3 * Real.log n)

end RandTreeUniv


