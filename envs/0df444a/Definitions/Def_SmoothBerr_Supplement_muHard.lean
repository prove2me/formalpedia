-- Prove2me | Definitions.Def_SmoothBerr_Supplement_muHard
-- name    : SmoothBerr_Supplement_muHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:55:58.276336+00:00
-- url     : https://prove2.me/theorems/3d2f14fa-3a50-40f7-87d5-c354fefa892f
-- title:
--   The measure $\mu=\delta_{\kappa^{-1}}+(1-2\varepsilon)\,\mathrm{Unif}[2\varepsilon,1]$ of Eq. (21)
-- statement:
--   For $\kappa>0$ and $0<\varepsilon\le1/2$, the measure
--   $$
--   \mu:=\delta_{\kappa^{-1}}+(1-2\varepsilon)\,\mathrm{Unif}[2\varepsilon,1]
--   $$
--   puts a unit point mass at $x_0=1/\kappa$ and spreads mass $1-2\varepsilon$ uniformly over $I_\varepsilon=[2\varepsilon,1]$. An odd polynomial that is small in $L^2(\mu)$ relative to $1/x$ must be large at $1/\kappa$ and small on $I_\varepsilon$, which forces a large degree (Theorem 7.1).
--
--   **Formalization Note** $(1-2\varepsilon)\,\mathrm{Unif}[2\varepsilon,1]$ is Lebesgue measure restricted to $[2\varepsilon,1]$. The measure is finite, of mass $2-2\varepsilon$, and not normalized.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §7.1, Eq. (21), p.19

import Mathlib

open MeasureTheory

namespace SmoothBerr.Supplement

/-- The measure **`µ := δ_{κ⁻¹} + (1 − 2ε) Unif[2ε, 1]`** of Eq. (21) (Dereziński, Mahoney, Meyer,
Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript
of 3 Nov 2026, sha256 9575cd20…, §7.1, Eq. (21), p.19): a unit point mass at `x₀ = 1/κ` plus
Lebesgue measure on `I_ε = [2ε, 1]`.

**Formalization Note** `(1 − 2ε) Unif[2ε, 1]` is Lebesgue measure restricted to `[2ε, 1]` (for
`2ε ≤ 1`); the measure is finite, of mass `2 − 2ε`, and not normalized. -/
noncomputable def muHard (κ ε : ℝ) : Measure ℝ :=
  Measure.dirac (1 / κ) + volume.restrict (Set.Icc (2 * ε) 1)

end SmoothBerr.Supplement


