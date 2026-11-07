-- Prove2me | Definitions.Def_HeilmanMax3Cut_fjRatio
-- name    : HeilmanMax3Cut_fjRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:56.687942+00:00
-- url     : https://prove2.me/theorems/0f423829-499a-456a-9af5-84598f94d0cc
-- title:
--   The Frieze–Jerrum ratio function $r(\rho)$
-- statement:
--   For a real number $\rho$ let
--
--   $$r(\rho)=\frac{\tfrac32\Bigl[1-3\Bigl(\tfrac19+\frac{[\arccos(-\rho)]^2-[\arccos(\rho/2)]^2}{4\pi^2}\Bigr)\Bigr]}{1-\rho},$$
--
--   the expression whose infimum over $-\tfrac12\le\rho\le1$ is the Frieze–Jerrum constant $\alpha_3$ of Eq. (2).
--
--   **Formalization Note** $\arccos$ takes values in $[0,\pi]$. At $\rho=1$ the fraction is $0/0$, which Lean would evaluate to $0$; the infimum is therefore taken over $[-\tfrac12,1)$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (2), p.3

import Mathlib
open Real

namespace HeilmanMax3Cut

/-- **The Frieze–Jerrum ratio function.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (2), p.3: the expression under the infimum
defining `α₃`,

`r(ρ) = (3/2) · [1 − 3 (1/9 + ([arccos(−ρ)]² − [arccos(ρ/2)]²)/(4π²))] / (1 − ρ)`.

**Formalization Note.** `arccos` is `Real.arccos` (values in `[0, π]`). At `ρ = 1` the printed
fraction is `0/0`, and Lean's division would return `0`; the infimum `alpha3` therefore ranges over
`[−1/2, 1)` only. -/
noncomputable def fjRatio (ρ : ℝ) : ℝ :=
  (3 / 2) * (1 - 3 * (1 / 9 + (Real.arccos (-ρ) ^ 2 - Real.arccos (ρ / 2) ^ 2) / (4 * π ^ 2))) /
    (1 - ρ)

end HeilmanMax3Cut


