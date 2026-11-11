-- Prove2me | Definitions.Def_AgnHalfMem_Kfun
-- name    : AgnHalfMem_Kfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:47.83859+00:00
-- url     : https://prove2.me/theorems/ef37d427-d11d-49d3-866e-fa01efbb5c83
-- title:
--   The Gaussian sine integral $K(t)$
-- statement:
--   For $G\sim N(0,1)$ and $t\in\mathbb R$,
--   $$
--   K(t)=\mathbb E_G[\sin(tG)\,\mathrm{sign}(G)].
--   $$
--   It is the correlation between a sine of a Gaussian and its sign, and drives the correlation of the sine functions with halfspaces (Claim 4.8). Claim A.1 states that $K(t)=\mathbb E[\sin(t|G|)]$ for $t\ge 0$ and bounds it below.
--
--   **Formalization Note** $\mathrm{sign}(0)=+1$; the value at $G=0$ is irrelevant, $\{0\}$ being a null set.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim A.1, p.25; p.15

import Mathlib
import Definitions.Def_AgnHalfMem_sgn

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **The Gaussian sine integral `K(t)`.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Claim A.1, p.25 (also p.15): "For G ∼ N(0, 1) and t ≥ 0, define
K(t) = E_G[sin(tG) sign(G)] = E_G[sin(t|G|)]".

`Kfun t = E[sin(tG) sign(G)]` for `G ∼ N(0, 1)`.

**Formalization Note.** `sign(0) = +1` (footnote 1, p.2); the value at `G = 0` does not matter
since `{0}` is a null set. The second expression `E[sin(t|G|)]` is part of Claim A.1. -/
noncomputable def Kfun (t : ℝ) : ℝ :=
  ∫ g, Real.sin (t * g) * sgn (signB g) ∂(gaussianReal 0 1)

end AgnHalfMem


