-- Prove2me | Definitions.Def_ConstrSOSP_groupPoly
-- name    : ConstrSOSP_groupPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:58.614865+00:00
-- url     : https://prove2.me/theorems/08099faf-e2b7-4fff-9e73-02e71a672167
-- title:
--   Representative polynomial of a group (Table 3)
-- statement:
--   The Hermite polynomial (17) with corner values $(z_{00},z_{10},z_{01},z_{11})$ and corner arrows, in the order $(0,0),(1,0),(0,1),(1,1)$ of Table 3, each arrow standing for its gradient (L $=(1/2,0)$, R $=(-1/2,0)$, U $=(0,-1/2)$, D $=(0,1/2)$), and corner Hessian $\sigma I$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Table 3, p.34; §5.4.1, p.32

import Mathlib
import Definitions.Def_ConstrSOSP_Dir
import Definitions.Def_ConstrSOSP_dirGrad
import Definitions.Def_ConstrSOSP_fsigma

namespace ConstrSOSP

/-- **The representative polynomial of a group** (arXiv:2604.02285, 2 Nov 2026, Table 3, p.34,
and §5.4.1, p.32: "let f_σ denote the unique biquintic interpolation polynomial with corner Hessian
σI and the remaining mixed corner derivative data set to zero"): the Hermite polynomial (17)
(`fsigma`) with corner values `(z₀₀, z₁₀, z₀₁, z₁₁)` and corner arrows `(d₀₀, d₁₀, d₀₁, d₁₁)`, in
the order `(0, 0), (1, 0), (0, 1), (1, 1)` of Table 3, each arrow standing for its gradient
(`dirGrad`: L = (1/2, 0), R = (−1/2, 0), U = (0, −1/2), D = (0, 1/2)). -/
noncomputable def groupPoly (σ z00 z10 z01 z11 : ℝ) (d00 d10 d01 d11 : Dir) : ℝ → ℝ → ℝ :=
  fsigma σ ![![z00, z01], ![z10, z11]]
    (fun i j => dirGrad (![![d00, d01], ![d10, d11]] i j) 0)
    (fun i j => dirGrad (![![d00, d01], ![d10, d11]] i j) 1)

end ConstrSOSP


