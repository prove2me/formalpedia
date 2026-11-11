-- Prove2me | Definitions.Def_DoubleCorrRME_InputLayout
-- name    : DoubleCorrRME_InputLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:03.366876+00:00
-- url     : https://prove2.me/theorems/cd92174d-8e9c-4c6c-9f90-5b1b5e2d9319
-- title:
--   Input layouts of Theorem 1.3 and Theorem A.1
-- statement:
--   The input of Theorem 1.3 holds the arguments of Algorithm 2: integer cells $0,1,2$ contain $N,n,d$; real cells $0,1,2$ contain $\varepsilon,\alpha,\delta$; then coordinate $a$ of $x_{i,j}$ (0-based $i,j,a$) is in real cell $3+(in+j)d+a$. Every other cell is $0$.
--
--   The input of Theorem A.1 holds the arguments of Algorithm 7: integer cells $0,1$ contain $n,d$; real cells $0,1,2$ contain $\Lambda,\alpha,\delta$; then coordinate $a$ of $X_k$ is in real cell $3+kd+a$.
--
--   Because the parameters are part of the input, one program serves every parameter value.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Algorithm 2, p.30 (PDF p.31); Algorithm 7, p.62 (PDF p.63)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Machine

namespace DoubleCorrRME

/-!
# Input layouts of Theorem 1.3 and Theorem A.1

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): Algorithm 2,
`BatchMeanEst({x_{i,j}}, ε, α, δ)`, p.30 (PDF p.31); Algorithm 7, `OneLevelQUE(Y, Λ, α, δ)`, p.62
(PDF p.63).

**Formalization Note.** The program receives its parameters as input, as the paper's procedures do,
so one program serves every parameter value.
* `goalInput`: integer memory holds `N, n, d` in cells `0, 1, 2`; real memory holds `ε, α, δ` in
  cells `0, 1, 2`, then the data, coordinate `a` of `x_{i,j}` (0-based `i, j, a`) in cell
  `3 + (i·n + j)·d + a`. Every other cell is `0`.
* `oneLevelInput`: integer memory holds `n, d` in cells `0, 1`; real memory holds `Λ, α, δ` in cells
  `0, 1, 2`, then coordinate `a` of `X_k` in cell `3 + k·d + a`.
-/

/-- The input of Theorem 1.3 (the arguments of Algorithm 2). -/
noncomputable def goalInput (N n d : ℕ) (ε α δ : ℝ) (x : Fin N → Fin n → Vec d) : State :=
  initState [(N : ℤ), (n : ℤ), (d : ℤ)]
    ([ε, α, δ] ++ List.ofFn fun k : Fin (N * n * d) =>
      let r := (finProdFinEquiv.symm k).1
      x (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm k).2)

/-- The input of Theorem A.1 (the arguments of Algorithm 7). -/
noncomputable def oneLevelInput (n d : ℕ) (Λ α δ : ℝ) (X : Fin n → Vec d) : State :=
  initState [(n : ℤ), (d : ℤ)]
    ([Λ, α, δ] ++ List.ofFn fun k : Fin (n * d) =>
      X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

end DoubleCorrRME


