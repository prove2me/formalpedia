-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW
-- name    : LogBarrierIPM_Curvature_TropicalCentralPathLW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:46.535374+00:00
-- url     : https://prove2.me/theorems/d9050de7-c04c-41b0-9ab9-152963f10d90
-- title:
--   The tropical central path $\mathcal C^{\mathrm{trop}}(\lambda)=(x^\lambda,w^\lambda,s^\lambda,y^\lambda)$ of $\mathbf{LW}_r$, explicitly (Props. 20, 21 and (20))
-- statement:
--   This module states, as a definition, the paper's explicit description of the tropical central path $\mathcal C^{\mathrm{trop}}(\lambda)=(x^\lambda,w^\lambda,s^\lambda,y^\lambda)\in\mathbb R^{2N}$, $N=5r-1$, of the Puiseux linear program $\mathbf{LW}^=_r$, as given by Propositions 20 and 21 and the identity (20). For $\lambda\in\mathbb R$:
--
--   1. (Proposition 20) the $x$-part is given by the recursion
--   $$x^\lambda_1=\min(\lambda,2),\quad x^\lambda_2=1,\quad x^\lambda_{2j+1}=1+\min(x^\lambda_{2j-1},x^\lambda_{2j}),\quad x^\lambda_{2j+2}=(1-1/2^j)+\max(x^\lambda_{2j-1},x^\lambda_{2j})\quad(1\le j<r);$$
--   2. (Proposition 21, (30)) the slack part is
--   $$w^\lambda_1=2,\quad w^\lambda_2=1,\quad w^\lambda_{3j}=1+x^\lambda_{2j-1},\quad w^\lambda_{3j+1}=1+x^\lambda_{2j},\quad w^\lambda_{3j+2}=x^\lambda_{2j+2}\quad(1\le j<r);$$
--   3. (identity (20), $x^\lambda_j\odot s^\lambda_j=\lambda=w^\lambda_i\odot y^\lambda_i$) the dual part is
--   $$s^\lambda_j=\lambda-x^\lambda_j\quad(1\le j\le 2r),\qquad y^\lambda_i=\lambda-w^\lambda_i\quad(1\le i\le 3r-1).$$
--
--   Table 1 and the claims in the proof of Theorem 25 are statements about this point.
--
--   **Formalization Note** Propositions 20 and 21 identify these formulas with the valuation of the central path of $\mathbf{LW}^=_r$ over $\mathbb K$; they are milestones of mission 1 of this series and are not restated here. The coordinates are functions of the paper's 1-based index $i$ (`tropX λ i`, `tropW λ i`, `tropS λ i`, `tropY λ i`); their values outside $1\le i\le 2r$ (resp. $3r-1$) are not used. Because the recursion does not involve $r$, the coordinates do not depend on $r$; $r$ only fixes the length of the vector `tropCentralPathLW r λ`, which lists the blocks in the order $(x,w,s,y)$ with 0-based positions.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 19, Proposition 20 and Proposition 21 (eq. (30)); p. 16, eq. (20)

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_TropicalLW

namespace LogBarrierIPM.Curvature

/-- `x^λ_i` (1-based, `1 ≤ i ≤ 2r`), the `x`-part of the tropical central path of `LW_r`
(Proposition 20, p. 19). -/
noncomputable def tropX (lam : ℝ) (i : ℕ) : ℝ :=
  if i % 2 = 1 then (LogBarrierIPM.Iterations.xPair lam ((i - 1) / 2)).1 else (LogBarrierIPM.Iterations.xPair lam ((i - 2) / 2)).2

/-- `w^λ_i` (1-based, `1 ≤ i ≤ 3r − 1`), the slack part of the tropical central path of `LW_r`,
by (30) of Proposition 21 (p. 19): `w_1 = 2`, `w_2 = 1`, and for `1 ≤ j < r`
`w_{3j} = 1 + x_{2j−1}`, `w_{3j+1} = 1 + x_{2j}`, `w_{3j+2} = x_{2j+2}`. -/
noncomputable def tropW (lam : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then 2
  else if i = 2 then 1
  else if i % 3 = 0 then 1 + (LogBarrierIPM.Iterations.xPair lam (i / 3 - 1)).1
  else if i % 3 = 1 then 1 + (LogBarrierIPM.Iterations.xPair lam (i / 3 - 1)).2
  else (LogBarrierIPM.Iterations.xPair lam (i / 3)).2

/-- `s^λ_j = λ − x^λ_j`, the dual slack part, by (20) (p. 16). -/
noncomputable def tropS (lam : ℝ) (i : ℕ) : ℝ := lam - tropX lam i

/-- `y^λ_i = λ − w^λ_i`, the dual part, by (20) (p. 16). -/
noncomputable def tropY (lam : ℝ) (i : ℕ) : ℝ := lam - tropW lam i

/-- The point `C^trop(λ) = (x^λ, w^λ, s^λ, y^λ) ∈ ℝ^{2N}`, `N = 5r − 1`, of the tropical central path
of `LW_r`, as given explicitly by Propositions 20 and 21 and the identity (20). Coordinate `k` of
each block is the paper's coordinate `k + 1`. -/
noncomputable def tropCentralPathLW (r : ℕ) (lam : ℝ) :
    Fin ((2 * r + (3 * r - 1)) + (2 * r + (3 * r - 1))) → ℝ :=
  Fin.append
    (Fin.append (fun k : Fin (2 * r) => tropX lam (k.val + 1))
      (fun i : Fin (3 * r - 1) => tropW lam (i.val + 1)))
    (Fin.append (fun k : Fin (2 * r) => tropS lam (k.val + 1))
      (fun i : Fin (3 * r - 1) => tropY lam (i.val + 1)))

end LogBarrierIPM.Curvature


