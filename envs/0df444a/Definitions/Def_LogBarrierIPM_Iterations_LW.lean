-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_LW
-- name    : LogBarrierIPM_Iterations_LW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:23.31881+00:00
-- url     : https://prove2.me/theorems/166d6d8a-46fc-4073-94e5-eeb5856f7a97
-- title:
--   The linear programs $\mathbf{LW}^=_r(t)$ in slack form and the wide neighborhood $\mathcal N^{-\infty}_{\theta,t}$ of their central path
-- statement:
--   For an integer $r\ge1$ and a real parameter $t>0$, the linear program $\mathrm{LW}_r(t)$ of the paper is
--   $$\begin{aligned}&\text{minimize } x_1 \text{ subject to } x_1\le t^2,\quad x_2\le t,\\ &x_{2j+1}\le t\,x_{2j-1},\quad x_{2j+1}\le t\,x_{2j},\quad x_{2j+2}\le t^{1-1/2^j}(x_{2j-1}+x_{2j})\quad(1\le j<r),\\ &x_{2r-1}\ge0,\ x_{2r}\ge0.\end{aligned}$$
--   Introducing slack variables $w_1,\dots,w_{3r-1}$ for the first $3r-1$ inequalities and adding the redundant constraints $x_i\ge0$ gives the program $\mathrm{LW}^=_r(t)=\mathrm{LP}(A,b,c)$ with $n=2r$, $m=3r-1$, $N=5r-1$, whose rows $Ax+w=b$ are
--   $$\begin{aligned} x_1+w_1&=t^2, & x_2+w_2&=t,\\ x_{2j+1}-t\,x_{2j-1}+w_{3j}&=0, & x_{2j+1}-t\,x_{2j}+w_{3j+1}&=0,\\ x_{2j+2}-t^{1-1/2^j}(x_{2j-1}+x_{2j})+w_{3j+2}&=0 &&(1\le j<r),\end{aligned}$$
--   so $b=(t^2,t,0,\dots,0)$, and $c=(1,0,\dots,0)\in\mathbb R^{2r}$. The set $\mathcal N^{-\infty}_{\theta,t}$ is the wide neighborhood $\mathcal N^{-\infty}_\theta$ of (5) for this data:
--   $$\mathcal N^{-\infty}_{\theta,t}=\Big\{z=(x,w,s,y)\in\mathcal F^\circ(t):\ \begin{pmatrix} xs\\ wy\end{pmatrix}\ge(1-\theta)\bar\mu(z)e\Big\},\qquad \bar\mu(z)=\frac{\langle x,s\rangle+\langle w,y\rangle}{5r-1}.$$
--
--   This is the family on which the paper's exponential lower bound for log-barrier interior point methods is proved.
--
--   **Formalization Note** Lean indices are 0-based: Lean row $i$ is the paper's row $i+1$ and Lean column $k$ is the paper's variable $x_{k+1}$. The entries are produced by a function of the paper's 1-based row and column numbers, so the rows above can be read off directly. $t^{1-1/2^j}$ is the real power `Real.rpow`. The dual constraint $s-A^\top y=c$ is not expanded by hand; it is taken from the general definition. The neighborhood is defined for every real $t$ and $\theta$; the theorems impose $0<\theta<1$ and the size condition on $t$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 2 (LW_r(t)); p. 18 (§4.3, LW^=_r, N = 5r − 1); p. 19, eq. (28); p. 17 (N^{−∞}_{θ,t})

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP

open Matrix

namespace LogBarrierIPM.Iterations

/-- Entry `(R, C)` (paper's 1-based row `R ∈ [3r − 1]`, column `C ∈ [2r]`) of the constraint
matrix of `LW^=_r(t)` (p. 2, slack form (28), p. 19):
row 1: `x_1`; row 2: `x_2`; for `1 ≤ j < r`, row `3j`: `x_{2j+1} − t x_{2j−1}`,
row `3j+1`: `x_{2j+1} − t x_{2j}`, row `3j+2`: `x_{2j+2} − t^{1 − 1/2^j} (x_{2j−1} + x_{2j})`. -/
noncomputable def lwEntry (t : ℝ) (R C : ℕ) : ℝ :=
  if R = 1 then (if C = 1 then 1 else 0)
  else if R = 2 then (if C = 2 then 1 else 0)
  else if R % 3 = 0 then
    (if C = 2 * (R / 3) + 1 then 1 else if C = 2 * (R / 3) - 1 then -t else 0)
  else if R % 3 = 1 then
    (if C = 2 * (R / 3) + 1 then 1 else if C = 2 * (R / 3) then -t else 0)
  else
    (if C = 2 * (R / 3) + 2 then 1
     else if C = 2 * (R / 3) - 1 ∨ C = 2 * (R / 3) then -(t ^ ((1 : ℝ) - 1 / 2 ^ (R / 3)))
     else 0)

/-- The `(3r − 1) × 2r` constraint matrix `A` of `LW^=_r(t)`; the 0-based Lean index `i`
(resp. `k`) is the paper's row `i + 1` (resp. variable `x_{k+1}`). -/
noncomputable def lwA (r : ℕ) (t : ℝ) : Matrix (Fin (3 * r - 1)) (Fin (2 * r)) ℝ :=
  fun i k => lwEntry t (i.val + 1) (k.val + 1)

/-- The right-hand side `b = (t², t, 0, …, 0) ∈ ℝ^{3r−1}` of `LW^=_r(t)`. -/
noncomputable def lwB (r : ℕ) (t : ℝ) : Fin (3 * r - 1) → ℝ :=
  fun i => if i.val = 0 then t ^ 2 else if i.val = 1 then t else 0

/-- The objective `c = (1, 0, …, 0) ∈ ℝ^{2r}` of `LW^=_r(t)` ("minimize `x_1`"). -/
def lwC (r : ℕ) : Fin (2 * r) → ℝ :=
  fun k => if k.val = 0 then 1 else 0

/-- The wide neighborhood `N^{−∞}_{θ,t}` of the primal-dual central path of `LW^=_r(t)`
(p. 17), i.e. the set (5) for `LP(A, b, c)` with the data of `LW^=_r(t)`; here
`n = 2r`, `m = 3r − 1`, `N = 5r − 1`. -/
def lwWideNeighborhood (r : ℕ) (θ t : ℝ) : Set (PDPoint (2 * r) (3 * r - 1)) :=
  wideNeighborhood (lwA r t) (lwB r t) (lwC r) θ

end LogBarrierIPM.Iterations


