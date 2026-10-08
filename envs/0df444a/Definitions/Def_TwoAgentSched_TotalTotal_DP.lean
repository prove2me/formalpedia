-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_DP
-- name    : TwoAgentSched_TotalTotal_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:14.273736+00:00
-- url     : https://prove2.me/theorems/5c60f7b7-414f-4e2f-a6ec-90942969d547
-- title:
--   §9, recursion (7) — the dynamic program $F(i,j,q)$ and the sums $P(i,j)$
-- statement:
--   The dynamic program of §9 of Agnetis, Mirchandani, Pacciarelli and Pacifici for $1\|\sum C^A_i:\sum C^B_i$. For a two-agent instance whose jobs are numbered so that $p^A_1\le\dots\le p^A_{n_A}$ and $p^B_1\le\dots\le p^B_{n_B}$, let $P(i,j)$ be the sum of the processing times of $J^A_1,\dots,J^A_i$ and $J^B_1,\dots,J^B_j$, i.e. of the $i$ shortest $A$-jobs and the $j$ shortest $B$-jobs. The value $F(i,j,q)\in\mathbb N\cup\{+\infty\}$, for integers $i,j\ge0$ and $q$, is given by the recursion
--
--   $$F(i,j,q)=\min\bigl\{F(i-1,j,q)+P(i-1,j)+p^A_i;\ F(i,j-1,q-P(i,j))\bigr\}\qquad(7)$$
--
--   with the initialisation $F(0,0,q)=0$ for $q\ge0$ and $F(i,j,q)=+\infty$ for $q<0$. The first argument of the minimum is $+\infty$ when $i=0$, and the second is $+\infty$ when $j=0$.
--
--   $F(i,j,q)$ is intended to be the least total completion time of agent $A$ over schedules of $J^A_1,\dots,J^A_i,J^B_1,\dots,J^B_j$ in which agent $B$'s total completion time is at most $q$; Theorem 9.3 states this for $(n_A,n_B,Q)$.
--
--   **Formalization Note** The paper initialises $F(0,0,q)$ for $q=0,\dots,Q$ and $F(i,j,q)$ for $q<0$ only. The terms $F(-1,j,q)$ and $F(i,-1,q)$ that (7) would need at $i=0$ or $j=0$ are not mentioned; they are read as $+\infty$ (no schedule with a negative number of jobs). Values lie in $\mathbb N_\infty$. `pAt i` is $p^A_i$ for the 1-based index $i$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, §9, recursion (7) and its initialization

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Model

namespace TwoAgentSched.TotalTotal

namespace Instance

variable (I : Instance)

/-- `p^A_i` for the 1-based index `i`, as a function of a natural number: `p^A_i = pA ⟨i - 1, _⟩`
for `1 ≤ i ≤ n_A`, and `0` outside that range (never used there by `dpF`). -/
def pAt (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ I.nA then I.pA ⟨i - 1, by omega⟩ else 0

/-- `P(i, j)` (§9, p. 238): the sum of the processing times of the A-jobs `J^A_1, …, J^A_i` and of
the B-jobs `J^B_1, …, J^B_j`; when each agent's jobs are numbered in SPT order, these are the `i`
shortest A-jobs and the `j` shortest B-jobs. -/
def bigPij (i j : ℕ) : ℕ :=
  (∑ h : Fin I.nA, if h.val < i then I.pA h else 0) +
    (∑ h : Fin I.nB, if h.val < j then I.pB h else 0)

/-- The dynamic-programming value `F(i, j, q)` of recursion (7) (§9, p. 238), with values in
`ℕ∞ = ℕ ∪ {+∞}` and `q ∈ ℤ`:
`F(i, j, q) = min{F(i - 1, j, q) + P(i - 1, j) + p^A_i ; F(i, j - 1, q - P(i, j))}`,
initialized by `F(0, 0, q) = 0` for `q ≥ 0` and `F(i, j, q) = +∞` for `q < 0`. The terms
`F(-1, j, q)` (first argument of the min when `i = 0`) and `F(i, -1, q)` (second argument when
`j = 0`), on which the paper is silent, are read as `+∞`. -/
noncomputable def dpF : ℕ → ℕ → ℤ → ℕ∞
  | i, j, q =>
    if q < 0 then ⊤
    else if i = 0 ∧ j = 0 then 0
    else
      min
        (if _hi : 0 < i then
            dpF (i - 1) j q + ((I.bigPij (i - 1) j + I.pAt i : ℕ) : ℕ∞)
          else ⊤)
        (if _hj : 0 < j then dpF i (j - 1) (q - (I.bigPij i j : ℤ)) else ⊤)
  termination_by i j => i + j

end Instance

end TwoAgentSched.TotalTotal


