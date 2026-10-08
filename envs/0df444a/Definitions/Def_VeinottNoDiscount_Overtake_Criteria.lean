-- Prove2me | Definitions.Def_VeinottNoDiscount_Overtake_Criteria
-- name    : VeinottNoDiscount_Overtake_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:01.103276+00:00
-- url     : https://prove2.me/theorems/aa42588f-6b44-40d3-9250-babd6c3e0242
-- title:
--   The n-period total expected return Vⁿ(π) (p. 1293)
-- statement:
--   This file defines the finite-horizon return in Veinott's average-overtaking criterion on top of Blackwell's finite decision model: a finite set of states $s$, a finite set of actions, incomes $i(s,a)$ and transition probabilities $q(s'\mid s,a)$. A decision rule $f\in F$ picks an action in every state; $r(f)$ is its income vector and $Q(f)$ its transition matrix. For a policy $\pi=(f_1,f_2,\dots)$, $Q_n(\pi)=Q(f_1)\cdots Q(f_n)$ with $Q_0(\pi)=I$. The **gain** and **bias** of the stationary policy $f^\infty=(f,f,\dots)$ are
--   $$x(f)=Q^*(f)\,r(f),\qquad y(f)=H(f)\,r(f),$$
--   where $Q^*(f)$ is the Cesàro limit of the powers of $Q(f)$ and $H(f)=(I-Q(f)+Q^*(f))^{-1}-Q^*(f)$. Vectors are compared coordinatewise.
--
--   The shared definitions give $F'=\{f\in F : x(f)\ge x(g)\text{ for all } g\in F\}$, the decision rules of maximal average return per unit time, and $F''=\{f\in F' : y(f)\ge y(g)\text{ for all } g\in F'\}$, those among them of maximal bias. This file defines the vector of total expected returns in periods $1,2,\dots,n$, starting from each state and using the policy $\pi$:
--   $$V^n(\pi)=\sum_{i=0}^{n-1}Q_i(\pi)\,r(f_{i+1}),\qquad V^0(\pi)=0 .$$
--
--   $F''$ is the set that Theorem 7 characterizes by comparing the averages $N^{-1}\sum_{n=1}^N V^n$ of finite-horizon returns.
--
--   **Formalization Note** Every action is available in every state ($A_s=A$ for all $s$), as in the published Blackwell model this file builds on. Policies are indexed from $0$: the Lean `π 0` is $f_1$, so $f_{i+1}$ is `π i`. $x(f)$ and $y(f)$ are the published closed forms; that they are the unique solutions of Veinott's (2), (3) is Blackwell's Theorem 3.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1293, §5: Vⁿ(π)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

variable {St Act : Type*} [Fintype St] [DecidableEq St]

/-- `V^n(π) = Σ_{i=0}^{n−1} Q_i(π) r(f_{i+1})`: the vector of total expected returns in periods
`1, 2, ⋯, n` starting from each state and using the policy `π`.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1293, §5 (unnumbered display).

**Formalization Note.** Policies are indexed from `0` (`π 0` is the paper's `f₁`), so
`f_{i+1}` is `π i` and `Q_i(π) = Q(f₁)⋯Q(f_i)` is the published `M.Qn π i`. `V^0(π) = 0`
(empty sum). -/
noncomputable def Vn (M : Model St Act) (π : Policy St Act) (n : ℕ) : St → ℝ :=
  ∑ i ∈ Finset.range n, M.Qn π i *ᵥ M.r (π i)

end VeinottNoDiscount.Overtake


