-- Prove2me | Definitions.Def_BNCovPack_Packing_Scheme
-- name    : BNCovPack_Packing_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:59:31.468212+00:00
-- url     : https://prove2.me/theorems/6693e81d-ed8a-4d13-aaff-46bc2e5f2b24
-- title:
--   The online fractional packing scheme of Buchbinder–Naor (Section 3): rounds, the exponential increment rule, primal and dual values
-- statement:
--   This file defines the online primal-dual scheme for the **general online fractional packing problem** of Section 3 of Buchbinder and Naor (2009), as a deterministic function of the instance.
--
--   **Instance.** There are $n$ primal (covering) variables $x(1),\dots,x(n)$ with known costs $c(i)>0$, and $m$ dual (packing) variables $y(1),\dots,y(m)$ that arrive one per round. In round $j$ the column $a(\cdot,j)$ of non-negative coefficients is revealed. The covering problem is to minimize $\sum_i c(i)x(i)$ subject to $\sum_i a(i,j)x(i)\ge 1$ for every $j$ and $x\ge 0$; its dual packing problem is to maximize $\sum_j y(j)$ subject to $\sum_j a(i,j)y(j)\le c(i)$ for every $i$ and $y\ge 0$.
--
--   **The scheme**, with parameter $B$. Initially all $x(i)$ and $y(k)$ are $0$. Round $j$ proceeds as follows.
--
--   1. Set $y(j)\leftarrow 0$, and for every $i$ let $a_i(\max)=\max_{k\le j} a(i,k)$ be the largest coefficient of $x(i)$ among the columns revealed so far.
--   2. If $\sum_i a(i,j)x(i)\ge 1$, nothing else happens in this round.
--   3. Otherwise, for $t\ge 0$ let $y_t$ be the current dual vector with $y(j)$ set to $t$, and
--   $$x_t(i)=\max\Big\{x(i),\ \frac{1}{n\,a_i(\max)}\Big[\exp\Big(\frac{B}{2c(i)}\sum_{k=1}^{j}a(i,k)\,y_t(k)\Big)-1\Big]\Big\}.$$
--   The new value $y(j)$ is the least $t\ge 0$ with $\sum_i a(i,j)\,x_t(i)\ge 1$, and $x$ is replaced by $x_t$ for that $t$.
--
--   The paper describes step 3 as a continuous process (raise $y(j)$ while the new constraint is unsatisfied, letting each $x(i)$ follow the increment function); its discrete implementation, as the paper says on p. 4, is to find the minimal $y(j)$ at which the new primal constraint is satisfied, which is what step 3 does. After $r$ rounds the **primal value** is $X=\sum_i c(i)x(i)$ and the **dual value** is $Y=\sum_{k\le r}y(k)$.
--
--   These objects are the subject of Theorem 3.1 and of the three claims of its proof.
--
--   **Formalization Note** The instance is the published `GeneralInstance I (Fin m)` (coefficients `a ≥ 0`, costs `c > 0`); columns are `Fin m` and arrive in index order, so round `j` (0-based in Lean) processes column `j`. $n$ is `Fintype.card I`. `stateAfter inst B r` is the state after the first `r` rounds (for `r ≥ m`, the final state); `primalValue` and `dualValue` are $X$ and $Y$. The least $t$ is `sInf` of the set of admissible $t\ge0$; that set is nonempty, and its infimum attained, whenever column $j$ has a positive entry, and every theorem about the scheme assumes this (the paper's standing assumption on p. 4). If $a_i(\max)=0$ the Lean expression $1/(n\cdot 0)$ is $0$; then every $a(i,k)$ with $k\le j$ is $0$ and the paper's bracket is $0$ too. Logarithms and exponentials are natural.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, pp. 4–5, Section 3 (scheme, lines (i), (ii)a–b; discrete implementation p. 4–5); model Figure 1, p. 4

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- The state of the online fractional packing scheme (Buchbinder–Naor 2009, §3, p. 5): the
current primal (covering) solution `x : I → ℝ` and the current dual (packing) solution
`y : Fin m → ℝ`, one dual variable per column (round). -/
structure State (I : Type*) (m : ℕ) where
  /-- the primal variables `x(i)` -/
  x : I → ℝ
  /-- the dual variables `y(k)` -/
  y : Fin m → ℝ

/-- The initial state (p. 4): every `x(i)` and every `y(k)` is zero. -/
def initState (I : Type*) (m : ℕ) : State I m where
  x := fun _ => 0
  y := fun _ => 0

/-- Line (i) of the scheme (p. 5): the prefix maximum `aᵢ(max) = max_{k=1}^{j} a(i,k)` used in
round `j`, i.e. the largest coefficient of `x(i)` among the columns revealed so far
(`k ≤ j`, column `j` included). -/
noncomputable def prefixMax {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (i : I) (j : Fin m) : ℝ :=
  (Finset.univ.filter (fun k : Fin m => k ≤ j)).sup'
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_refl j⟩⟩ (inst.a i)

/-- The increment function of line (ii)b (p. 5) in round `j`, evaluated at the dual vector `y`:
`(1/(n aᵢ(max))) [exp((B/(2c(i))) ∑_{k=1}^{j} a(i,k) y(k)) − 1]`, where `n = |I|` is the number
of primal variables and `aᵢ(max)` is the prefix maximum `prefixMax inst i j`. (If
`prefixMax inst i j = 0` then `1/0 = 0` in Lean; in that case every `a(i,k)`, `k ≤ j`, is zero
and the bracket is `0` as well.) -/
noncomputable def increment {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (y : Fin m → ℝ) (j : Fin m) (i : I) : ℝ :=
  1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
    (Real.exp (B / (2 * inst.c i) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k) - 1)

/-- The primal solution of round `j` when the new dual variable has been raised to `y(j) = t`
(line (ii)b, p. 5): `x(i) ← max{x(i), increment}`, with the dual vector `s.y` updated at
coordinate `j` to `t`. -/
noncomputable def primalAt {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) (t : ℝ) : I → ℝ :=
  fun i => max (s.x i) (increment inst B (Function.update s.y j t) j i)

/-- The value given to the new dual variable `y(j)` in round `j` (p. 4–5, discrete
implementation): "one should find the minimal `y(j)` such that the new primal constraint is
satisfied", i.e. the least `t ≥ 0` with `∑ᵢ a(i,j) x_t(i) ≥ 1`, where `x_t = primalAt … t`.
When the instance's column `j` has a positive entry this set is nonempty and closed, so the
infimum is attained; every theorem about the scheme carries that hypothesis. -/
noncomputable def roundValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ ∑ i, inst.a i j * primalAt inst B s j t i}

/-- Round `j` of the scheme (p. 5), applied to the state `s` reached after the earlier rounds:
line (i) sets `y(j) ← 0`; if the new primal constraint `∑ᵢ a(i,j) x(i) ≥ 1` already holds, the
while-loop (ii) does not run and nothing changes; otherwise `y(j)` is raised to the minimal
value `roundValue` at which the constraint holds, and every `x(i)` is updated by line (ii)b. -/
noncomputable def runRound {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) : State I m :=
  if 1 ≤ ∑ i, inst.a i j * s.x i then
    ⟨s.x, Function.update s.y j 0⟩
  else
    ⟨primalAt inst B s j (roundValue inst B s j),
      Function.update s.y j (roundValue inst B s j)⟩

/-- The state of the scheme after the first `r` rounds (the columns `k : Fin m` with `k < r`, in index
order), starting from `initState`. For `r ≥ m` it is the final state. -/
noncomputable def stateAfter {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) : ℕ → State I m
  | 0 => initState I m
  | r + 1 =>
    if h : r < m then runRound inst B (stateAfter inst B r) ⟨r, h⟩
    else stateAfter inst B r

/-- The value `X` of the primal (covering) solution after `r` rounds: `∑ᵢ c(i) x(i)`. -/
noncomputable def primalValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (r : ℕ) : ℝ :=
  ∑ i, inst.c i * (stateAfter inst B r).x i

/-- The value `Y` of the dual (packing) solution after `r` rounds: `∑_{k < r} y(k)` (the
objective coefficient of every `y(k)` is normalized to `1`, footnote 2, p. 4). -/
noncomputable def dualValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), (stateAfter inst B r).y k

end BNCovPack.Packing


