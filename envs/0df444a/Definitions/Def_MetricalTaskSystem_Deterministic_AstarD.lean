-- Prove2me | Definitions.Def_MetricalTaskSystem_Deterministic_AstarD
-- name    : MetricalTaskSystem_Deterministic_AstarD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:11:07.729511+00:00
-- url     : https://prove2.me/theorems/0de38d29-8e18-449a-8b40-109f9192e771
-- title:
--   The cycle offset ratio $\psi(d)$ and the nearly oblivious algorithm $A^*_d$
-- statement:
--   The **cycle offset ratio** of a (not necessarily symmetric) matrix $d$ is
--   $$\psi(d)=\max_{s_0,s_1,\dots,s_k=s_0}\frac{\sum_{i=1}^k d(s_{i-1},s_i)}{\sum_{i=1}^k d(s_i,s_{i-1})},$$
--   the maximum over closed walks; $\psi(d)=1$ when $d$ is symmetric.
--
--   A **nearly oblivious** algorithm is specified by states $s_0,s_1,s_2,\dots$ ($s_0$ given) and budgets $c_0,c_1,\dots$: it visits $s_1,s_2,\dots$ in this order regardless of the input, and moves from $s_j$ to $s_{j+1}$ at the instant $t_{j+1}$ at which the processing cost incurred since entering $s_j$ reaches $c_j$, i.e. $c_j=\int_{t_j}^{t_{j+1}}T^{\lfloor t\rfloor}(s_j)\,dt$.
--
--   The algorithm **$A^*_d$** is the nearly oblivious algorithm defined together with functions $f_k:S\to\mathbb R$ by $f_0\equiv0$ and, for $k\ge1$,
--   $$s_k\in\operatorname*{arg\,min}_{s\neq s_{k-1}}\big(f_{k-1}(s)+d(s,s_{k-1})\big),\qquad f_k(s)=\begin{cases}f_{k-1}(s)& s\neq s_{k-1},\\ f_{k-1}(s_k)+d(s_k,s_{k-1})& s=s_{k-1},\end{cases}$$
--   with budgets $c_{k-1}=f_k(s_{k-1})-f_{k-1}(s_{k-1})$.
--
--   **Formalization Note** $\psi(d)$ is the supremum of the ratio over closed walks whose reverse length is positive (walks that never move are excluded); for a task system with at least two states this set is nonempty and bounded, and the supremum is attained. The printed rule minimizes over all $s$; it is read, as in the proof of Lemma 6.2 (p. 757) and the requirement $s_{j-1}\neq s_j$ (p. 747), as a minimum over $s\neq s_{k-1}$. Ties are not fixed: `IsAstarSeq d s₀ s` says that $s$ is a state sequence of $A^*_d$ with some tie-breaking. Budgets may be $0$ (an instantaneous transition). The entry times are `Option ℝ` (`none` when the budget is not reached before time $m+1$), and the online cost is a sum over stages in $[0,\infty]$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 747 (cycle offset ratio ψ(d)); pp. 752-753, Section 4 (nearly oblivious algorithms); p. 755, Section 6 (algorithm A*_d)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime

namespace MetricalTaskSystem.Deterministic

/-- The **cycle offset ratio** `ψ(d)` (p. 747): the maximum, over closed walks
`v₀, v₁, …, v_k = v₀`, of `(Σ_{i=1}^k d(v_{i−1}, v_i)) / (Σ_{i=1}^k d(v_i, v_{i−1}))`.
Walks whose reverse length is `0` (walks that never move) are excluded. For a task system
on at least two states the set is nonempty and bounded above, and its supremum is attained
(on simple cycles). -/
noncomputable def cycleOffsetRatio {S : Type} (d : S → S → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (k : ℕ) (v : Fin (k + 1) → S), v 0 = v (Fin.last k) ∧
    0 < ∑ i : Fin k, d (v i.succ) (v i.castSucc) ∧
    r = (∑ i : Fin k, d (v i.castSucc) (v i.succ)) / ∑ i : Fin k, d (v i.succ) (v i.castSucc)}

/-- The functions `f_k : S → ℝ` of the algorithm `A*_d` (p. 755), computed from a state
sequence `s₀, s₁, s₂, …`: `f₀ = 0` and, for `k ≥ 1`,
`f_k(x) = f_{k−1}(x)` if `x ≠ s_{k−1}`, and `f_k(s_{k−1}) = f_{k−1}(s_k) + d(s_k, s_{k−1})`. -/
def fSeq {S : Type} [DecidableEq S] (d : S → S → ℝ) (s : ℕ → S) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun x =>
    if x = s k then fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) else fSeq d s k x

/-- `s` is a state sequence of the algorithm `A*_d` started at `s₀` (p. 755, with the
minimization over states different from `s_{k−1}`, as in the proof of Lemma 6.2, p. 757):
`s 0 = s₀` and, for every `k ≥ 1`, `s_k ≠ s_{k−1}` minimizes `f_{k−1}(x) + d(x, s_{k−1})` over
`x ≠ s_{k−1}`. Ties are broken arbitrarily. -/
def IsAstarSeq {S : Type} [DecidableEq S] (d : S → S → ℝ) (s₀ : S) (s : ℕ → S) : Prop :=
  s 0 = s₀ ∧ ∀ k : ℕ, s (k + 1) ≠ s k ∧
    ∀ x, x ≠ s k → fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) ≤ fSeq d s k x + d x (s k)

/-- The processing budgets of `A*_d` (p. 755): `c_{k−1} = f_k(s_{k−1}) − f_{k−1}(s_{k−1})`,
i.e. `cSeq d s j = f_{j+1}(s_j) − f_j(s_j)`. -/
def cSeq {S : Type} [DecidableEq S] (d : S → S → ℝ) (s : ℕ → S) (j : ℕ) : ℝ :=
  fSeq d s (j + 1) (s j) - fSeq d s j (s j)

open Classical in
/-- For a nearly oblivious algorithm in state `s`, entered at time `t`, with budget `c`
(p. 753): the first time `u ≥ t` at which the processing cost incurred in `s` since `t`
reaches `c`, provided this happens strictly before the end `m + 1` of the task sequence;
`none` otherwise (the algorithm then stays in `s` until the end). -/
noncomputable def nextTime {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (s : S) (c t : ℝ) :
    Option ℝ :=
  if ∃ u : ℝ, t ≤ u ∧ u < (m : ℝ) + 1 ∧ c ≤ proc T s t u then
    some (sInf {u : ℝ | t ≤ u ∧ c ≤ proc T s t u})
  else none

/-- The entry times `t_j` of the nearly oblivious algorithm specified by the states
`s₀ s₁ s₂ ⋯` and budgets `c₀ c₁ c₂ ⋯` on `T¹ ⋯ Tᵐ` (p. 752–753): `t₀ = 1` (the first task
arrives at time 1) and `t_{j+1}` is the time at which the processing cost incurred since
entering `s_j` reaches `c_j`; `none` when that does not happen before time `m + 1`. -/
noncomputable def entryTime {S : Type} (s : ℕ → S) (c : ℕ → ℝ) {m : ℕ} (T : Fin m → S → ℝ) :
    ℕ → Option ℝ
  | 0 => some 1
  | j + 1 => (entryTime s c T j).bind (fun t => nextTime T (s j) (c j) t)

/-- The cost incurred by the nearly oblivious algorithm `(s, c)` in state `s_j`: the processing
cost in `s_j` from `t_j` until the next transition (or until time `m + 1`), plus the transition
cost `d(s_j, s_{j+1})` if the transition to `s_{j+1}` occurs before time `m + 1`; `0` if `s_j`
is never entered. -/
noncomputable def stageCost {S : Type} (d : S → S → ℝ) (s : ℕ → S) (c : ℕ → ℝ) {m : ℕ}
    (T : Fin m → S → ℝ) (j : ℕ) : ENNReal :=
  match entryTime s c T j, entryTime s c T (j + 1) with
  | none, _ => 0
  | some tj, none => ENNReal.ofReal (proc T (s j) tj ((m : ℝ) + 1))
  | some tj, some tj1 => ENNReal.ofReal (proc T (s j) tj tj1 + d (s j) (s (j + 1)))

/-- The total cost (p. 751) of the continuous-time schedule of the nearly oblivious algorithm
`(s, c)` on `T¹ ⋯ Tᵐ`: the sum of all stage costs, in `ℝ≥0∞` (a sum over infinitely many
transitions before time `m + 1` would be `⊤`). -/
noncomputable def noCost {S : Type} (d : S → S → ℝ) (s : ℕ → S) (c : ℕ → ℝ) {m : ℕ}
    (T : Fin m → S → ℝ) : ENNReal :=
  ∑' j : ℕ, stageCost d s c T j

/-- The cost of the algorithm `A*_d` (with the state sequence `s`, satisfying `IsAstarSeq`)
on `T¹ ⋯ Tᵐ`: the nearly oblivious algorithm with states `s` and budgets `cSeq d s`. -/
noncomputable def astarCost {S : Type} [DecidableEq S] (d : S → S → ℝ) (s : ℕ → S) {m : ℕ}
    (T : Fin m → S → ℝ) : ENNReal :=
  noCost d s (cSeq d s) T

end MetricalTaskSystem.Deterministic


