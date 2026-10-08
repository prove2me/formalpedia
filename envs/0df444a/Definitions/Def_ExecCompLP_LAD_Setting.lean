-- Prove2me | Definitions.Def_ExecCompLP_LAD_Setting
-- name    : ExecCompLP_LAD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:08:04.636995+00:00
-- url     : https://prove2.me/theorems/ffc50dd2-e12f-42e8-a190-d616c8336bd3
-- title:
--   §§4–5 and Table I — ranked salary constraints and the absolute-deviation linear program
-- statement:
--   For factor ratings $x_{ik}$, nonnegative weights $a_i$, and ranked job levels $k=1,\ldots,L$, define the estimated salary at level $k$ by
--
--   $$S_k(a)=\sum_{i=1}^n a_i x_{ik}.$$
--
--   The feasible weights satisfy $a_i\ge 0$, $S_1(a)\le s_M$, $S_{k+1}(a)\le S_k(a)$ for adjacent levels, and $s_m\le S_L(a)$. If $K$ is the set of levels with specified salary targets $s_k$, the original objective is $D(a)=\sum_{k\in K}|S_k(a)-s_k|$. The linear program adds nonnegative variables $u_k,v_k$ for $k\in K$, requires $S_k(a)-s_k=u_k-v_k$, and minimizes $P(u,v)=\sum_{k\in K}(u_k+v_k)$. A minimizer is a feasible point whose objective is no larger than that of any other feasible point.
--
--   Table I is recorded as nine factor-rating columns at seven ranked levels. Its specified target levels are $R_1,R_5,R_7$, with targets 16, 10, 4 in thousands of dollars. The vector $a^*$ records the coefficients of equation (7).
--
--   These definitions provide the exact two optimization problems compared by the main theorem and the numerical data for the paper's worked example.
--
--   **Formalization Note** Levels start at Lean index 0, so the first and last levels have indices 0 and $L-1$. The finite set $K$ may be empty; then both objectives are zero and the same feasible weights minimize each. Intermediate targets enter $D$ and $P$, without adding constraints beyond (2).
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), pp. 140–141, §§4–5, equations (1)–(5); p. 145, Table I; p. 148, equation (7); https://doi.org/10.1287/mnsc.1.2.138

import Mathlib

namespace ExecCompLP.LAD

variable {n L : ℕ} [NeZero L]

/-- The final ranked job level. -/
def lastLevel : Fin L := Fin.ofNat L (L - 1)

/-- Salary at ranked level `k`, in the units used for the factor ratings. -/
def salary (x : Fin n → Fin L → ℝ) (a : Fin n → ℝ) (k : Fin L) : ℝ :=
  ∑ i, a i * x i k

/-- The nonnegative weights, ceiling, descending rankings and floor in (2). -/
def Feasible (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (a : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧
  salary x a 0 ≤ sM ∧
  (∀ k : Fin L, ∀ h : k.val + 1 < L,
    salary x a ⟨k.val + 1, h⟩ ≤ salary x a k) ∧
  sm ≤ salary x a lastLevel

/-- The sum of absolute deviations from the specified salary levels in (3). -/
def obj (x : Fin n → Fin L → ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ k ∈ K, |salary x a k - s k|

/-- The feasible set after splitting deviations into two nonnegative variables, (4)–(5). -/
def LPFeasible (x : Fin n → Fin L → ℝ) (sM sm : ℝ)
    (K : Finset (Fin L)) (s : Fin L → ℝ)
    (a : Fin n → ℝ) (u v : Fin L → ℝ) : Prop :=
  Feasible x sM sm a ∧
  ∀ k ∈ K, 0 ≤ u k ∧ 0 ≤ v k ∧ salary x a k - s k = u k - v k

/-- The linear objective of the split-variable problem. -/
def lpObj (K : Finset (Fin L)) (u v : Fin L → ℝ) : ℝ :=
  ∑ k ∈ K, (u k + v k)

/-- A feasible least-absolute-deviation minimizer. -/
def IsMinimizer (x : Fin n → Fin L → ℝ) (sM sm : ℝ)
    (K : Finset (Fin L)) (s : Fin L → ℝ) (a : Fin n → ℝ) : Prop :=
  Feasible x sM sm a ∧
  ∀ a' : Fin n → ℝ, Feasible x sM sm a' → obj x K s a ≤ obj x K s a'

/-- A feasible minimizer of the linear program in split variables. -/
def IsLPMinimizer (x : Fin n → Fin L → ℝ) (sM sm : ℝ)
    (K : Finset (Fin L)) (s : Fin L → ℝ)
    (a : Fin n → ℝ) (u v : Fin L → ℝ) : Prop :=
  LPFeasible x sM sm K s a u v ∧
  ∀ (a' : Fin n → ℝ) (u' v' : Fin L → ℝ),
    LPFeasible x sM sm K s a' u' v' → lpObj K u v ≤ lpObj K u' v'

/-- Positive part of an unrestricted deviation. -/
def posPart (w : ℝ) : ℝ := max w 0

/-- Negative part of an unrestricted deviation. -/
def negPart (w : ℝ) : ℝ := max (-w) 0

/-- Table I factor ratings: factor index first, ranked job level second. -/
def tableI : Fin 9 → Fin 7 → ℝ :=
  ![![3, 3, 2, 0, 1, 0, 0],
    ![4, 4, 3, 2, 3, 2, 2],
    ![4, 3, 2, 2, 1, 1, 1],
    ![4, 3, 2, 2, 3, 2, 1],
    ![4, 1, 1, 0, 1, 1, 0],
    ![4, 0, 0, 2, 4, 0, 0],
    ![5, 3, 2, 2, 2, 2, 1],
    ![3, 2, 2, 2, 1, 2, 1],
    ![4, 3, 3, 2, 2, 2, 2]]

/-- The ceiling, R5 and floor are the specified target levels. -/
def K7 : Finset (Fin 7) := {0, 4, 6}

/-- Target salaries in thousands of dollars; values outside `K7` are unused. -/
def s7 (k : Fin 7) : ℝ :=
  if k = 0 then 16 else if k = 4 then 10 else if k = 6 then 4 else 0

/-- The weight vector reported in equation (7). -/
noncomputable def aStar : Fin 9 → ℝ :=
  ![(4:ℝ)/11, 0, 0, (16:ℝ)/11, 0, (4:ℝ)/11, 0, (28:ℝ)/11, 0]

end ExecCompLP.LAD


