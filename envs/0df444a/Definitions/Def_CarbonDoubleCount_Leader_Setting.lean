-- Prove2me | Definitions.Def_CarbonDoubleCount_Leader_Setting
-- name    : CarbonDoubleCount_Leader_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:18.562512+00:00
-- url     : https://prove2.me/theorems/1af1026e-ae6b-4f5b-97c5-ec72e64b6ccb
-- title:
--   §3, pp. 8–11 and §5, pp. 14–16 — effort boxes, partial derivatives, first best (1), the carbon leader's problems P_E (6)–(8) and P_F (9)–(11), rule (12)
-- statement:
--   This file fixes the model of Caro, Corbett, Tan and Zuidwijk (§3) and the two contracting problems of a **carbon leader** (§5).
--
--   **Firms, actions, processes.** There is a finite set of firms $\mathcal N$, a finite set of carbon abatement actions for each firm $n$ (the page's $\{1,\dots,m_n\}$), and a finite set of processes $\mathcal I$. An effort profile $e=(e_{n,j})$ assigns an effort to every action of every firm. Given a bound $A$, the **effort box** is $[0,A]^M=\{e : 0\le e_{n,j}\le A \text{ for all } n,j\}$, and firm $n$'s own box is $[0,A]^{m_n}$.
--
--   **Data.** Firm $n$ earns profit $V_n(e_n)$, a function of its own effort vector; process $i$ has footprint $f_i(e)$, a function of the whole profile.
--
--   **Partial derivatives.** $\partial F/\partial e_{n,j}$ of a function of the profile is the derivative of the one-variable function obtained by varying the coordinate $e_{n,j}$ alone; $\partial V_n/\partial e_{n,j}$ is defined the same way on firm $n$'s own vector.
--
--   **Social value and first best (1), p. 9.** At carbon price $c$ the social value is
--   $$\Sigma(e;c)=\sum_{n\in\mathcal N}V_n(e_n)-c\sum_{i\in\mathcal I}f_i(e),$$
--   and $e$ is a **first best** at price $c$ if it lies in the effort box and maximizes $\Sigma(\cdot;c)$ over the box.
--
--   **The carbon leader.** One firm $N$ (written $L$ in Lean) pays for all supply-chain emissions at carbon price $p$ and compensates the other firms; firm $n$ has reservation profit $\bar\pi_n$.
--
--   1. **Problem $P_E$ (contracting on efforts), (6)–(8), p. 15.** The leader chooses payments $g_n(e_n)$, functions of firm $n$'s own effort, and the efforts. Its objective is
--   $$V_N(e_N)-p\sum_{i}f_i(e)+\sum_{n\ne N}g_n(e_n). \qquad (6)$$
--   A pair $(g,e)$ is feasible if $e$ lies in the effort box and, for every $n\neq N$, the participation constraint $V_n(e_n)-g_n(e_n)\ge\bar\pi_n$ (7) holds and $e_n$ maximizes $V_n(x)-g_n(x)$ over firm $n$'s box (8). It is **optimal** if it is feasible and its objective is at least that of every feasible pair.
--   2. **Problem $P_F$ (contracting on emissions), (9)–(11), p. 15.** Now the payments $g_n(f)$ are functions of the footprint vector. The objective is
--   $$V_N(e_N)-p\sum_{i}f_i(e)+\sum_{n\ne N}g_n(f(e)), \qquad (9)$$
--   and $(g,e)$ is feasible if $e$ lies in the box, $V_n(e_n)-g_n(f(e))\ge\bar\pi_n$ (10), and $e_n$ maximizes $V_n(x)-g_n(f(e_{-n},x))$ over firm $n$'s box (11), every other firm's effort (the leader's included) held fixed.
--   3. **Rule (12), p. 16.** For an influence matrix $B=(b_{n,i})$ and efforts $e^E$ with emissions $f^E=f(e^E)$,
--   $$g_n(f)=p\sum_{i\in\mathcal I}b_{n,i}f_i+k_n,\qquad k_n=V_n(e^E_n)-p\sum_{i\in\mathcal I}b_{n,i}f^E_i-\bar\pi_n.$$
--
--   These objects carry the whole of §5: Proposition 5 compares the two problems, and Lemma 6 compares $P_E$ with the first best.
--
--   **Formalization Note.** Firms, actions and processes are finite types rather than index ranges. "Optimal" is "feasible and at least every feasible value", not a supremum, so the optimal value of $P_E$ is the objective at an optimal pair. In $P_E$ and $P_F$ the followers' efforts are chosen together with the payments, subject to (8) or (11); this is the page's "we assume that it will choose the level determined by the carbon leader". The sign condition $g_n\le 0$ stated on p. 14 is not imposed. The standing assumptions of §3.1 (differentiability, concavity, monotonicity, non-negativity) are hypotheses of the theorems, not part of these definitions.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, pp. 8–9 (§3.1, §3.2, eq. (1)), p. 10 (reservation profits), pp. 14–16 (§5, P_E eqs. (6)–(8), P_F eqs. (9)–(11), rule (12))

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

namespace CarbonDoubleCount.Leader

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The partial derivative `∂F/∂e_{n,j}` of a function of the whole effort profile, taken as
the one-variable derivative along the coordinate `(n, j)`. -/
noncomputable def dEff (F : ((n : ι) → act n → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) (n : ι)
    (j : act n) : ℝ :=
  deriv (fun t => F (Function.update e n (Function.update (e n) j t))) (e n j)

/-- The partial derivative `∂W/∂e_{n,j}` of a function of firm `n`'s own effort vector. -/
noncomputable def dOwn {n : ι} (W : (act n → ℝ) → ℝ) (x : act n → ℝ) (j : act n) : ℝ :=
  deriv (fun t => W (Function.update x j t)) (x j)

/-- The social value of the supply chain at carbon price `c` (§3.2, p. 9):
`Σ_n V_n(e_n) − c Σ_i f_i(e)`. -/
def socialValue (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ) (c : ℝ)
    (e : (n : ι) → act n → ℝ) : ℝ :=
  ∑ n, V n (e n) - c * ∑ i, f e i

/-- `e` solves the first-best problem (1) at carbon price `c` (p. 9): `e` lies in the effort box
and attains the maximum of the social value over the box. -/
def IsFirstBest (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (c : ℝ) (e : (n : ι) → act n → ℝ) : Prop :=
  e ∈ CarbonDoubleCount.Planner.effortBox A ∧ ∀ e' ∈ CarbonDoubleCount.Planner.effortBox A, socialValue V f c e' ≤ socialValue V f c e

/-- The carbon leader's objective (6) of problem `P_E` (p. 15), with the leader `L` (the page's
`N`) and effort-contingent payments `g n : (act n → ℝ) → ℝ` of the firms `n ≠ L`:
`V_L(e_L) − p Σ_i f_i(e) + Σ_{n ≠ L} g_n(e_n)`. -/
def peObjective (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ) (p : ℝ)
    (L : ι) (g : (n : ι) → (act n → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) : ℝ :=
  V L (e L) - p * ∑ i, f e i + ∑ n ∈ univ.erase L, g n (e n)

/-- Feasibility for `P_E` (p. 15): `e` lies in the effort box, every firm `n ≠ L` meets its
participation constraint (7), and every firm `n ≠ L` has `e_n` in its arg max (8) over its own
box. -/
def PEFeasible (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ) (L : ι) (πbar : ι → ℝ)
    (g : (n : ι) → (act n → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) : Prop :=
  e ∈ CarbonDoubleCount.Planner.effortBox A ∧
    (∀ n, n ≠ L → πbar n ≤ V n (e n) - g n (e n)) ∧
    (∀ n, n ≠ L → ∀ x ∈ CarbonDoubleCount.Planner.firmBox A n, V n x - g n x ≤ V n (e n) - g n (e n))

/-- `(g, e)` is an optimal solution of `P_E`: feasible, with objective (6) at least that of every
feasible pair. -/
def IsOptimalPE (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (p : ℝ) (L : ι) (πbar : ι → ℝ) (g : (n : ι) → (act n → ℝ) → ℝ)
    (e : (n : ι) → act n → ℝ) : Prop :=
  PEFeasible A V L πbar g e ∧
    ∀ (g' : (n : ι) → (act n → ℝ) → ℝ) (e' : (n : ι) → act n → ℝ),
      PEFeasible A V L πbar g' e' → peObjective V f p L g' e' ≤ peObjective V f p L g e

/-- The carbon leader's objective (9) of problem `P_F` (p. 15), with emission-contingent payments
`g n : (κ → ℝ) → ℝ`: `V_L(e_L) − p Σ_i f_i(e) + Σ_{n ≠ L} g_n(f(e))`. -/
def pfObjective (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ) (p : ℝ)
    (L : ι) (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) : ℝ :=
  V L (e L) - p * ∑ i, f e i + ∑ n ∈ univ.erase L, g n (f e)

/-- Feasibility for `P_F` (p. 15): `e` lies in the effort box, every firm `n ≠ L` meets the
participation constraint (10), and every firm `n ≠ L` has `e_n` in its arg max (11) over its own
box, a unilateral deviation `x` changing the footprint to `f(e with e_n := x)` while every other
firm's effort, the leader's included, stays fixed. -/
def PFFeasible (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (L : ι) (πbar : ι → ℝ) (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) : Prop :=
  e ∈ CarbonDoubleCount.Planner.effortBox A ∧
    (∀ n, n ≠ L → πbar n ≤ V n (e n) - g n (f e)) ∧
    (∀ n, n ≠ L → ∀ x ∈ CarbonDoubleCount.Planner.firmBox A n,
      V n x - g n (f (Function.update e n x)) ≤ V n (e n) - g n (f e))

/-- The linear payment rule (12) of Proposition 5 (p. 16), built from the efforts `eE` and the
emissions `f^E = f(eE)`:
`g_n(φ) = p Σ_i b_{n,i} φ_i + k_n` with `k_n = V_n(eE_n) − p Σ_i b_{n,i} f_i(eE) − π̄_n`. -/
def rule12 (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ) (p : ℝ)
    (B : ι → κ → ℝ) (πbar : ι → ℝ) (eE : (n : ι) → act n → ℝ) (n : ι) (φ : κ → ℝ) : ℝ :=
  p * ∑ i, B n i * φ i + (V n (eE n) - p * ∑ i, B n i * f eE i - πbar n)

end CarbonDoubleCount.Leader


