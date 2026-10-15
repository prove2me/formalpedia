-- Prove2me | Definitions.Def_HiringLP_SimLower_LP
-- name    : HiringLP_SimLower_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:41.619541+00:00
-- url     : https://prove2.me/theorems/a2366603-6884-4f2a-9b4e-0e71fd77d110
-- title:
--   §6.2, p. 27 and Lemma 12, p. 28 — the LP relaxation LP_sim, its optimal solutions, V_high, P_high, P_total
-- statement:
--   Let $I=(k,n,p,v)$ be a Simultaneous Offering instance. The linear programming relaxation $\mathrm{LP}_{\mathrm{sim}}(I)$ is
--   $$\mathrm{LP}_{\mathrm{sim}}(I)=\max_{y,z}\ \sum_{i\in[n]}v_ip_iy_i+z\quad\text{s.t.}\quad z\le k-\sum_{i\in[n]}p_iy_i,\quad z\le 0,\quad 0\le y_i\le 1\ \ (i\in[n]).$$
--   A pair $(y,z)$ satisfying the constraints is *feasible*; it is *optimal* when its objective is at least that of every feasible pair. $\mathrm{LP}_{\mathrm{sim}}(I)$ denotes the optimal value, the supremum of the objective over feasible pairs. The *total mass* of $y$ is $\sum_i y_ip_i$.
--
--   Further, $V_{\mathrm{high}}=\{i\in[n]: v_i>1\}$ is the set of candidates worth hiring even over capacity, $P_{\mathrm{high}}=\sum_{i\in V_{\mathrm{high}}}p_i$ and $P_{\mathrm{total}}=\sum_{i\in[n]}p_i$.
--
--   Finally, $y$ has the *prefix structure at index $j$* (the structure of Lemma 11) when $y_i=1$ for $i<j$, $y_j>0$ and $y_i=0$ for $i>j$.
--
--   The LP is the benchmark against which the algorithm of the mission is measured, and Lemmas 10–12 describe its value and its optimal solutions.
--
--   **Formalization Note** Indices are 0-based (`Fin n`), so the paper's "$y_i=1$ for $1\le i\le j-1$, $y_j>0$, $y_i=0$ for $j+1\le i\le n$" reads $y_i=1$ for $i<j$ etc. `LPsim` is the real `sSup` of the objective over the feasible set; the set is nonempty ($y=0$, $z=0$) and bounded above by $\sum_i v_ip_i$ for a valid instance, so it is the LP value, and it equals the objective at any optimal pair.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 27, §6.2 (LP_sim); p. 26 (V_high); p. 28, Lemma 12 (P_high, P_total); p. 27, Lemma 11 (prefix structure)

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model

open Finset

namespace HiringLP.SimLower

/-- Feasibility in `LP_sim(I)` (p. 27): `z ≤ k − Σᵢ pᵢyᵢ`, `z ≤ 0`, `0 ≤ yᵢ ≤ 1`. -/
def LPFeasible {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) (z : ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ z ≤ 0 ∧ z ≤ (I.k : ℝ) - ∑ i, I.p i * y i

/-- The objective of `LP_sim(I)` (p. 27): `Σᵢ vᵢpᵢyᵢ + z`. -/
def LPobj {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ i, I.v i * I.p i * y i + z

/-- `(y, z)` is an optimal solution of `LP_sim(I)`. -/
def IsLPOpt {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) (z : ℝ) : Prop :=
  LPFeasible I y z ∧ ∀ y' z', LPFeasible I y' z' → LPobj I y' z' ≤ LPobj I y z

/-- The optimal value `LP_sim(I)` (p. 27), the supremum of the objective over feasible points. -/
noncomputable def LPsim {n : ℕ} (I : SimInstance n) : ℝ :=
  sSup {x | ∃ y z, LPFeasible I y z ∧ x = LPobj I y z}

/-- `V_high = {i ∈ [n] : vᵢ > 1}` (p. 26). -/
noncomputable def Vhigh {n : ℕ} (I : SimInstance n) : Finset (Fin n) :=
  univ.filter (fun i => 1 < I.v i)

/-- `P_high = Σ_{i ∈ V_high} pᵢ` (p. 28). -/
noncomputable def Phigh {n : ℕ} (I : SimInstance n) : ℝ :=
  ∑ i ∈ Vhigh I, I.p i

/-- `P_total = Σ_{i ∈ [n]} pᵢ` (p. 28). -/
def Ptotal {n : ℕ} (I : SimInstance n) : ℝ :=
  ∑ i, I.p i

/-- The structure of Lemma 11 (p. 27), with 0-based index `j`: `yᵢ = 1` for `i < j`, `y_j > 0`, and
`yᵢ = 0` for `i > j`. -/
def IsPrefix {n : ℕ} (y : Fin n → ℝ) (j : Fin n) : Prop :=
  (∀ i, i < j → y i = 1) ∧ 0 < y j ∧ ∀ i, j < i → y i = 0

end HiringLP.SimLower


