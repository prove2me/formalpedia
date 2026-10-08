-- Prove2me | Definitions.Def_StochSchedPrec_InForest_LP
-- name    : StochSchedPrec_InForest_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:16.709765+00:00
-- url     : https://prove2.me/theorems/976c789c-f368-4e13-bb9b-7f307bdcdde9
-- title:
--   (3.1) and §3, pp. 796–797 — the set function f(W), the LP-relaxation, priority lists, B_j and A_j
-- statement:
--   Let $\mu_j=\mathrm E[P_j]$ be the expected processing times of the jobs $j\in V$, $m\ge 1$ the number of machines and $\Delta\ge 0$ a common bound on the squared coefficients of variation. The set function $f:2^V\to\mathbb R$ of (3.1) is
--   $$f(W)=\frac{1}{2m}\Big(\Big(\sum_{j\in W}\mu_j\Big)^2+\sum_{j\in W}\mu_j^2\Big)-\frac{(m-1)(\Delta-1)}{2m}\sum_{j\in W}\mu_j^2,\qquad W\subseteq V .$$
--
--   **The LP-relaxation** (§3, p. 797) with weights $w_j$ is
--   $$\text{minimize}\ \sum_{j\in V}w_jC^{\mathrm{LP}}_j\quad\text{s.t.}\quad \sum_{j\in W}\mu_jC^{\mathrm{LP}}_j\ge f(W)\ (W\subseteq V),\qquad C^{\mathrm{LP}}_j\ge C^{\mathrm{LP}}_i+\mu_j\ ((i,j)\in A),\qquad C^{\mathrm{LP}}_j\ge\mu_j\ (j\in V).$$
--   A vector satisfying the three families of constraints is *LP-feasible*; it is *LP-optimal* if in addition its objective value is at most that of every LP-feasible vector.
--
--   **Priority lists.** A priority list is a bijection $L$ from the positions $1,\dots,n$ to the jobs. It is *sorted by* a vector $C$ if $C$ is nondecreasing along the list ("a priority list according to $C^{\mathrm{LP}}$", p. 798), and it is a *linear extension* of the precedence constraints if every predecessor of a job comes earlier in the list. For a job $j$, $B_j$ is the set of jobs that come before $j$ in $L$, including $j$, and $A_j$ is the set of jobs that come after $j$ (p. 793).
--
--   These are the LP data and list notation used by Lemma 3.3, Lemmas 4.3–4.4 and Theorem 4.5.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 796 (3.1), p. 797 (LP-relaxation), p. 793 (B_j, A_j), p. 798 (list according to C^LP)

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model

namespace StochSchedPrec.InForest

variable {V : Type*}

/-- The set function `f : 2^V → ℝ` of (3.1), p. 796, with `μ j = E[P_j]`:
`f(W) = 1/(2m) ((∑_{j∈W} μ_j)^2 + ∑_{j∈W} μ_j^2) − (m−1)(Δ−1)/(2m) ∑_{j∈W} μ_j^2`. -/
noncomputable def f (μ : V → ℝ) (m : ℕ) (Δ : ℝ) (W : Finset V) : ℝ :=
  1 / (2 * (m : ℝ)) * ((∑ j ∈ W, μ j) ^ 2 + ∑ j ∈ W, μ j ^ 2)
    - ((m : ℝ) - 1) * (Δ - 1) / (2 * (m : ℝ)) * ∑ j ∈ W, μ j ^ 2

/-- `C` is feasible for the LP-relaxation of §3, p. 797:
the load inequalities `∑_{j∈W} μ_j C_j ≥ f(W)` for all `W ⊆ V`,
`C_j ≥ C_i + μ_j` for every arc `(i, j)`, and `C_j ≥ μ_j` for every job. -/
def IsLPFeasible (μ : V → ℝ) (A : V → V → Prop) (m : ℕ) (Δ : ℝ) (C : V → ℝ) : Prop :=
  (∀ W : Finset V, f μ m Δ W ≤ ∑ j ∈ W, μ j * C j) ∧
  (∀ i j, A i j → C i + μ j ≤ C j) ∧
  (∀ j, μ j ≤ C j)

/-- `C` is an optimal solution of the LP-relaxation of §3, p. 797, with objective
`∑_j w_j C_j` (minimized). -/
def IsLPOptimal [Fintype V] (μ : V → ℝ) (A : V → V → Prop) (m : ℕ) (Δ : ℝ) (w C : V → ℝ) :
    Prop :=
  IsLPFeasible μ A m Δ C ∧
    ∀ C' : V → ℝ, IsLPFeasible μ A m Δ C' → ∑ j, w j * C j ≤ ∑ j, w j * C' j

/-- `B_j` (p. 793): the jobs that come before `j` in the priority list `L`, including `j`. -/
def Bset [Fintype V] (L : Fin (Fintype.card V) ≃ V) (j : V) : Finset V :=
  Finset.univ.filter fun i => L.symm i ≤ L.symm j

/-- `A_j` (p. 793): the jobs that come after `j` in the priority list `L`. -/
def Aset [Fintype V] (L : Fin (Fintype.card V) ≃ V) (j : V) : Finset V :=
  Finset.univ.filter fun i => L.symm j < L.symm i

end StochSchedPrec.InForest


