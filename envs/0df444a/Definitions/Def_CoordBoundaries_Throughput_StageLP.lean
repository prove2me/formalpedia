-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_StageLP
-- name    : CoordBoundaries_Throughput_StageLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:26.094224+00:00
-- url     : https://prove2.me/theorems/f6a7e849-b3be-471e-bb2e-7455dcef033a
-- title:
--   Configuration copies, tracked sets and the penalized stage LPs of the pseudopolynomial implementation
-- statement:
--   Fix a candidate $(\mathcal B,\mathcal S,K)$, $\eta=1/q$ and $\Delta$. The stage variables are common placement marginals $y=(y_{j,B})$ subject to $y_j\le1$ and both density constraints, together with **configuration copies** $x^{[0]},\dots,x^{[i]}$, each a family of distributions on $\mathcal C(B)$ with marginals exactly $y$. Copy $x^{[k]}$, $k\ge1$, is linked to projected consistent distributions on the tracked sets
--   $$H^{k-1}_B=\{j\text{ global}: B\in\{B_L(j),B_R(j)\},\ y^{k-1}_{j,B}\ge 1/8\}$$
--   of the previous stage's solution. $P_i$ is the set of marginals $y$ that extend to a feasible solution of all stage-$i$ constraints.
--
--   With $d_y=n|\mathcal B|$, $\beta=\eta$, $\gamma=\eta/100$ and $h=\lceil4d_y/\gamma\rceil$,
--   $$\phi(t)=\max_{\ell=0,\dots,h}\Big(2\frac{\ell}{h}t-\Big(\frac{\ell}{h}\Big)^2\Big),\qquad \hat\Phi(y)=F-\beta\sum_{j,B}\phi(y_{j,B}).$$
--   A **run** of the procedure chooses at every stage $i$ a maximizer $y^i$ of $\hat\Phi$ over $P_i$ (ties broken arbitrarily); the **stopping test** is $\|y^{i+1}-y^i\|_2^2\le\gamma F_{i+1}$.
--
--   **Formalization Note** Since the copies are linked to each other only through $y$, $P_i$ is the set of $y$ satisfying the base constraints and admitting, for each tracked-set family used so far, one copy with consistent projected distributions.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 21–23, §4.2 (copies, tracked sets, P_i), §4.3 (φ, Φ̂, stopping test)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Relaxation

open Classical

namespace CoordBoundaries.Throughput

/-! # Configuration copies and the penalized stage LPs (Tong–Xu, §4.2–§4.3, pp. 21–24)

For one candidate `(ℬ, 𝒮, K)` the variables of stage `i` are the common placement marginals
`y = (y_{j,B})`, configuration copies `x^{[0]}, …, x^{[i]}` that all have marginals `y`, and for
every `k = 1, …, i` projected consistent distributions on the tracked sets `H^{k−1}`, linked only to
copy `k`. The job and density constraints are imposed on `y`. Since the copies are linked only
through `y`, the stage-`i` feasible marginal set `P_i` is the set of `y` satisfying the base
constraints and admitting, for each tracked-set family used so far, one copy with consistent
projected distributions. -/

/-- A vector of placement marginals `y = (y_{j,B})`. -/
abbrev Marg (I : Instance) (P : Partition I.T) := Fin I.n → Fin P.len → ℝ

/-- `γ = η/100` (p. 22). -/
noncomputable def gammaP (q : ℕ) : ℝ := eta q / 100

namespace Partition

variable {I : Instance} (P : Partition I.T)

/-- `x` is a configuration copy representing `y` (p. 21): distributions on `𝒞(B)` with
`Σ_{C ∋ j} x_{B,C} = y_{j,B}`. -/
def IsCopy (K : ℕ) (y : Marg I P) (x : Fin P.len → Finset (Fin I.n) → ℝ) : Prop :=
  (∀ k C, 0 ≤ x k C) ∧ (∀ k C, C ∉ P.configs K k → x k C = 0) ∧
    (∀ k, ∑ C ∈ P.configs K k, x k C = 1) ∧
    ∀ j k, ∑ C ∈ (P.configs K k).filter (fun C => j ∈ C), x k C = y j k

/-- `F = Σ_{j,B} y_{j,B}`. -/
def margF (y : Marg I P) : ℝ := ∑ j, ∑ k, y j k

/-- The job constraints `y_j ≤ 1` and both density constraints, on the common marginals. -/
def BaseOK (K Δ q : ℕ) (y : Marg I P) : Prop :=
  (∀ j, ∑ k, y j k ≤ 1) ∧ (I.m : ℝ) * Δ * P.len / eta q ≤ P.margF y ∧
    (K : ℝ) * P.numSuper / eta q ^ 8 ≤ P.margF y

/-- `p_B^{[k]}(A) = Σ_{C ∩ H_B = A} x^{[k]}_{B,C}` (p. 22). -/
noncomputable def stateMassOf (K : ℕ) (x : Fin P.len → Finset (Fin I.n) → ℝ)
    (H : Fin P.len → Finset (Fin I.n)) (B : Fin P.len) (A : Finset (Fin I.n)) : ℝ :=
  ∑ C ∈ (P.configs K B).filter (fun C => C ∩ H B = A), x B C

/-- The feasible marginal set `P_i` after the tracked-set families `Hs = [H^0, …, H^{i−1}]`. -/
def StageSet (K Δ q : ℕ) (Hs : List (Fin P.len → Finset (Fin I.n))) : Set (Marg I P) :=
  {y | P.BaseOK K Δ q y ∧ (∃ x, P.IsCopy K y x) ∧
    ∀ H ∈ Hs, ∃ x, P.IsCopy K y x ∧
      ∃ π, Consistent (fun B => (H B).powerset) (P.stateMassOf K x H) π}

/-- Tracked sets `H^i_B = {j global : B ∈ {B_L(j), B_R(j)}, y^i_{j,B} ≥ 1/8}` (p. 21). -/
noncomputable def tracked (y : Marg I P) : Fin P.len → Finset (Fin I.n) := fun B =>
  Finset.univ.filter fun j =>
    P.IsGlobal j ∧ ((B : ℕ) = P.BL j ∨ (B : ℕ) = P.BR j) ∧ (1 : ℝ) / 8 ≤ y j B

/-- `d_y = n|ℬ|`. -/
def dy : ℕ := I.n * P.len

/-- `h = ⌈4 d_y / γ⌉`. -/
noncomputable def hGrid (q : ℕ) : ℕ := ⌈4 * (P.dy : ℝ) / gammaP q⌉₊

/-- `Φ̂(y) = F − β Σ_{j,B} φ(y_{j,B})` with `β = η` (p. 22). -/
noncomputable def PhiHat (q : ℕ) (y : Marg I P) : ℝ :=
  P.margF y - eta q * ∑ j, ∑ k,
    (Finset.range (P.hGrid q + 1)).sup' Finset.nonempty_range_add_one
      (fun ℓ => 2 * ((ℓ : ℝ) / P.hGrid q) * y j k - ((ℓ : ℝ) / P.hGrid q) ^ 2)

/-- `‖y′ − y‖₂² = Σ_{j,B} (y′_{j,B} − y_{j,B})²`. -/
def sqDist (y y' : Marg I P) : ℝ := ∑ j, ∑ k, (y' j k - y j k) ^ 2

/-- A run of the projected procedure through stage `M` (p. 23): for every `i ≤ M`, `y^i` is a
maximizer of `Φ̂` over `P_i`, where `P_i` uses the tracked sets of `y^0, …, y^{i−1}`; ties between
optimal solutions are broken arbitrarily. -/
def IsRun (K Δ q : ℕ) (y : ℕ → Marg I P) (M : ℕ) : Prop :=
  ∀ i ≤ M,
    y i ∈ P.StageSet K Δ q ((List.range i).map fun k => P.tracked (y k)) ∧
      ∀ y' ∈ P.StageSet K Δ q ((List.range i).map fun k => P.tracked (y k)),
        P.PhiHat q y' ≤ P.PhiHat q (y i)

end Partition

end CoordBoundaries.Throughput


