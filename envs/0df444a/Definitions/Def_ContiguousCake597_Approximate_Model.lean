-- Prove2me | Definitions.Def_ContiguousCake597_Approximate_Model
-- name    : ContiguousCake597_Approximate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:35.326816+00:00
-- url     : https://prove2.me/theorems/4f921ed4-983b-4b47-adf1-59117613504d
-- title:
--   Explicit cake inputs and complete allocations with arbitrary assignment
-- statement:
--   A finite rational step density is a strictly increasing list of rational knots starting at 0 and ending at 1, together with one nonnegative rational level for each intervening interval. Redundant knots with equal neighboring levels are allowed and do not count as genuine breakpoints. For endpoints $a\le b$, its value is
--   $$V([a,b])=\sum_k r_k\max\{0,\min(b,x_{k+1})-\max(a,x_k)\}.$$
--   This is the interval integral of the represented step density; density values use left-closed, right-open intervals and the final level at 1. An input has $n\ge1$ agents, each with such a density and total value $V_i([0,1])=1$. General inputs allow zero levels and any finite number of breakpoints. The restricted class has one positive rational $\lambda$ shared by all agents, every density level in $\{\lambda,2\lambda\}$, and at most six genuine internal breakpoints per agent.
--
--   A complete allocation of $[0,\Lambda]$ consists of $n+1$ nondecreasing cuts from 0 to $\Lambda$ and a permutation $\sigma$ sending agents to spatial pieces $P_j=[\theta_{j-1},\theta_j]$. Empty pieces are allowed. It is $e$-envy-free precisely when
--   $$V_i(P_{\sigma(i)})\ge V_i(P_j)-e\quad\text{for every }i,j.$$
--   Computational answers have rational cuts; realization embeds them into the real-cut model used by the analytic lemmas. Normalization, input validity and envy-freeness are independent predicates, with no assumed existence or complexity classification.
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 3 (PDF 4), §2.1, continuing p.4 (PDF 5)

import Mathlib

namespace ContiguousCake597.Approximate

/-- §2.1, printed pp.3–4 (PDF 4–5). Endpoints are included in `knots`.
Validity is separate, so parsing does not presuppose normalization. -/
structure StepDensity where
  knots : List ℚ
  levels : List ℚ
  deriving DecidableEq

def StepDensity.WellFormed (d : StepDensity) : Prop :=
  d.knots.length = d.levels.length + 1 ∧
  d.knots.head? = some 0 ∧ d.knots.getLast? = some 1 ∧
  d.knots.Pairwise (· < ·) ∧ ∀ r ∈ d.levels, 0 ≤ r

/-- Exact finite sum of density times interval-overlap length. -/
noncomputable def StepDensity.value (d : StepDensity) (a b : ℝ) : ℝ :=
  ((List.range d.levels.length).map fun k =>
    ((d.levels[k]?.getD 0 : ℚ) : ℝ) *
      max 0 (min b ((d.knots[k+1]?.getD 0 : ℚ) : ℝ) - max a ((d.knots[k]?.getD 0 : ℚ) : ℝ))).sum

/-- Half-open intervals, and the final level at the right endpoint. -/
noncomputable def StepDensity.density (d : StepDensity) (t : ℝ) : ℝ :=
  if t = 1 then ((d.levels.getLast?.getD 0 : ℚ) : ℝ) else
    ((List.range d.levels.length).map fun k =>
      if ((d.knots[k]?.getD 0 : ℚ) : ℝ) ≤ t ∧ t < ((d.knots[k+1]?.getD 0 : ℚ) : ℝ)
      then ((d.levels[k]?.getD 0 : ℚ) : ℝ) else 0).sum

/-- Redundant knots with equal adjacent levels are not genuine breakpoints. -/
def StepDensity.breakCount (d : StepDensity) : ℕ :=
  ((Finset.Ico 1 d.levels.length).filter fun k =>
    d.levels[k-1]?.getD 0 ≠ d.levels[k]?.getD 0).card

structure CakeData where
  n : ℕ
  densities : Fin n → StepDensity

def CakeData.Valid (D : CakeData) : Prop :=
  1 ≤ D.n ∧ ∀ i, (D.densities i).WellFormed ∧ (D.densities i).value 0 1 = 1

def CakeData.Restricted (D : CakeData) : Prop :=
  ∃ lam : ℚ, 0 < lam ∧ ∀ i,
    (∀ r ∈ (D.densities i).levels, r = lam ∨ r = 2 * lam) ∧
    (D.densities i).breakCount ≤ 6

/-- A permutation sends an agent to its spatial piece. -/
structure Allocation (K : Type) (n : ℕ) where
  cuts : Fin (n+1) → K
  assign : Equiv.Perm (Fin n)

def Allocation.Complete {n : ℕ} (T : Allocation ℝ n) (L : ℝ) : Prop :=
  T.cuts 0 = 0 ∧ T.cuts ⟨n, Nat.lt_succ_self n⟩ = L ∧ Monotone T.cuts

def Allocation.piece {n : ℕ} (T : Allocation ℝ n) (j : Fin n) : Set ℝ :=
  Set.Icc (T.cuts j.castSucc) (T.cuts j.succ)

noncomputable def Allocation.length {n : ℕ} (T : Allocation ℝ n) (j : Fin n) : ℝ :=
  T.cuts j.succ - T.cuts j.castSucc

noncomputable def Allocation.realize {n : ℕ} (T : Allocation ℚ n) : Allocation ℝ n :=
  ⟨fun j => (T.cuts j : ℝ), T.assign⟩

def EnvyFree {n : ℕ} (V : Fin n → ℝ → ℝ → ℝ) (e : ℝ)
    (T : Allocation ℝ n) : Prop :=
  ∀ (i j : Fin n), V i (T.cuts (T.assign i).castSucc) (T.cuts (T.assign i).succ) ≥
    V i (T.cuts j.castSucc) (T.cuts j.succ) - e

def CakeAnswer (D : CakeData) (e : ℚ) (T : Allocation ℚ D.n) : Prop :=
  T.realize.Complete 1 ∧ EnvyFree (fun i => (D.densities i).value) (e : ℝ) T.realize

end ContiguousCake597.Approximate


