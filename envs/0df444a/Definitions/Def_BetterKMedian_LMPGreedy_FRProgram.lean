-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
-- name    : BetterKMedian_LMPGreedy_FRProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:14.742254+00:00
-- url     : https://prove2.me/theorems/e8534e7b-27df-408d-88ef-0596a15373a2
-- title:
--   Definition 3.2 — the factor-revealing program and "$\rho$ bounds it for all $n\ge1$"
-- statement:
--   For $n\ge1$ and a bidding function $\beta$, the variables are $d_j$ ($1\le j\le n$), $f$, and $r_{j,k}$ ($1\le j\le k\le n+1$), represented as `d : ℕ → ℝ`, `f : ℝ`, `r : ℕ → ℕ → ℝ` with the paper's 1-based indices (values outside these ranges occur nowhere). The objective (5) is
--   $$\texttt{frObjective}=\sum_{j=1}^n\Bigl(\sum_{k=j}^n\beta(r_{j,k},r_{j,k+1})+r_{j,n+1}\Bigr)-f.$$
--   `FRConstraints` are (7) $r_{j,k+1}\le r_{j,k}$ ($1\le j\le k\le n$); (8) $r_{k,k}\le r_{j,k}+d_k+d_j$ ($1\le j<k\le n$); (9) $r_{j,\ell}\le r_{k,\ell}+d_k+d_j$ ($1\le j\ne k<\ell\le n+1$, read as $j,k<\ell$, $j\ne k$); (10) $\sum_{j=1}^{k-1}\beta(r_{j,k},d_j)+\sum_{j=k}^n\beta(r_{k,k},d_j)\le f$ ($1\le k\le n$); (11) $d_j,f,r_{j,k}\ge0$ in range. `FRFeasible` adds the normalization (6) $\sum_{i=1}^nd_i=1$.
--
--   `FRBoundedBy β ρ`: $\rho$ is an upper bound on the optimal value for every $n\ge1$, i.e. every feasible point for every $n\ge1$ has objective $\le\rho$ (no supremum is formed).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Definition 3.2, printed p. 13 (PDF 15)

import Mathlib

set_option autoImplicit false

/-!
# The factor-revealing program (Definition 3.2)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Definition 3.2, printed p. 13 (PDF 15).

Conventions.
* Indices are the paper's, 1-based natural numbers: clients `1 ≤ j ≤ n`, and `r j k` for
  `1 ≤ j ≤ k ≤ n + 1` (column `n + 1` is the final connection distance). The variables are
  functions `d : ℕ → ℝ`, `r : ℕ → ℕ → ℝ` and a real `f`; their values outside these ranges
  occur in no constraint and not in the objective.
* "`ρ` is an upper bound on the optimal value" is stated as: every feasible point has objective
  value at most `ρ` (no supremum is taken).
-/

namespace BetterKMedian.LMPGreedy

open Finset

/-- Objective (5): `Σ_{j=1}^n (Σ_{k=j}^n β(r_{j,k}, r_{j,k+1}) + r_{j,n+1}) − f`. -/
noncomputable def frObjective (β : ℝ → ℝ → ℝ) (n : ℕ) (f : ℝ) (r : ℕ → ℕ → ℝ) : ℝ :=
  (∑ j ∈ Icc 1 n, ((∑ k ∈ Icc j n, β (r j k) (r j (k + 1))) + r j (n + 1))) - f

/-- Constraints (7)–(11) of Definition 3.2 (everything except the normalization (6)):
* (7) `r_{j,k+1} ≤ r_{j,k}` for `1 ≤ j ≤ k ≤ n`;
* (8) `r_{k,k} ≤ r_{j,k} + d_k + d_j` for `1 ≤ j < k ≤ n`;
* (9) `r_{j,ℓ} ≤ r_{k,ℓ} + d_k + d_j` for `1 ≤ j ≠ k < ℓ ≤ n + 1` (`j, k < ℓ`, `j ≠ k`);
* (10) `Σ_{j=1}^{k−1} β(r_{j,k}, d_j) + Σ_{j=k}^n β(r_{k,k}, d_j) ≤ f` for `1 ≤ k ≤ n`;
* (11) `d_j, f, r_{j,k} ≥ 0` for `j, k` in range. -/
def FRConstraints (β : ℝ → ℝ → ℝ) (n : ℕ) (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → r j (k + 1) ≤ r j k) ∧
  (∀ j k : ℕ, 1 ≤ j → j < k → k ≤ n → r k k ≤ r j k + d k + d j) ∧
  (∀ j k l : ℕ, 1 ≤ j → 1 ≤ k → j ≠ k → j < l → k < l → l ≤ n + 1 →
      r j l ≤ r k l + d k + d j) ∧
  (∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∑ j ∈ Ico 1 k, β (r j k) (d j)) + (∑ j ∈ Icc k n, β (r k k) (d j)) ≤ f) ∧
  ((∀ j : ℕ, 1 ≤ j → j ≤ n → 0 ≤ d j) ∧ 0 ≤ f ∧
      ∀ j k : ℕ, 1 ≤ j → j ≤ n → j ≤ k → k ≤ n + 1 → 0 ≤ r j k)

/-- Feasibility for Definition 3.2: the normalization (6) `Σ_{i=1}^n d_i = 1` and (7)–(11). -/
def FRFeasible (β : ℝ → ℝ → ℝ) (n : ℕ) (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  (∑ i ∈ Icc 1 n, d i) = 1 ∧ FRConstraints β n d f r

/-- `ρ` is an upper bound on the optimal value of the factor-revealing program of
Definition 3.2 over all `n ≥ 1`: every feasible point, for every `n ≥ 1`, has objective `≤ ρ`. -/
def FRBoundedBy (β : ℝ → ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ),
    FRFeasible β n d f r → frObjective β n f r ≤ ρ

end BetterKMedian.LMPGreedy


