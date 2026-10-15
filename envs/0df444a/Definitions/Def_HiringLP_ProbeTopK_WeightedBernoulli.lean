-- Prove2me | Definitions.Def_HiringLP_ProbeTopK_WeightedBernoulli
-- name    : HiringLP_ProbeTopK_WeightedBernoulli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:38.618889+00:00
-- url     : https://prove2.me/theorems/54efa382-a4c2-4b2c-8c37-8202af6dd083
-- title:
--   §4.6, p. 20 — weighted Bernoulli instances and the rewritten LPptk
-- statement:
--   A **weighted Bernoulli instance** of ProbeTop-k has, for each applicant $i \in [n]$, a value equal to $r_i \ge 0$ with probability $q_i \in [0,1]$ and $0$ otherwise, together with $k$ positions and $T$ interviews, $1 \le k \le T \le n$. For these instances $\mathrm{LP}_{ptk}$ is rewritten (p. 20), dropping the variable of the zero value, as
--
--   $$
--   \max \sum_{i=1}^n r_i x_i \quad \text{s.t.} \quad x_i \le y_i q_i,\quad \sum_i y_i \le T,\quad \sum_i x_i \le k,\quad x_i \ge 0,\quad 0 \le y_i \le 1 .
--   $$
--
--   An optimal solution is a feasible $(x, y)$ whose objective is at least that of every feasible point.
--
--   This is the LP that Lemma 5 is about, and the bridge from ProbeTop-k to the Sequential Offering problem.
--
--   **Formalization Note.** Applicants are `Fin n`; the instance is a structure with fields `k`, `T`, `r`, `q`, and validity is a separate predicate.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 20, §4.6

import Mathlib

namespace HiringLP.ProbeTopK

/-- §4.6, p. 20: a weighted Bernoulli instance: applicant `i`'s value is `r i` with probability `q i`
and `0` otherwise. -/
structure WBInstance (n : ℕ) where
  k : ℕ
  T : ℕ
  r : Fin n → ℝ
  q : Fin n → ℝ

/-- `1 ≤ k ≤ T ≤ n` (p. 11), non-negative values, probabilities in `[0, 1]`. -/
def WBInstance.Valid {n : ℕ} (I : WBInstance n) : Prop :=
  1 ≤ I.k ∧ I.k ≤ I.T ∧ I.T ≤ n ∧ (∀ i, 0 ≤ I.r i) ∧ ∀ i, 0 ≤ I.q i ∧ I.q i ≤ 1

/-- p. 20: the constraints of LPptk rewritten for weighted Bernoulli instances. -/
def WBFeasible {n : ℕ} (I : WBInstance n) (x y : Fin n → ℝ) : Prop :=
  (∀ i, x i ≤ y i * I.q i) ∧ (∑ i, y i ≤ (I.T : ℝ)) ∧ (∑ i, x i ≤ (I.k : ℝ)) ∧
    (∀ i, 0 ≤ x i) ∧ ∀ i, 0 ≤ y i ∧ y i ≤ 1

/-- p. 20: the objective `Σ_i r_i x_i`. -/
def WBobj {n : ℕ} (I : WBInstance n) (x : Fin n → ℝ) : ℝ := ∑ i, I.r i * x i

/-- An optimal solution of the rewritten LP. -/
def WBIsOpt {n : ℕ} (I : WBInstance n) (x y : Fin n → ℝ) : Prop :=
  WBFeasible I x y ∧ ∀ x' y', WBFeasible I x' y' → WBobj I x' ≤ WBobj I x

end HiringLP.ProbeTopK


