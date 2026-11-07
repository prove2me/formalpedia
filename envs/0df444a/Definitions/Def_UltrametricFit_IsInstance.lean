-- Prove2me | Definitions.Def_UltrametricFit_IsInstance
-- name    : UltrametricFit_IsInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:32.912625+00:00
-- url     : https://prove2.me/theorems/52df0af7-d1a2-4800-b3e0-6bf890a3ca99
-- title:
--   Distance matrices, ultrametrics on pairs and the $\ell_p$ objective
-- statement:
--   This module fixes the data of the $\ell_p$-Ultrametric Fitting problem.
--
--   1. An **instance** is a matrix $X:\binom{[n]}{2}\to\mathbb R_{>0}$ of pairwise distances between $n$ species.
--   2. An **ultrametric** is a function $U:\binom{[n]}{2}\to\mathbb R_{>0}$ with the strong triangle inequality
--   $$U(i,j)\le\max\{U(i,k),\,U(k,j)\}$$
--   for pairwise distinct $i,j,k$.
--   3. The **objective** is
--   $$\|U-X\|_p=\Bigl(\sum_{i<j}|U(i,j)-X(i,j)|^p\Bigr)^{1/p}.$$
--
--   Every approximation guarantee of the mission compares two values of this objective.
--
--   **Formalization Note** A function on unordered pairs is a function on `Fin n × Fin n` that is symmetric and positive off the diagonal. The diagonal is free and is never read. The exponent $p$ is a real number.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §1, p.1 and §2, p.6

import Mathlib

namespace UltrametricFit

/-- **Input distance matrix**, Charikar, Gao, *Fitting Ultrametrics under any ℓ_p Objective*, STOC
2027 submission (manuscript sha256 87af12a2…), §2, p.6: `X : ([n] choose 2) → ℝ_{>0}`.

**Formalization Note.** A function on unordered pairs is encoded as a function on `Fin n × Fin n`
that is symmetric and positive off the diagonal. The diagonal is unconstrained and no definition
of this mission reads the diagonal of an input matrix. -/
def IsInstance {n : ℕ} (X : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, i ≠ j → X i j = X j i) ∧ (∀ i j, i ≠ j → 0 < X i j)

/-- **Ultrametric**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), §1, p.1 and
§2, p.6: `U : ([n] choose 2) → ℝ_{>0}` with `U(i, j) ≤ max{U(i, k), U(k, j)}`.

**Formalization Note.** `U` is a positive function on unordered pairs (`IsInstance`), so the
inequality is imposed on pairwise distinct `i, j, k` only and the diagonal stays free. Positivity
and the strong inequality imply the triangle inequality, so `U` is a metric on pairs, as the page
says. -/
def IsUltrametric {n : ℕ} (U : Fin n → Fin n → ℝ) : Prop :=
  IsInstance U ∧ ∀ i j k, i ≠ j → i ≠ k → k ≠ j → U i j ≤ max (U i k) (U k j)

/-- The index set `([n] choose 2)`: each unordered pair once, as `i < j`. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q => q.1 < q.2

/-- **The objective** `‖U − X‖_p`, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, p.6: `(Σ_{i,j ∈ ([n] choose 2)} |U(i, j) − X(i, j)|^p)^{1/p}`.

**Formalization Note.** The exponent `p` is real (`Real.rpow`); the page assumes `p ≥ 1`. The sum
runs over `i < j` and reads no diagonal entry. -/
noncomputable def lpDist {n : ℕ} (p : ℝ) (U X : Fin n → Fin n → ℝ) : ℝ :=
  (∑ q ∈ pairs n, |U q.1 q.2 - X q.1 q.2| ^ p) ^ (1 / p)

end UltrametricFit


