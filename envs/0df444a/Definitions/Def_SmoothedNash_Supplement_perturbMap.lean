-- Prove2me | Definitions.Def_SmoothedNash_Supplement_perturbMap
-- name    : SmoothedNash_Supplement_perturbMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:08:25.970468+00:00
-- url     : https://prove2.me/theorems/7fe4ea4b-a4cb-4101-bcaf-af056d35e5b2
-- title:
--   Affine perturbation $\tilde F(x) = F(x) + Dx + e$
-- statement:
--   For an $n \times n$ matrix $D$ and a vector $e \in \mathbb R^n$, the **perturbed map** used in the proof of Theorem 4.20 is
--   $$
--   \tilde F(x) = F(x) + D x + e .
--   $$
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), proof of Theorem 4.20, pp.43–44

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The affine perturbation `F̃(x) = F(x) + D x + e` of the proof of Theorem 4.20 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53),
pp.43–44), for an `n × n` matrix `D` (entries `D (i, j)`) and a vector `e ∈ ℝ^n`. -/
noncomputable def perturbMap {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (D : Fin n × Fin n → ℝ) (e : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => F x + WithLp.toLp 2 (fun i => ∑ j, D (i, j) * x j + e i)

end SmoothedNash.Supplement


