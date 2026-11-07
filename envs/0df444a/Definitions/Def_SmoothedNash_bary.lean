-- Prove2me | Definitions.Def_SmoothedNash_bary
-- name    : SmoothedNash_bary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:18.84021+00:00
-- url     : https://prove2.me/theorems/120f479d-3d32-4c22-9ad8-50e790f1a7a8
-- title:
--   Barycenter $b_A$ of $K_A$
-- statement:
--   The **barycenter** $b_A$ of $K_A$ is the product of the uniform distributions on $A_1, \dots, A_m$:
--   $$
--   b_A(i, a) = \begin{cases} 1/|A_i| & a \in A_i, \\ 0 & a \notin A_i. \end{cases}
--   $$
--   It is the single level-$0$ center of Algorithm 2 ($F_0(A) = \{b_A\}$).
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2 line 3, p.15, and proof of Lemma 2.6, p.17

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- The barycenter `b_A` of `K_A` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 2 line 3, p.15, and proof of Lemma 2.6, p.17):
the product of the uniform distributions on `A_1, …, A_m`. -/
noncomputable def bary {m n : ℕ} (A : SupportProfile m n) : Fin m → Fin n → ℝ :=
  fun i a => if a ∈ A.1 i then 1 / ((A.1 i).card : ℝ) else 0

end SmoothedNash


