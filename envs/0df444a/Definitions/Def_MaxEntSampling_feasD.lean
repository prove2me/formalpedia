-- Prove2me | Definitions.Def_MaxEntSampling_feasD
-- name    : MaxEntSampling_feasD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:56.755238+00:00
-- url     : https://prove2.me/theorems/0b8a9b35-063d-4ac2-9f8d-b78eea713a89
-- title:
--   The feasible set $D=\{x\in[0,1]^n:\sum_i x_i=s\}$ of PC (9)
-- statement:
--   The feasible set of the continuous relaxation PC (9) is
--
--   $$
--   D := \Bigl\{x\in\mathbb R^n : \sum_{i\in[n]} x_i = s,\ 0\le x_i\le 1\ \ \forall i\in[n]\Bigr\}.
--   $$
--
--   Its binary points are the indicator vectors of the size-$s$ subsets of $[n]$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, eq. (9), p.9 (PDF p.9); the name D is from Lemma 4, p.12

import Mathlib

namespace MaxEntSampling

/-- **The feasible set `D` of PC (9).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, eq. (9), p.9 (PDF p.9): the constraints "Σ_{i∈[n]} xi = s, x ∈ [0,1]^n";
the set is named D in Lemma 4, p.12.

`feasD n s = {x ∈ ℝⁿ : Σ_i x_i = s, 0 ≤ x_i ≤ 1 for all i}`. -/
def feasD (n s : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i, x i = s ∧ ∀ i, 0 ≤ x i ∧ x i ≤ 1}

end MaxEntSampling


