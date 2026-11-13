-- Prove2me | Definitions.Def_DeepQOperator_Quantizer
-- name    : DeepQOperator_Quantizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:00:04.999794+00:00
-- url     : https://prove2.me/theorems/c37d73df-ea7a-4f02-8eda-475a72f6b43c
-- title:
--   The uniform scalar quantizer $j_d$, $Q_d$ of (41)
-- statement:
--   For an integer $d\ge1$ and a scalar $x\in[-1,1]$, the **encoder** and **reconstruction** are
--   $$j_d(x)=\min\{2^d-1,\ \lfloor2^{d-1}(x+1)\rfloor\},\qquad Q_d(x)=-1+(2j_d(x)+1)2^{-d}.$$
--   The encoder sends the index $j_d(x)\in\{0,\dots,2^d-1\}$ with $d$ bits; the algorithm computes $Q_d(x)$ from the index alone. Interior bin boundaries go to the bin on their right and the last bin contains $1$.
--
--   These are the explicit uniform quantizers used by the upper-bound protocol of Theorem 2.
--
--   **Formalization Note** $j_d(x)$ is a natural number (the integer floor sent to $\mathbb N$, which changes no value for $x\ge-1$). `recon d j` $=-1+(2j+1)/2^d$ is the reconstruction from a received index, and $Q_d=$ `recon d ∘ jEnc d`. The maps are defined for all real $x$; the paper uses them on $[-1,1]$.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.1 eq. (41), p.23 (PDF p.26)

import Mathlib

namespace DeepQOperator

/-!
# The uniform scalar quantizer (41)

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.1, eq. (41), p.23 (PDF p.26).

For an integer `d ≥ 1` and `x ∈ [-1, 1]`,
`j_d(x) = min{2^d - 1, ⌊2^{d-1}(x + 1)⌋}` and `Q_d(x) = -1 + (2 j_d(x) + 1) 2^{-d}`.
The encoder sends the index `j_d(x)`; the algorithm reconstructs `Q_d(x)` from the index alone.

**Formalization Note.** `jEnc d x` is a natural number: the floor is taken in `ℤ` and sent to `ℕ`
with `Int.toNat`, which is the identity on the floor's values for `x ≥ -1`. The maps are defined
for every real `x` and every `d`; the paper uses them for `d ≥ 1` and `x ∈ [-1,1]` only, and
`jEnc d x ≤ 2^d - 1` holds for all inputs because of the `min`. `recon d j` is the reconstruction
from a received index; `qRound d x = recon d (jEnc d x)` is `Q_d(x)`.
-/

/-- The encoder `j_d(x) = min{2^d - 1, ⌊2^{d-1}(x + 1)⌋}`. -/
noncomputable def jEnc (d : ℕ) (x : ℝ) : ℕ :=
  min (2 ^ d - 1) (Int.toNat ⌊(2 : ℝ) ^ (d - 1) * (x + 1)⌋)

/-- The reconstruction from a received index `j`: `-1 + (2j + 1) 2^{-d}`. -/
noncomputable def recon (d j : ℕ) : ℝ := -1 + (2 * (j : ℝ) + 1) / 2 ^ d

/-- `Q_d(x) = -1 + (2 j_d(x) + 1) 2^{-d}`. -/
noncomputable def qRound (d : ℕ) (x : ℝ) : ℝ := recon d (jEnc d x)

lemma jEnc_lt (d : ℕ) (x : ℝ) : jEnc d x < 2 ^ d :=
  lt_of_le_of_lt (min_le_left _ _) (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)

end DeepQOperator


