-- Prove2me | Definitions.Def_ModernConvex_SchurFormRat
-- name    : ModernConvex_SchurFormRat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:14:05.850768+00:00
-- url     : https://prove2.me/theorems/b9124ff7-e0b7-4dac-95d1-aa5487e30991
-- title:
--   The Schur form at a pivot over the rationals
-- statement:
--   **The Schur form over the rationals.**
--
--   For a rational matrix $M$ of order $n$ and an index $i$, the rational Schur form at $i$ is
--   $$Q_i(v)=\sum_{j\ne i}\sum_{k\ne i}v_jv_kM_{jk}-\frac{1}{M_{ii}}\Big(\sum_{j\ne i}M_{ij}v_j\Big)^2\in\mathbb Q,$$
--   for $v\in\mathbb Q^n$ — the exact analogue of the real Schur form, over $\mathbb Q$ instead of $\mathbb R$.
--
--   This exists because the PSD oracle must be **computable**. A decision procedure that splits on real numbers is not computable, whereas comparisons on $\mathbb Q$ are; and the output certificate has to be rational anyway, since the machine that runs the oracle is a rational-arithmetic machine. The rational Schur form is the recursive payload of that oracle: eliminating the coordinate $i$ reduces the question to $Q_i$.
--
--   Since the definition uses only the field operations, the completing-the-square identity holds over $\mathbb Q$ exactly as over $\mathbb R$.
-- source:
--   Schur complement at a 1x1 pivot, over Q; recursive payload of the computable symmetric-elimination PSD oracle for the MAXCUT SDP.

import Mathlib

/-!
# The Schur form over `ℚ`

The PSD oracle must run over the rationals: its output is a rational certificate, its case splits
must be decidable, and the machine that executes it is a rational-arithmetic machine. This file
fixes the rational Schur form at a pivot:

  `schurFormRat M i v = Σ_{j,k≠i} v j v k M j k − (M i i)⁻¹ (Σ_{j≠i} M i j v j)²`.

Everything here is pure field algebra, so the statement is the one of the real case verbatim;
`quadform_eq_schurFormRat` (proved separately) records that `v ᵀ M v` is this form plus a square.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- The Schur form of a rational matrix at the pivot `i`, on the remaining coordinates. -/
noncomputable def schurFormRat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (v : Fin n → ℚ) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, v j * (M j k * v k)
    - (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j) ^ 2

end ModernConvex.Relaxations


