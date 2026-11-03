-- Prove2me | Definitions.Def_HolevoEntropyGain_matrixCos
-- name    : HolevoEntropyGain_matrixCos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:50.781608+00:00
-- url     : https://prove2.me/theorems/45f8fbaa-3d58-4b0e-a303-6e1d34d80b4d
-- title:
--   Cosine of a real square matrix
-- statement:
--   For a real square matrix $M$,
--
--   $$
--   \cos M = \sum_{k\ge0}\frac{(-1)^k}{(2k)!}M^{2k},
--   $$
--
--   the everywhere convergent power series. Used for $\cot(\beta\epsilon\Delta)$ in (17).
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5

import Mathlib

namespace HolevoEntropyGain

/-- The cosine of a real square matrix, by its everywhere convergent power series
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5, PDF p.5). -/
noncomputable def matrixCos {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, (((-1 : ℝ) ^ k) / ((2 * k).factorial : ℝ)) • M ^ (2 * k)

end HolevoEntropyGain


