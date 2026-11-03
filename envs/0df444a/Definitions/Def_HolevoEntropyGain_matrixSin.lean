-- Prove2me | Definitions.Def_HolevoEntropyGain_matrixSin
-- name    : HolevoEntropyGain_matrixSin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:53.196849+00:00
-- url     : https://prove2.me/theorems/ab4ee2d1-2ecb-4a14-a428-9dd7b8597224
-- title:
--   Sine of a real square matrix
-- statement:
--   For a real square matrix $M$,
--
--   $$
--   \sin M = \sum_{k\ge0}\frac{(-1)^k}{(2k+1)!}M^{2k+1},
--   $$
--
--   the everywhere convergent power series. Used for $\cot(\beta\epsilon\Delta)$ in (17).
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5

import Mathlib

namespace HolevoEntropyGain

/-- The sine of a real square matrix, by its everywhere convergent power series
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (17), p.5, PDF p.5). -/
noncomputable def matrixSin {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, (((-1 : ℝ) ^ k) / ((2 * k + 1).factorial : ℝ)) • M ^ (2 * k + 1)

end HolevoEntropyGain


