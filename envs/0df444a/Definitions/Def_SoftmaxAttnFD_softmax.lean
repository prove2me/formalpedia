-- Prove2me | Definitions.Def_SoftmaxAttnFD_softmax
-- name    : SoftmaxAttnFD_softmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:36.737804+00:00
-- url     : https://prove2.me/theorems/083c6c87-5626-4661-abcb-e472b61c9798
-- title:
--   The softmax function
-- statement:
--   For $x\in\mathbb R^n$, $\mathrm{softmax}(x)_j=e^{x_j}/\sum_{l} e^{x_l}$.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 2.5, p.11

import Mathlib

namespace SoftmaxAttnFD

/-- `softmax(x)_j = e^{x_j} / ∑_l e^{x_l}` (arXiv:2611.06055, sha256 a60f7609…, Lemma 2.5, p.11). -/
noncomputable def softmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) / ∑ l, Real.exp (x l)

end SoftmaxAttnFD


