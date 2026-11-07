-- Prove2me | Definitions.Def_SoftmaxAttnFD_BatchMaxima
-- name    : SoftmaxAttnFD_BatchMaxima
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:21.251083+00:00
-- url     : https://prove2.me/theorems/c501222c-3c9d-472b-8c49-6399ae3acad2
-- title:
--   The batch maxima problem: layout and correct output
-- statement:
--   Given queries $q_i\in\mathbb Q^d$ and points $k_j\in\mathbb Q^d$, the task is to compute every maximum $M_i=\max_j q_i\cdot k_j$ and a maximizing index. The input memory holds $m$, $n$, the queries and the points. After the input, each query has four cells, the triple of $M_i$ and a $0$-based index. The output is correct if the index is valid, the triple is exactly the score of that index, and no point scores more.
--
--   The running-time base is $b+\log_2(m+n)+\log_2U$, with $U$ a magnitude bound.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Proposition 5.1, p.20

import Definitions.Def_SoftmaxAttnFD_RatEnc

namespace SoftmaxAttnFD

/-- The input cells of the batch maxima problem: `m, n`, the queries, then the points. -/
def maxInput {m n d : ℕ} (q : Fin m → Fin d → RatEnc) (k : Fin n → Fin d → RatEnc) : List ℕ :=
  [m, n] ++ matCells q ++ matCells k

/-- Correct output of the batch maxima problem (arXiv:2611.06055, sha256 a60f7609…, Proposition 5.1,
p.20): after the input, each query `i` has four cells, the triple of `M_i` and a 0-based index. The
index is a valid point, the triple is exactly its score, and no point scores more. So `M_i` is the
exact maximum and the index attains it. -/
def maxGood {m n d : ℕ} (q : Fin m → Fin d → RatEnc) (k : Fin n → Fin d → RatEnc)
    (out : ℕ → ℕ) : Prop :=
  ∀ i : Fin m,
    let a := (maxInput q k).length + 4 * i.val
    ValidAt out a ∧
      ∃ h : out (a + 3) < n,
        valAt out a = qdot (q i) (k ⟨out (a + 3), h⟩) ∧
          ∀ j, qdot (q i) (k j) ≤ valAt out a

/-- The soft-O base of the batch maxima problem: `b + log₂(m + n) + log₂ U`. -/
noncomputable def lamMax (b m n U : ℕ) : ℝ :=
  (b : ℝ) + Real.logb 2 ((m : ℝ) + n) + Real.logb 2 U

end SoftmaxAttnFD


