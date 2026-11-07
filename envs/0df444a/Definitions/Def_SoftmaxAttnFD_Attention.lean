-- Prove2me | Definitions.Def_SoftmaxAttnFD_Attention
-- name    : SoftmaxAttnFD_Attention
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:24.244218+00:00
-- url     : https://prove2.me/theorems/6f114d80-66bc-469e-b2b8-3b0745835e51
-- title:
--   The problem $\mathrm{Attention}_d$: attention values, input layout, correct output
-- statement:
--   Given $Q\in\mathbb Q^{m\times d}$, $K\in\mathbb Q^{n\times d}$ and $V\in\mathbb Q^{n\times r}$ with rows $q_i$, $k_j$, $v_j$,
--   $$\mathrm{Att}(Q,K,V)_{it}=\frac{\sum_{j=1}^n e^{q_i\cdot k_j}v_{jt}}{\sum_{j=1}^n e^{q_i\cdot k_j}},\qquad i\in[m],\ t\in[r].$$
--   The input memory holds $m$, $n$, $p$, then $Q$, $K$, $V$ row by row as encoded triples, and $0$ elsewhere. The output is correct if for every $(i,t)$ the memory holds a well-formed triple at address $3+3(md+nd+nr)+3(ir+t)$, and its value differs from $\mathrm{Att}(Q,K,V)_{it}$ by at most $2^{-p}$.
--
--   This is the problem of the goal theorem, $\|\hat O-\mathrm{Att}(Q,K,V)\|_{\max}\le\varepsilon$ with $\varepsilon=2^{-p}$.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definition 2.1, p.10

import Definitions.Def_SoftmaxAttnFD_RatEnc

namespace SoftmaxAttnFD

/-- `Att(Q, K, V)_{it} = (∑_j e^{q_i·k_j} v_{jt}) / (∑_j e^{q_i·k_j})` (arXiv:2611.06055,
sha256 a60f7609…, Definition 2.1, p.10). The denominator is positive when `n ≥ 1`, which every
statement using `att` assumes. -/
noncomputable def att {m n d r : ℕ} (Q : Fin m → Fin d → ℝ) (K : Fin n → Fin d → ℝ)
    (V : Fin n → Fin r → ℝ) (i : Fin m) (t : Fin r) : ℝ :=
  (∑ j, Real.exp (Q i ⬝ᵥ K j) * V j t) / ∑ j, Real.exp (Q i ⬝ᵥ K j)

/-- The input cells of Attention_d: `m, n, p`, then `Q`, `K`, `V` row by row, each entry a triple. -/
def attnInput {m n d r : ℕ} (p : ℕ) (Q : Fin m → Fin d → RatEnc) (K : Fin n → Fin d → RatEnc)
    (V : Fin n → Fin r → RatEnc) : List ℕ :=
  [m, n, p] ++ matCells Q ++ matCells K ++ matCells V

/-- The input memory of Attention_d. All other cells are `0`. -/
def attnMem {m n d r : ℕ} (p : ℕ) (Q : Fin m → Fin d → RatEnc) (K : Fin n → Fin d → RatEnc)
    (V : Fin n → Fin r → RatEnc) : ℕ → ℕ :=
  memOf (attnInput p Q K V)

/-- The output base `3 + 3(md + nd + nr)`, the first cell after the input. -/
def attnBase (m n d r : ℕ) : ℕ := 3 + 3 * (m * d + n * d + n * r)

/-- Correct output of Attention_d (arXiv:2611.06055, Definition 2.1, p.10): a rational matrix `Ô` with
`∥Ô − Att(Q, K, V)∥_max ≤ 2^{−p}`. Entry `(i, t)` is the triple at `attnBase + 3(ir + t)`. -/
def attnGood {m n d r : ℕ} (p : ℕ) (Q : Fin m → Fin d → RatEnc) (K : Fin n → Fin d → RatEnc)
    (V : Fin n → Fin r → RatEnc) (out : ℕ → ℕ) : Prop :=
  ∀ (i : Fin m) (t : Fin r),
    let a := attnBase m n d r + 3 * (i.val * r + t.val)
    ValidAt out a ∧
      |((valAt out a : ℚ) : ℝ) -
          att (fun i l => (Q i l).toReal) (fun j l => (K j l).toReal)
            (fun j t => (V j t).toReal) i t| ≤ (2 : ℝ)⁻¹ ^ p

end SoftmaxAttnFD


