-- Prove2me | Definitions.Def_StochQuasiNewton_SQN_LBFGS
-- name    : StochQuasiNewton_SQN_LBFGS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:50:32.287237+00:00
-- url     : https://prove2.me/theorems/a37fe4d3-bf1a-46fd-a9e6-a29d5014632f
-- title:
--   Algorithm 2 (Hessian Updating) and the direct L-BFGS update (3.7)
-- statement:
--   Fix a memory parameter $M$, a counter $t\ge1$, correction pairs $(s_j,y_j)$, and put $\tilde m=\min\{t,M\}$.
--
--   **Algorithm 2 (inverse L-BFGS matrix).** Start from $H=\dfrac{s_t^Ty_t}{y_t^Ty_t}I$ and, for $j=t-\tilde m+1,\dots,t$ (oldest pair first), with $\rho_j=1/(y_j^Ts_j)$, apply the BFGS formula (2.5)
--   $$H\leftarrow (I-\rho_j s_jy_j^T)\,H\,(I-\rho_j y_js_j^T)+\rho_j s_js_j^T .$$
--   The result is $H_t$.
--
--   **Direct L-BFGS matrices (3.7).** Start from $B_t^{(0)}=\dfrac{y_t^Ty_t}{s_t^Ty_t}I$ and, for $i=0,\dots,\tilde m-1$ and $j=t-\tilde m+1+i$, set
--   $$B_t^{(i+1)}=B_t^{(i)}-\frac{B_t^{(i)}s_js_j^TB_t^{(i)}}{s_j^TB_t^{(i)}s_j}+\frac{y_jy_j^T}{y_j^Ts_j}.$$
--   The paper writes $B_{t+1}=B_t^{(\tilde m)}$.
--
--   Algorithm 2 is the quasi-Newton matrix of the SQN method; the direct matrices are the objects of the proof of Lemma 3.1 (they are the inverses of the $H$'s built from the same pairs).
--
--   **Formalization Note** `lbfgsInverseStage M t s y i` and `lbfgsDirectStage M t s y i` are the matrices after $i$ updates; `lbfgsMatrix M t s y` is stage $\tilde m$ of the former. The formulas are literal: there is no guard against a vanishing $y_j^Ts_j$ or $s_j^TB s_j$ (Lean then divides by $0$, giving $0$); the theorems assume $s_j\neq0$ and pairs coming from subsampled Hessians instead.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1012, Algorithm 2 and Eq. (2.5); p. 1015, proof of Lemma 3.1, steps (i)–(iii) and Eq. (3.7)

import Mathlib

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- One inverse BFGS update (2.5) with the correction pair `(s, y)`:
`H ← (I − ρ s yᵀ) H (I − ρ y sᵀ) + ρ s sᵀ`, where `ρ = 1 / (yᵀ s)`. No guard is placed on
`yᵀ s = 0`. -/
noncomputable def bfgsInverseUpdate {n : ℕ} (s y : EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - (1 / ⟪y, s⟫) • Matrix.vecMulVec s.ofLp y.ofLp) * H *
      (1 - (1 / ⟪y, s⟫) • Matrix.vecMulVec y.ofLp s.ofLp) +
    (1 / ⟪y, s⟫) • Matrix.vecMulVec s.ofLp s.ofLp

/-- The intermediate matrices of Algorithm 2 (Hessian Updating) at counter `t` with memory `M`:
stage `0` is the scaling `(s_tᵀ y_t)/(y_tᵀ y_t) I` built from the newest pair, and stage `i + 1`
applies (2.5) to stage `i` with the pair `j = t − m̃ + 1 + i`, where `m̃ = min t M`; the pairs
are thus used oldest first, `j = t − m̃ + 1, …, t`. -/
noncomputable def lbfgsInverseStage {n : ℕ} (M t : ℕ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => (⟪s t, y t⟫ / ⟪y t, y t⟫) • (1 : Matrix (Fin n) (Fin n) ℝ)
  | i + 1 => bfgsInverseUpdate (s (t - min t M + 1 + i)) (y (t - min t M + 1 + i))
      (lbfgsInverseStage M t s y i)

/-- Algorithm 2 (Hessian Updating): the limited-memory BFGS matrix `H_t`, the result of the
`m̃ = min t M` updates (2.5) applied to the scaled identity. -/
noncomputable def lbfgsMatrix {n : ℕ} (M t : ℕ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  lbfgsInverseStage M t s y (min t M)

/-- One direct BFGS update (3.7) with the correction pair `(s, y)`:
`B ← B − (B s sᵀ B)/(sᵀ B s) + (y yᵀ)/(yᵀ s)`. No guard is placed on vanishing denominators. -/
noncomputable def bfgsDirectUpdate {n : ℕ} (s y : EuclideanSpace ℝ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  B - (1 / dotProduct s.ofLp (B.mulVec s.ofLp)) • (B * Matrix.vecMulVec s.ofLp s.ofLp * B) +
    (1 / ⟪y, s⟫) • Matrix.vecMulVec y.ofLp y.ofLp

/-- The direct limited-memory BFGS matrices `B_t^{(i)}` of the proof of Lemma 3.1, (i)–(ii):
`B_t^{(0)} = (y_tᵀ y_t)/(s_tᵀ y_t) I`, and `B_t^{(i+1)}` is (3.7) applied to `B_t^{(i)}` with the
pair `j = t − m̃ + 1 + i`, `m̃ = min t M`. Step (iii) of the paper sets `B_{t+1} = B_t^{(m̃)}`. -/
noncomputable def lbfgsDirectStage {n : ℕ} (M t : ℕ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => (⟪y t, y t⟫ / ⟪s t, y t⟫) • (1 : Matrix (Fin n) (Fin n) ℝ)
  | i + 1 => bfgsDirectUpdate (s (t - min t M + 1 + i)) (y (t - min t M + 1 + i))
      (lbfgsDirectStage M t s y i)

end StochQuasiNewton.SQN


