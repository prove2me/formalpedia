-- Prove2me | Definitions.Def_FreeWeaver_Walk_Weaver
-- name    : FreeWeaver_Walk_Weaver
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:31:43.581483+00:00
-- url     : https://prove2.me/theorems/5047b696-e408-4f4c-859b-a811756c231a
-- title:
--   Weaver's data, signs, the signed sum, and the machine input layout
-- statement:
--   For $v_1,\dots,v_n\in\mathbb C^m$ (`v : Fin n → Fin m → ℂ`), $A_i=v_iv_i^*$ (`rankOne`), $a_i=\|v_i\|^2=\sum_j|v_i(j)|^2$ (`sqNorm`), the Parseval condition $\sum_iv_iv_i^*=I_m$ (`IsParseval`), signs $\sigma\in\{-1,1\}^n$ (`IsSigns`, real entries $\pm1$) and the signed sum $H(x)=\sum_ix_iA_i$ (`signedSum`), whose operator norm is the discrepancy. `weaverInput n m v` is the input of the real-arithmetic machine: the list $[n,m]$ followed, for $i=1,\dots,n$ and inside for $j=1,\dots,m$, by $\operatorname{Re}v_i(j),\operatorname{Im}v_i(j)$ ("complex matrices stored by their real and imaginary parts", p. 2). `sgn t` is $1$ for $t\ge0$ and $-1$ for $t<0$ (§1.4).
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 2 and p. 24, Theorem 1.1, §1.4, §4.1

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FreeWeaver_Walk_Pencil

namespace FreeWeaver.Walk

noncomputable section

/-!
# Weaver's discrepancy data and the input layout of the real-arithmetic machine

Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version dated
November 3, 2026; sha256 c06bf728…), p. 2 (Theorem 1.1 and the computational model), §1.4 and §4.1,
p. 24.

**Formalization Note** Vectors `v_1, …, v_n ∈ ℂ^m` are a function `v : Fin n → Fin m → ℂ` (indices
from `0`). `A_i = v_i v_i*` is `vecMulVec (v i) (star (v i))`, `a_i = ‖v_i‖² = Σ_j |v_i(j)|²`. Signs
are real vectors with entries `1` or `−1`. The machine input stores `n`, `m` and then, for
`i = 1, …, n` and, inside, `j = 1, …, m`, the real part and then the imaginary part of `v_i(j)`
("complex matrices stored by their real and imaginary parts", p. 2). `ε` is not part of the input.
-/

/-- The rank-one matrix `A_i = v v*`. -/
def rankOne {m : ℕ} (v : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.vecMulVec v (star v)

/-- The squared Euclidean norm `‖v‖² = Σ_j |v(j)|²`. -/
def sqNorm {m : ℕ} (v : Fin m → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

/-- The isotropic (Parseval) condition `Σ_i v_i v_i* = I_m`. -/
def IsParseval {n m : ℕ} (v : Fin n → Fin m → ℂ) : Prop :=
  ∑ i, rankOne (v i) = 1

/-- `σ ∈ {−1, 1}^n`. -/
def IsSigns {n : ℕ} (σ : Fin n → ℝ) : Prop := ∀ i, σ i = 1 ∨ σ i = -1

/-- The signed sum `H(x) = Σ_i x_i A_i` (for signs, the matrix whose norm is the discrepancy). -/
def signedSum {n m : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ i, ((x i : ℝ) : ℂ) • rankOne (v i)

/-- The input list of the machine: `[n, m]`, then `Re v_i(j), Im v_i(j)` for `i = 1..n`, and inside
each `i`, `j = 1..m`. -/
def weaverInput (n m : ℕ) (v : Fin n → Fin m → ℂ) : List ℝ :=
  [(n : ℝ), (m : ℝ)] ++
    (List.finRange n).flatMap fun i => (List.finRange m).flatMap fun j => [(v i j).re, (v i j).im]

/-- `sgn(t) = 1` if `t ≥ 0` and `−1` if `t < 0` (§1.4, p. 12). -/
def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

end

end FreeWeaver.Walk


