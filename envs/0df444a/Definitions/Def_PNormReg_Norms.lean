-- Prove2me | Definitions.Def_PNormReg_Norms
-- name    : PNormReg_Norms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:15.515455+00:00
-- url     : https://prove2.me/theorems/525d69ba-217a-475e-94e7-25229c9c48e8
-- title:
--   Vector and matrix norms: $\|v\|_p$, $\|v\|_2$, $\|v\|_\infty$, $\|M\|_{p,2}$, $\|M\|_{2\to s}$
-- statement:
--   For $v\in\mathbb R^n$ and finite $p$, $\|v\|_p^p=\sum_i|v_i|^p$ and $\|v\|_p=(\sum_i|v_i|^p)^{1/p}$; $\|v\|_2$ is the Euclidean norm and $\|v\|_\infty$ the sup norm. For a matrix $M\in\mathbb R^{n\times d}$,
--
--   $$\|M\|_{p,2}=\Big(\sum_{i}\|M_{i:}\|_2^p\Big)^{1/p},\qquad \|M\|_{2\to s}=\max_{\|x\|_2\le1}\|Mx\|_s.$$
--
--   The first is the $\ell_p$ norm of the row $\ell_2$ norms and is not an operator norm. The conjugate exponent is $q/(q-1)$.
--
--   These are the quantities in which the paper's reduction to matrix games is measured.
--
--   **Formalization Note** Powers use `Real.rpow`, so $|r|^0=1$ also at $r=0$, which is the reading p.19 prescribes. The maximum defining $\|M\|_{2\to s}$ is written as a real `sSup` of a nonempty bounded set.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), conventions, p.7

import Mathlib

open Matrix

namespace PNormReg

/-!
# Vector and matrix norms

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), "General notation" and "Matrix-related
conventions", p.7.

**Formalization Note.** Vectors are functions `Fin n → ℝ`. `lpPow p v = ∑ i, |v i| ^ p` uses
`Real.rpow`, so `|v i| ^ 0 = 1` also at `v i = 0`, the paper's reading at p = 2 (p.19). All uses have
`p ≥ 1`. `linfNorm` is Mathlib's sup norm on `Fin n → ℝ`, which is `0` at `n = 0`.
-/

/-- `∥v∥_p^p`. -/
noncomputable def lpPow {n : ℕ} (p : ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, |v i| ^ p

/-- `∥v∥_p` for finite `p`. -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (v : Fin n → ℝ) : ℝ := lpPow p v ^ (1 / p)

/-- The Euclidean norm `∥v∥₂`. -/
noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- `∥v∥_∞`. -/
noncomputable def linfNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ‖v‖

/-- `∥M∥_{p,2}`, the `ℓ_p` norm of the vector of row `ℓ₂` norms (p.7); not an operator norm. -/
noncomputable def rowNormP2 {n d : ℕ} (p : ℝ) (M : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  lpNorm p (fun i => l2Norm (M i))

/-- The induced operator norm `∥M∥_{2→s} = max_{∥x∥₂ ≤ 1} ∥Mx∥_s` (p.7). The set is nonempty and
bounded, so the supremum is the paper's maximum. -/
noncomputable def opTwoTo {n d : ℕ} (s : ℝ) (M : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  sSup ((fun x : Fin d → ℝ => lpNorm s (M *ᵥ x)) '' {x | l2Norm x ≤ 1})

/-- The conjugate exponent `q/(q − 1)`: `p` from `q` in §5 and `q` from `p` in §3 (pp.18, 33). -/
noncomputable def conjExp (q : ℝ) : ℝ := q / (q - 1)

end PNormReg


