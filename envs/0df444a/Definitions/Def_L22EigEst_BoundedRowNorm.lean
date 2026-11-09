-- Prove2me | Definitions.Def_L22EigEst_BoundedRowNorm
-- name    : L22EigEst_BoundedRowNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:22.4172+00:00
-- url     : https://prove2.me/theorems/9d6d3992-3be8-4709-ad12-b3496e9d52ac
-- title:
--   Bounded row-norm property (Definition 3.1), with $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$, $q=1/\sqrt{\log(1/\varepsilon)}$ and $p_i=s\|A_i\|_2^2/\|A\|_F^2$
-- statement:
--   Fix a constant $c$ and an accuracy $\varepsilon\in(0,1)$, and set
--
--   $$s=\Big\lceil \frac{c\log(1/\varepsilon)}{\varepsilon^2}\Big\rceil,\qquad q=\frac1{\sqrt{\log(1/\varepsilon)}} .$$
--
--   For a nonnegative integer $s$ and a real $n\times n$ matrix $A$, the **$\ell_2^2$-sampling probabilities** are $p_i=s\|A_i\|_2^2/\|A\|_F^2$, and $A$ has **bounded row norms** (Definition 3.1) if
--
--   $$\forall i\in[n]:\qquad \frac{s\|A_i\|_2^2}{\|A\|_F^2}\le 1. \tag{1}$$
--
--   Condition (1) says exactly that every $p_i$ is a probability. Algorithm 1 samples row $i$ with probability $p_i$; Algorithm 2 reduces every symmetric matrix to one satisfying (1).
--
--   **Formalization Note** The logarithm is natural and the ceiling is `Nat.ceil`, so $s$ is a natural number ($s\ge1$ when $c>0$, $\varepsilon\in(0,1)$). The predicate takes the integer $s$ as an argument; Definition 3.1 is the case $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$. Condition (1) is stated multiplied out, $s\|A_i\|_2^2\le\|A\|_F^2$, which is equivalent for $A\neq0$ and avoids the undefined quotient at $A=0$. At $A=0$ Lean's convention $x/0=0$ gives $p_i=0$.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 3.1, p.10, eq. (1); Algorithm 1 (Figure 1), p.11

import Definitions.Def_L22EigEst_rowSq

namespace L22EigEst

/-- **The sample-size parameter** `s = ⌈c log(1/ε)/ε²⌉` of Definition 3.1 and Algorithms 1 and 2.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 3.1, p.10, and
Algorithm 1 (Figure 1), p.11.

**Formalization Note.** `log` is the natural logarithm. The ceiling is `Nat.ceil`, so a
non-positive argument gives `0`; for `c > 0` and `ε ∈ (0, 1)` the argument is positive and
`sParam c ε ≥ 1`. -/
noncomputable def sParam (c ε : ℝ) : ℕ :=
  ⌈c * Real.log (1 / ε) / ε ^ 2⌉₊

/-- **The entry-keeping probability** `q = 1/√log(1/ε)` of Algorithm 1 (Figure 1), p.11,
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…).

**Formalization Note.** For `ε ∈ (0, 1/4)`, `log(1/ε) > log 4 > 1`, so `q ∈ (0, 1)`. -/
noncomputable def qParam (ε : ℝ) : ℝ :=
  1 / Real.sqrt (Real.log (1 / ε))

/-- **The ℓ₂²-sampling probabilities** `p_i = s‖A_i‖₂²/‖A‖_F²` of Algorithm 1 (Figure 1), p.11,
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…): "draws of a matrix S ∼ 𝒮
include each row i independently with probability p_i = s∥A_i∥2²/∥A∥F²".

**Formalization Note.** `s` is a natural number (in Algorithm 1 it is `sParam c ε`; Lemmas 4.3,
4.4 and 4.11 take any integer `s` above a threshold). A zero row has `p_i = 0`. At `A = 0` the
source's quotient is undefined and Lean's `x / 0 = 0` gives `p_i = 0`; the statements that use
this value at `A = 0` say so. Under Definition 3.1 (`BoundedRowNorm s A`) every `p_i ≤ 1`. -/
noncomputable def rowProb {n : ℕ} (s : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (s : ℝ) * rowSq A i / frobSq A

/-- **Bounded row-norm property** (Definition 3.1, p.10), Menand, Waingarten, STOC 2027 submission
(manuscript sha256 b1f6adce…): "∀i ∈ [n], s∥A_i∥2²/∥A∥F² ≤ 1, (1) where s = ⌈c log(1/ε)/ε²⌉ for some
constant c."

**Formalization Note.** The integer `s` is an argument (Definition 3.1 is
`BoundedRowNorm (sParam c ε) A`). Condition (1) is stated multiplied out,
`s‖A_i‖₂² ≤ ‖A‖_F²`, which is equivalent for `A ≠ 0` and avoids the undefined quotient `0/0` at
`A = 0` (where the multiplied-out form holds trivially). Symmetry of `A` is a separate hypothesis
of the statements that use this predicate. -/
def BoundedRowNorm {n : ℕ} (s : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, (s : ℝ) * rowSq A i ≤ frobSq A

end L22EigEst


