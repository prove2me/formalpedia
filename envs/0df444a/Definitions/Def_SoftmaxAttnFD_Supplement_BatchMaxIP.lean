-- Prove2me | Definitions.Def_SoftmaxAttnFD_Supplement_BatchMaxIP
-- name    : SoftmaxAttnFD_Supplement_BatchMaxIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:41:21.96613+00:00
-- url     : https://prove2.me/theorems/a1e8ddec-85c3-47b5-a31a-80422a95c987
-- title:
--   Definition 2.2 — the batch maximum-inner-product problem $\mathrm{BatchMaxIP}_d$, its integer input layout and exact output
-- statement:
--   Let $X\in\mathbb Z^{m\times d}$ and $Y\in\mathbb Z^{n\times d}$ be integer matrices with rows $x_i$ and $y_j$ and coordinate magnitudes at most an integer $B\ge1$. The batch problem $\mathrm{BatchMaxIP}_d$ asks for
--
--   $$M_i=\max_{j\in[n]}x_i\cdot y_j,\qquad i\in[m].$$
--
--   Each $M_i$ is an integer in $[-dB^2,dB^2]$.
--
--   This item fixes how an instance and a correct answer look on the base mission's logarithmic-cost RAM:
--
--   1. an integer $z$ is the encoded rational triple with sign $[z<0]$, numerator $|z|$ and denominator $1$;
--   2. the **input** consists of the cells $m,n,d,B$, followed by $X$ and then $Y$ row by row, each entry an integer triple;
--   3. an output memory is **correct**, with output starting at address $a$, if for every $i$ the triple at address $a+3i$ is well formed and its value is some $x_i\cdot y_j$ and at least every $x_i\cdot y_j$, that is, it equals $M_i$ exactly.
--
--   It also names the integer inner product $x_i\cdot y_j=\sum_\ell X_{i\ell}Y_{j\ell}$ and the bound $|X_{i\ell}|\le B$ on every entry. The problem is the comparison point of the paper's attention bounds; Theorem 3.1 reduces it to attention.
--
--   **Formalization Note** No maximizing index is asked for (Definition 2.2 asks only for the values $M_i$); this differs from the base mission's batch-maxima predicate of Proposition 5.1. The magnitude bound $B$ and the dimension $d$ are input cells: the reductions of Theorem 3.1 use $B$, and in §3 the dimension is not fixed, so a fixed program has to read it. The output triple need not be reduced.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definition 2.2, p.10 (PDF p.13)

import Definitions.Def_SoftmaxAttnFD_RatEnc

namespace SoftmaxAttnFD

namespace Supplement

/-- The canonical encoded triple of an integer `z`: sign `z < 0`, numerator `|z|`, denominator `1`.

Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055, sha256
a60f7609…, Definition 2.2, p.10 (inputs are integer matrices), on the published triple `RatEnc`. -/
def intEnc (z : ℤ) : RatEnc := ⟨decide (z < 0), z.natAbs, 1, Nat.one_pos⟩

/-- An integer matrix, entrywise encoded by `intEnc`. -/
def intMat {a c : ℕ} (A : Fin a → Fin c → ℤ) : Fin a → Fin c → RatEnc :=
  fun i l => intEnc (A i l)

/-- Every entry of an integer matrix has absolute value at most `B`. -/
def IntBounded {a c : ℕ} (A : Fin a → Fin c → ℤ) (B : ℕ) : Prop :=
  ∀ i l, |A i l| ≤ (B : ℤ)

/-- The integer inner product `x_i · y_j` of row `i` of `X` and row `j` of `Y`. -/
def idot {m n d : ℕ} (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ) (i : Fin m) (j : Fin n) : ℤ :=
  ∑ l, X i l * Y j l

/-- The input cells of BatchMaxIP_d (arXiv:2611.06055, Definition 2.2, p.10): `m, n, d, B`, then `X`
and `Y` row by row, each entry the triple `intEnc`.

**Formalization Note** The magnitude bound `B` and the dimension `d` are input cells: the instance of
Definition 2.2 carries the integer `B`, the reductions of Theorem 3.1 use it (`ε₀`, `V = dB·Y`), and
in §3 the dimension is not fixed, so a fixed program must read it. -/
def bmipInput {m n d : ℕ} (B : ℕ) (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ) : List ℕ :=
  [m, n, d, B] ++ matCells (intMat X) ++ matCells (intMat Y)

/-- Correct output of BatchMaxIP_d (arXiv:2611.06055, Definition 2.2, p.10: "asks for
`M_i = max_{j∈[n]} x_i · y_j`, `i ∈ [m]`"), with the output starting at address `base`: for every
`i`, the triple at `base + 3i` is well formed and its value is attained by some `x_i · y_j` and is at
least every `x_i · y_j`, i.e. it equals `M_i` exactly.

**Formalization Note** No maximizing index is required (unlike the published `maxGood`). The triple
need not be reduced; only its value is constrained. With `n = 0` the predicate is unsatisfiable for
`m ≥ 1`; every statement using it assumes `n ≥ 1`. -/
def bmipGood {m n d : ℕ} (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ) (base : ℕ)
    (out : ℕ → ℕ) : Prop :=
  ∀ i : Fin m,
    ValidAt out (base + 3 * i.val) ∧
      (∃ j, valAt out (base + 3 * i.val) = (idot X Y i j : ℚ)) ∧
        ∀ j, (idot X Y i j : ℚ) ≤ valAt out (base + 3 * i.val)

end Supplement

end SoftmaxAttnFD


