-- Prove2me | Definitions.Def_AlgoPFR_Supplement_Quad
-- name    : AlgoPFR_Supplement_Quad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:34:39.639604+00:00
-- url     : https://prove2.me/theorems/c8b9d905-cfc0-4252-80ab-5ab1e533105a
-- title:
--   Quadratic polynomials over $\mathbb F_2$, their output encoding, and the correlation $\mathbb E_x[f(x)(-1)^{q(x)}]$
-- statement:
--   1. A **quadratic polynomial** in $n$ variables over $\mathbb F_2$ is
--   $$q(x)=\sum_{i\le j}a_{ij}x_ix_j+\sum_i b_ix_i+c,\qquad a_{ij},b_i,c\in\mathbb F_2,$$
--   that is, any polynomial of degree at most two, with linear and constant terms.
--   2. On the oracle RAM a quadratic is output as the list $[1,c,b_1,\dots,b_n,(a_{ij})_{i\le j}]$, with the $a_{ij}$ in lexicographic order of $(i,j)$; the symbol $\bot$ is output as $[0]$.
--   3. The **correlation** of $f:\mathbb F_2^n\to\mathbb R$ with $q$ is
--   $$\operatorname{corr}(f,q)=\mathbb E_{x}\bigl[f(x)(-1)^{q(x)}\bigr]=2^{-n}\sum_{x\in\mathbb F_2^n}f(x)(-1)^{q(x)}.$$
--
--   These are the output and the quality measure of the quadratic Goldreich–Levin algorithm (Theorem 7.1).
--
--   **Formalization Note** The correlation is signed, with no absolute value, as on the page. Only the coefficients $a_{ij}$ with $i\le j$ enter the value and the encoding.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 7.1, p.47; Lemma 7.7 and Claim 7.6, pp.51

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

namespace AlgoPFR

namespace Supplement

noncomputable section

/-- A **quadratic polynomial over `F₂`** in `n` variables, the output of the quadratic
Goldreich–Levin algorithm of Theorem 7.1, p.47 of Arunachalam, Dutt, Grewal, Gupte, *Marton's
conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…): "a quadratic form q" in
Theorem 7.1, "a quadratic polynomial q" in Theorem 1.3, Lemma 7.7 and the proof of Claim 7.6
("the output is a polynomial of degree at most two", p.51). It is
`q(x) = ∑_{i ≤ j} a_{ij} x_i x_j + ∑_i b_i x_i + c`.

**Formalization Note.** Linear and constant terms are included, as in the paper's proof (the
output of Claim 7.6 carries a constant `c` and a linear phase `⟨ξ, y⟩`). Only the coefficients
`a i j` with `i ≤ j` are used; the others are ignored by `eval` and by `encodeQuad`. -/
structure Quad (n : ℕ) where
  /-- The constant term `c`. -/
  c : ZMod 2
  /-- The linear coefficients `b_i`. -/
  b : Fin n → ZMod 2
  /-- The quadratic coefficients `a_{ij}`, read only for `i ≤ j`. -/
  a : Fin n → Fin n → ZMod 2

/-- The value `q(x) ∈ F₂` of a quadratic polynomial. -/
def Quad.eval {n : ℕ} (q : Quad n) (x : Vec n) : ZMod 2 :=
  (∑ i, ∑ j, if i ≤ j then q.a i j * x i * x j else 0) + (∑ i, q.b i * x i) + q.c

/-- The output encoding of a quadratic polynomial on the oracle RAM: the list
`[1, c, b_1, …, b_n, a_{ij} (i ≤ j, lexicographic in (i, j))]`, every coefficient as `0` or `1`.
The symbol `⊥` is the list `[0]` (`botOutput`). -/
def encodeQuad {n : ℕ} (q : Quad n) : List ℕ :=
  [1, q.c.val] ++ (List.finRange n).map (fun i => (q.b i).val) ++
    (List.finRange n).flatMap fun i =>
      ((List.finRange n).filter fun j => decide (i ≤ j)).map fun j => (q.a i j).val

/-- The output `⊥` of Theorem 7.1, p.47, encoded as `[0]`. -/
def botOutput : List ℕ := [0]

/-- The **correlation** `E_x[f(x) · (−1)^{q(x)}]` of `f : F₂ⁿ → ℝ` with a quadratic phase, Theorem
7.1, p.47: the average over the uniform `x ∈ F₂ⁿ`.

**Formalization Note.** The correlation is signed: the rendered page has no absolute value. -/
def corr {n : ℕ} (f : Vec n → ℝ) (q : Quad n) : ℝ :=
  (∑ x : Vec n, f x * (-1 : ℝ) ^ (q.eval x).val) / (Fintype.card (Vec n) : ℝ)

end

end Supplement

end AlgoPFR


