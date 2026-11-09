-- Prove2me | Definitions.Def_KSPolySign_layout
-- name    : KSPolySign_layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:55.365035+00:00
-- url     : https://prove2.me/theorems/1f0e1907-a8d6-41b7-abbb-cf0d99dfbc14
-- title:
--   Real-RAM input layout of a family of complex matrices
-- statement:
--   For matrices $A_1,\dots,A_m\in\mathbb C^{n\times n}$, the input list of the real RAM is
--   $$[\,m,\ n\,]\ \text{followed by}\ \operatorname{Re}(A_i)_{jl},\ \operatorname{Im}(A_i)_{jl}\quad\text{for } i<m,\ j<n,\ l<n \text{ in this order.}$$
--   The algorithm of Theorem 6.8(b) reads its input in this form.
--
--   **Formalization Note** The machine stores reals, so each complex entry occupies two cells; indices are $0$-based.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Input layout of a matrix family on the real RAM.** The list `[m, n]` followed, for `i < m`, row
`j < n` and column `l < n`, by the pair `re (A_i)_{jl}`, `im (A_i)_{jl}`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68): the input of Algorithm 3 is the family `A_1, …, A_m ∈ ℂ^{n×n}`.

**Formalization Note** The machine holds reals only, so a complex entry is stored as its real and
imaginary parts; the dimensions `m`, `n` are stored as reals in the first two cells. -/
noncomputable def layout (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) : List ℝ :=
  [(m : ℝ), (n : ℝ)] ++
    (List.finRange m).flatMap fun i => (List.finRange n).flatMap fun j =>
      (List.finRange n).flatMap fun l => [(A i j l).re, (A i j l).im]

end KSPolySign


