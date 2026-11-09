-- Prove2me | Definitions.Def_KSPolySign_vecLayout
-- name    : KSPolySign_vecLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:10.866066+00:00
-- url     : https://prove2.me/theorems/d2636bb7-6504-488f-bca7-68954fe75532
-- title:
--   Real-RAM input layout of a family of vectors and a tolerance
-- statement:
--   For vectors $b_1,\dots,b_m\in\mathbb R^{d}$ and a tolerance $\eta$, the input list of the real RAM is
--   $$[\,m,\ d,\ \eta\,]\ \text{followed by the coordinates of } b_1, \dots, b_m \text{ in order.}$$
--   The partial-signing routine of Lemma 4.6 reads its input in this form.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.6, p.39 (PDF p.39)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Input layout of a vector family and a tolerance on the real RAM.** The list `[m, d, η]` followed
by the vectors `b_1, …, b_m ∈ ℝ^d` in order, each in coordinate order.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.6, p.39 (PDF p.39): the input is `b_1, …, b_m ∈ ℝ^{d_vec}` and `0 < η < 1`.

**Formalization Note** The tolerance `η` is part of the input, so a single program serves every `η`. -/
noncomputable def vecLayout (m d : ℕ) (b : Fin m → Fin d → ℝ) (η : ℝ) : List ℝ :=
  [(m : ℝ), (d : ℝ), η] ++ (List.finRange m).flatMap fun i => MatMulTimeLP.vecToList (b i)

end KSPolySign


