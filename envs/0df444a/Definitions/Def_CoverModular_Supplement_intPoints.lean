-- Prove2me | Definitions.Def_CoverModular_Supplement_intPoints
-- name    : CoverModular_Supplement_intPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:17:11.675183+00:00
-- url     : https://prove2.me/theorems/77b966a5-d016-5f22-adc5-7a79693c8708
-- title:
--   Integer points $P(b)=\{x\in\mathbb Z^n\mid\sum_ja_{ij}x_j\le b_i\}$
-- statement:
--   For an integer matrix $(a_{ij})$ with $a_{ij}\in\mathbb Z$ ($1\le i\le m$, $1\le j\le n$) and a real vector $b\in\mathbb R^m$, the set of integer points is
--
--   $$
--   P(b)=\Big\{x\in\mathbb Z^n\ \Big|\ \sum_ja_{ij}x_j\le b_i,\ 1\le i\le m\Big\}.
--   $$
--
--   Lemma 5 shows that $P(b)$ does not change when $b$ is rounded down element-wise. This is the step that lets Theorem 2 handle a non-integral right-hand side under integrality constraints.
--
--   **Formalization Note** There is no sign condition on $a$ or on $x$. Each integer row sum is cast to $\mathbb R$ before it is compared with $b_i$.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, Lemma 5, p.43

import Mathlib

namespace CoverModular.Supplement

/-- The set of integer points `P(b) = {x ∈ ℤⁿ | ∑_j a_ij x_j ≤ b_i, 1 ≤ i ≤ m}` of Lemma 5
(DeValve, Pekeč, Wei, SSRN 3844987, Appendix A.3, Lemma 5, p.43), for an integer matrix
`a_ij ∈ ℤ` and a real right-hand side `b ∈ ℝ^m`.

**Formalization Note** No sign condition on `a` or on `x`; the integer row sum is cast to `ℝ`
for the comparison with `b_i`. -/
def intPoints {m n : ℕ} (a : Fin m → Fin n → ℤ) (b : Fin m → ℝ) : Set (Fin n → ℤ) :=
  {x | ∀ i, ((∑ j, a i j * x j : ℤ) : ℝ) ≤ b i}

end CoverModular.Supplement


