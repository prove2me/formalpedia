-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_HasStructuredL1Approx
-- name    : EffRobustLearn_Supplement_HasStructuredL1Approx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:16:08.819779+00:00
-- url     : https://prove2.me/theorems/82317800-ae7a-4616-abbe-fada75a01d27
-- title:
--   Structured $L_1$ polynomial approximation (Definition 4.13)
-- statement:
--   For $\alpha\in(0,1)$, a concept class $\mathcal C$ admits **structured polynomial approximators of degree $\ell$ and error $\alpha$** with respect to $D$ if for every $c\in\mathcal C$ there is one real polynomial $q$ of degree at most $\ell$ satisfying both
--   $$
--   \mathbb E_{x\sim D}|q(x)-c(x)|\le\alpha
--   \qquad\text{and}\qquad
--   \mathbb E_{x\sim D}|q(x)^2-1|\le\alpha .
--   $$
--
--   The first condition controls approximation of the concept, the second lets weighted iterative polynomial filtering control $q^2-1$. Theorem 4.14 assumes it with $\alpha=\varepsilon/512$.
--
--   **Formalization Note** The source's sentence says "structured $L_\infty$ polynomial approximators" while its title and Theorem 4.14 say "structured $L_1$"; the notion is the one fixed by the two displayed conditions. Concepts are read as $\pm1$ through `toPM`; expectations are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 4.13, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- Structured `L1` approximation, Definition 4.13 of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.25 (PDF p.26):
`C` admits structured polynomial approximators of degree `ℓ` and error `α` with respect to `D` if every
`c ∈ C` has **one** polynomial `q` of degree at most `ℓ` with both
`E_{x∼D}|q(x) − c(x)| ≤ α` and `E_{x∼D}|q(x)² − 1| ≤ α`.

**Formalization Note.**
* The definition's sentence says "structured L∞ polynomial approximators" while its title and Theorem 4.14 say
  "structured L1"; it is one notion, fixed by these two conditions.
* Concepts are read as `±1` through `toPM`; expectations are lower Lebesgue integrals in `ℝ≥0∞`.
* Definition 4.13 takes `α ∈ (0, 1)`; Theorem 4.14 passes `ε/512`. -/
def HasStructuredL1Approx {d : ℕ} (D : Measure (Fin d → ℝ)) (C : Set ((Fin d → ℝ) → Bool))
    (ℓ : ℕ) (α : ℝ) : Prop :=
  ∀ c ∈ C, ∃ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ ℓ ∧
    ∫⁻ x, ‖MvPolynomial.eval x q - toPM c x‖ₑ ∂D ≤ ENNReal.ofReal α ∧
    ∫⁻ x, ‖MvPolynomial.eval x q ^ 2 - 1‖ₑ ∂D ≤ ENNReal.ofReal α

end Supplement

end EffRobustLearn


